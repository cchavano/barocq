open Printf
open Types
open Syntax
open Syntax.Typed
open Monads
open Imp1
open Imp1Typed
open Aliasing_defs
open Aliasing_defs.PathTree
open Aliasing_defs.AbsDom
open PrintCommon

exception UnsupportedFeature of string

let unsupported =
  UnsupportedFeature
    "arrays and function pointers are not handled by the alias analysis yet "

let debug_info (b : bool) (s : string) : unit = if b then eprintf "%s" s else ()

let ( let* ) = AbsDom.dbind

(** [is_valid_atom d a] checks wether the atom [a] is valid in [d]. If [a]
    contains variables x1, ..., xn, it checks wether paths x1, ..., xn are valid
    in [d]. *)
let rec is_valid_atom (d : t) (a : atom) : bool =
  match a with
  | AVar (x, _) -> is_valid_path d x []
  | AUnaryOp (op, a', _) -> is_valid_atom d a'
  | ABinaryOp (op, a1, a2, _) -> is_valid_atom d a1 && is_valid_atom d a2
  | _ -> true

let paths_to_string (paths : path_tree IdentMap.t) : string =
  list_to_string_bracket
    (fun (x, t) -> sprintf "%s.%s" (ident_to_string x) (PathTree.to_string t))
    (List.of_seq (IdentMap.to_seq paths))

let is_prim (c : ctyp) : bool =
  match c with
  | CBool | CInt32 | CInt64 -> true
  | CFun (_, _) | CArray _ -> raise unsupported
  | _ -> false

(** [subst_atom ce a] substitutes each var contained in [a] by the var to which
    it is binded in [ce]. It is used to replace formal parameters by their
    argument during function calls in the inter-procedural analysis. *)
let subst_atom (ce : cenv) (a : atom) : atom =
  match a with
  | AVar (x, _) -> begin
      match IdentMap.find_opt x ce with
      | Some a' -> a'
      | None -> a
    end
  | _ -> a

(** [subst_in_comp ce c] substitutes each var contained in [c] by the var to
    which it is binded in [ce]. *)
let subst_in_comp (ce : cenv) (c : comp) : comp =
  match c with
  | CpAtom (a, ty) -> CpAtom (subst_atom ce a, ty)
  | CpStructProj (a, f, ty) -> CpStructProj (subst_atom ce a, f, ty)
  | CpStructUpdate (a, f, v, ty) -> CpStructUpdate (subst_atom ce a, f, v, ty)
  | CpCall (a, args, ty) ->
      let a' = subst_atom ce a in
      let args' = List.map (subst_atom ce) args in
      CpCall (a', args', ty)
  | _ -> raise unsupported

(** [substitute_in_statement ce s] substitutes each var contained in [s] by the
    var to which it is binded in [ce]. *)
let rec subst_in_statement (ce : cenv) (s : statement) : statement * cenv =
  match s with
  | StSet (x, c) ->
      let c' = subst_in_comp ce c in
      let ce' = IdentMap.remove x ce in
      (StSet (x, c'), ce')
  | StIfThenElse (a, s1, s2) ->
      let a' = subst_atom ce a in
      let s1', ce1 = subst_in_statement ce s1 in
      let s2', ce2 = subst_in_statement ce s2 in
      (* ce1 and ce2 should be the same, because ifthenelse statements result
         from the compilation of let x = if _ then _ else _, so every branches 
         should contain the "set x" statement. *)
      let ce' =
        assert (ce1 = ce2);
        ce1
      in
      (StIfThenElse (a', s1', s2'), ce')
  | StSequence (s1, s2) ->
      let s1', ce1 = subst_in_statement ce s1 in
      let s2', ce2 = subst_in_statement ce1 s2 in
      (StSequence (s1', s2'), ce2)
  | StReturn a -> (StReturn (subst_atom ce a), ce)

let rec paths_to_loc_rec (rev : rev_asbenv) (rm : rev_absmem) (curr : absloc)
    (p : path) (paths : path_tree IdentMap.t) : path_tree IdentMap.t =
  let paths' =
    match IdentMap.find_opt curr rev with
    | Some vars ->
        IdentSet.fold
          (fun v accS ->
            IdentMap.update
              v
              (fun ptv ->
                match ptv with
                | Some ptv -> Some (PathTree.add ptv p)
                | None -> Some (PathTree.create p))
              accS)
          vars
          paths
    | None -> paths
  in
  match IdentMap.find_opt curr rm with
  | Some adj ->
      List.fold_left
        (fun accL (f, lf) ->
          IdentSet.fold
            (fun n accS -> paths_to_loc_rec rev rm n (f :: p) accS)
            lf
            accL)
        paths'
        adj
  | None -> paths'

(** [paths_to_loc st loc] computes all the paths leading to the location [loc]
    in [st]. *)
let paths_to_loc (st : absstate) (loc : absloc) : path_tree IdentMap.t =
  paths_to_loc_rec st.st_rev_env st.st_rev_mem loc [] IdentMap.empty

(** [paths_to_loc_suffix st loc suffix] computes all the paths leading to the
    location [loc] in [st] nd suffixes them with [suffix]. *)
let paths_to_loc_suffix (st : absstate) (loc : absloc) (suffix : path) :
    path_tree IdentMap.t =
  paths_to_loc_rec st.st_rev_env st.st_rev_mem loc suffix IdentMap.empty

(** [invalid_paths_with_prefix inv x p] returns the invalid paths with prefix
    x.p in [inv]. *)
let invalid_paths_with_prefix (inv : path_map) (x : ident) (p : path) :
    path_tree option =
  match IdentMap.find_opt x inv with
  | Some t -> PathTree.prefixed_by t p
  | None -> None

(** [invalid_paths_of_atom inv a] returns the invalid paths of all variables
    contains in [a]. *)
let rec invalid_paths_of_atom (inv : path_map) (a : atom) : path_tree option =
  match a with
  | AVar (v, _) -> invalid_paths_with_prefix inv v []
  | AUnaryOp (op, a', _) -> invalid_paths_of_atom inv a'
  | ABinaryOp (op, a1, a2, _) -> begin
      let iv1 = invalid_paths_of_atom inv a1 in
      let iv2 = invalid_paths_of_atom inv a2 in
      match (iv1, iv2) with
      | Some t1, Some t2 -> Some (PathTree.union t1 t2)
      | Some t1, None -> Some t1
      | None, Some t2 -> Some t2
      | _, _ -> None
    end
  | _ -> None

(** [exec_set_atom x a st] computes the transfer function for the statement
    [set x = a] on [st]. *)
let exec_set_atom (x : ident) (a : atom) (st : absstate) : absstate =
  let a_inv = invalid_paths_of_atom st.st_inv a in
  let st' =
    match a with
    | AVar (v, ty) ->
        if is_prim ty then st
        else
          let lv = IdentMap.find v st.st_env in
          (* x inherits the invalid paths from v. *)
          env_add st x lv
    | _ -> st
  in
  match a_inv with
  | Some t -> inv_add st' x t
  | None -> st'

(** [exec_set_struct_proj x a f ty st] computes the transfer function for the
    statement [set x = a.f] on [st]. [ty] is the type of the field [f] of the
    struct [a]. *)
let exec_set_struct_proj (x : ident) (a : atom) (f : ident) (ty : ctyp)
    (st : absstate) : absstate =
  match a with
  | AVar (y, _) ->
      let yf_inv = invalid_paths_with_prefix st.st_inv y [f] in
      let st' =
        if is_prim ty then st
        else
          let ly = IdentMap.find y st.st_env in
          let ly_f =
            IdentSet.fold
              (fun l acc -> IdentSet.union acc (AbsDom.mem_get st.st_mem l f))
              ly
              set_empty
          in
          env_add st x ly_f
      in
      begin
        match yf_inv with
        | Some t ->
            (* x inherits the invalid paths from y.f. *)
            inv_add st' x t
        | None -> st'
      end
  | _ -> assert false

(** [exec_set_struct_update ts x a f v st] computes the transfer function for
    the statement [set x = x.f <- y] on [st]. *)
let exec_set_struct_update (ts : types) (x : ident) (a : atom) (f : ident)
    (v : atom) (st : absstate) : absstate =
  match a with
  | AVar (y, CStruct sy) ->
      let ly = IdentMap.find y st.st_env in
      (* All paths leading to all locations in ly + suffix f are now invalid. *)
      let inv' =
        IdentSet.fold
          (fun l acc ->
            let l_inv = paths_to_loc_suffix st l [f] in
            inv_union l_inv acc)
          ly
          st.st_inv
      in
      (* If variable shadowing occurs, and x already had invalid paths, then removes them. *)
      let inv' = IdentMap.remove x inv' in
      (* x inherits the invalid paths from v *)
      let v_inv = invalid_paths_of_atom st.st_inv a in
      (* x inherits the invalid paths from y
         - if y was already completely invalid, x.f is valid (modulo invalid paths from v) but all x.f', f' <> f are invalid
         - otherwise, if some y.f', f' <> f were invalid, then x.f' becomes also invalid. *)
      let y_inv =
        match invalid_paths_with_prefix st.st_inv y [] with
        | Some (Leaf | Node []) -> begin
            match types_get ts sy with
            | Errors.OK fields ->
                let ln =
                  List.fold_left
                    (fun acc (fi, _) ->
                      if fi <> f then (fi, Leaf) :: acc else acc)
                    []
                    fields
                in
                Some (Node ln)
            | _ -> assert false
          end
        | Some (Node (_ :: _ as ln)) ->
            let ln' = List.remove_assoc f ln in
            if ln' = [] then None else Some (Node ln')
        | None -> None
      in
      let x_inv =
        match (v_inv, y_inv) with
        | Some t1, Some t2 -> Some (PathTree.union t1 t2)
        | Some t1, None -> Some t1
        | None, Some t2 -> Some t2
        | None, None -> None
      in
      let st' =
        match v with
        | AVar (v, ty) ->
            if is_prim ty then st
            else
              let lv = IdentMap.find v st.st_env in
              IdentSet.fold (fun l acc -> mem_add acc (l, f) lv) ly st
        | _ -> st
      in
      let st' = env_add st' x ly in
      let inv' =
        match x_inv with
        | Some t -> IdentMap.add x t inv'
        | None -> inv'
      in
      { st' with st_inv = inv' }
  | _ -> assert false

(** [build_cenv params args] builds the call environment which binds each
    parameter to its corresponding argument. *)
let rec build_cenv (params : (ident * ctyp) list) (args : atom list) : cenv =
  match (params, args) with
  | [], [] -> IdentMap.empty
  | (pid, ptyp) :: params', a :: args' ->
      IdentMap.add pid a (build_cenv params' args')
  | _, _ -> assert false

(** [is_arg v args] checks wether the variable [v] is contained in the argument
    list [args]. *)
let is_arg (v : ident) (args : atom list) : bool =
  List.exists
    (fun a ->
      match a with
      | Syntax.Typed.AVar (x, _) ->
          if Common.ident_eq_dec x v then true else false
      | _ -> false)
    args

(** [pointsto_unique st x] checks wether the variable [x] points to only one
    abstract location in [st]. *)
let pointsto_unique (st : absstate) (x : ident) : bool =
  match IdentMap.find_opt x st.st_env with
  | Some locs -> IdentSet.cardinal locs = 1
  | None -> true

(** [args_points_unique st args] checks wether all function arguments points to
    only abstract location [st]. *)
let args_pointsto_unique (st : absstate) (args : atom list) : bool =
  let nr =
    List.exists
      (fun (a : atom) ->
        match a with
        | AVar (x, _) -> not (pointsto_unique st x)
        | _ -> false)
      args
  in
  not nr

let rec is_tree_loc_aux (m : absmem) (curr : absloc) (visited : IdentSet.t) :
    bool * IdentSet.t =
  if IdentSet.mem curr visited then (false, visited)
  else
    let adjacents =
      IdentPairMap.fold
        (fun (l, f) locs acc ->
          if Common.ident_eq_dec l curr then
            List.append (IdentSet.elements locs) acc
          else acc)
        m
        []
    in
    let b, visited' = is_tree_locs_aux m (true, visited) adjacents in
    let visited' = IdentSet.add curr visited' in
    if b then (true, visited') else (false, visited')

and is_tree_locs_aux (m : absmem) ((b, vis) : bool * IdentSet.t)
    (locs : ident list) : bool * IdentSet.t =
  match locs with
  | [] -> (b, vis)
  | l :: locs' ->
      let b', vis' = is_tree_loc_aux m l vis in
      let visu = IdentSet.union vis vis' in
      if b' then is_tree_locs_aux m (b', visu) locs' else (false, visu)

(** [is_tree_loc m curr visited] checks wether the memory layout of [m] is a
    tree starting from [curr] and given the already visited nodes [visited]. *)
let is_tree_loc (m : absmem) (curr : absloc) (visited : IdentSet.t) : bool =
  fst (is_tree_loc_aux m curr set_empty)

(** [is_tree_locs m locs] checks wether the memory layout of [m] is a
    multi-rooted tree starting from the locations [locs]. *)
let is_tree_locs (m : absmem) (locs : ident list) : bool =
  fst (is_tree_locs_aux m (true, set_empty) locs)

(** [is_tree_var st x] checks wether the memory layout in [st] is a tree
    starting from the variable [x]. *)
let is_tree_var (st : absstate) (x : ident) : bool =
  match IdentMap.find_opt x st.st_env with
  | Some locs -> is_tree_locs st.st_mem (IdentSet.elements locs)
  | None -> false

(** [wf_args st args] checks that all arguments [args] are well-formed at
    function call, i.e. all args points to trees and there is no inter-arg
    aliasing. *)
let wf_args (st : absstate) (args : atom list) : bool =
  let all_roots args =
    List.fold_left
      (fun acc (a : atom) ->
        match a with
        | AVar (x, ty) -> begin
            match IdentMap.find_opt x st.st_env with
            | Some locs -> List.append (IdentSet.elements locs) acc
            | None -> acc
          end
        | _ -> acc)
      []
      args
  in
  is_tree_locs st.st_mem (all_roots args)

(** [wf_return_val st] checks that the return value in [st] is well-formed, i.e.
    it has a tree structure. *)
let wf_return_val (st : absstate) : bool =
  is_tree_locs st.st_mem (IdentSet.elements st.st_res)

(** [vars_aliased_to_loc rev loc] returns the variable set that may point to
    [loc]. If no variable points to [loc], it returns an empty set. *)
let vars_aliased_to_loc (rev : rev_asbenv) (loc : absloc) : var_set =
  match IdentMap.find_opt loc rev with
  | Some vars -> vars
  | None -> set_empty

let rec aliased_paths_rec (m : absmem) (rev : rev_asbenv) (rm : rev_absmem)
    (loc : absloc) (p : path) (paths : path_map) : path_map =
  match p with
  | [] -> raise (Invalid_argument "aliased_path_rec")
  | [f] ->
      let vars = vars_aliased_to_loc rev loc in
      IdentSet.fold
        (fun v acc ->
          IdentMap.update
            v
            (fun t ->
              match t with
              | Some t -> Some (PathTree.add t p)
              | None -> Some (PathTree.create p))
            acc)
        vars
        paths
  | f :: p' ->
      let vars = vars_aliased_to_loc rev loc in
      let paths' =
        IdentSet.fold
          (fun v acc ->
            IdentMap.update
              v
              (fun t ->
                match t with
                | Some t -> Some (PathTree.add t p)
                | None -> Some (PathTree.create p))
              acc)
          vars
          paths
      in
      let locs = mem_get m loc f in
      IdentSet.fold
        (fun l acc -> aliased_paths_rec m rev rm l p' acc)
        locs
        paths'

(** [aliased_path st x p] returns the paths which are in alias with [x.p] in
    [st]. *)
let aliased_paths (st : absstate) (x : ident) (p : path) : path_map =
  match IdentMap.find_opt x st.st_env with
  | Some locs ->
      IdentSet.fold
        (fun l acc ->
          aliased_paths_rec st.st_mem st.st_rev_env st.st_rev_mem l p acc)
        locs
        IdentMap.empty
  | None -> IdentMap.empty

(** [aliased_paths_of_ptree st x t] returns a path tree which contain all paths
    aliased to those contained in [t] prefixed by the variable [x]. *)
let aliased_paths_of_ptree (st : absstate) (x : ident) (t : path_tree) :
    path_map =
  let paths = PathTree.flatten t in
  List.fold_left
    (fun acc p -> inv_union acc (aliased_paths st x p))
    IdentMap.empty
    paths

(** [aliased_paths_of_pmap st pm] returns a path map which, for each variable
    binding x -> t in [pm], contain all paths aliased to those belonging to [t]
    prefixed by the variable [x] *)
let aliased_paths_of_pmap (st : absstate) (pm : path_map) : path_map =
  IdentMap.fold
    (fun k t acc -> inv_union (aliased_paths_of_ptree st k t) acc)
    pm
    IdentMap.empty

(** [create_fresh_arg a vmap nctr] creates a fresh argument from atom [a] with
    the variable mapping [vmap] and the fresh counter [nctr]. Every variable x
    in [a] is associated with a variable argN, wether the binding x -> argN
    already exists in vmap, or argN is a fresh identifier generated from [nctr].
*)
let rec create_fresh_arg (a : atom) (vmap : ident IdentMap.t) (nctr : int ref) :
    atom * ident IdentMap.t =
  match a with
  | AVar (x, ty) -> begin
      match IdentMap.find_opt x vmap with
      | Some x' -> (AVar (x', ty), vmap)
      | None ->
          let x' = ident_of_string (sprintf "arg%d" !nctr) in
          incr nctr;
          (AVar (x', ty), IdentMap.add x x' vmap)
    end
  | AUnaryOp (op, a1, ty) ->
      let a1', vmap' = create_fresh_arg a1 vmap nctr in
      (AUnaryOp (op, a1', ty), vmap')
  | ABinaryOp (op, a1, a2, ty) ->
      let a1', vmap1 = create_fresh_arg a1 vmap nctr in
      let a2', vmap2 = create_fresh_arg a2 vmap1 nctr in
      (ABinaryOp (op, a1', a2', ty), vmap2)
  | _ -> (a, vmap)

(** [create_fresh_arg_list args nctr] creates a list of fresh arguments from the
    argument list [args] and the fresh counter [nctr]. It also returns the
    binding from old variable names to the new ones and its reverse version. *)
let create_fresh_arg_list (args : atom list) (nctr : int ref) :
    atom list * ident IdentMap.t * ident IdentMap.t =
  let rec aux args vmap =
    match args with
    | [] -> ([], vmap)
    | a :: args' ->
        let a', vmap = create_fresh_arg a vmap nctr in
        let fargs, vmap = aux args' vmap in
        (a' :: fargs, vmap)
  in
  let args', vmap = aux args IdentMap.empty in
  let rvmap =
    IdentMap.fold (fun k v acc -> IdentMap.add v k acc) vmap IdentMap.empty
  in
  (args', vmap, rvmap)

(** [subst_var_names st vmap] substitutes all variable names in [st] given the
    binding [vmap]. It does affect the environment, its reverse version and the
    invalid paths environment. *)
let subst_var_names (st : absstate) (vmap : ident IdentMap.t) : absstate =
  let get_new_name x =
    match IdentMap.find_opt x vmap with
    | Some x' -> x'
    | None -> x
  in
  let ev =
    IdentMap.fold
      (fun k v acc ->
        let k' = get_new_name k in
        IdentMap.add k' v acc)
      st.st_env
      IdentMap.empty
  in
  let rev = env_reverse ev in
  let iv =
    IdentMap.fold
      (fun k v acc ->
        let k' = get_new_name k in
        IdentMap.add k' v acc)
      st.st_inv
      IdentMap.empty
  in
  { st with st_env = ev; st_rev_env = rev; st_inv = iv }

(** [exec_set_call x a args ty fe st nctr] computes the transfer function for
    the statement [set x = a (args)] on [st]. [fe] is the function descriptor
    environment. When a function f is called, its transfer function is retrived
    from [fe]. [ty] is the type of the return value. [nctr] is the fresh counter
    used to avoid shadowing of function arguments. *)
let exec_set_call (show_debug : bool) (x : ident) (a : atom) (args : atom list)
    (ty : ctyp) (fe : fenv) (st : absstate) (nctr : int ref) : absdom =
  match a with
  | AVar (y, _) ->
      let fdescr =
        match IdentMap.find_opt y fe with
        | Some descr -> descr
        | None -> raise unsupported
      in
      (* We want to avoid variable shadowing on function arguments
         1 - We create fresh names for all variables contained in the function arguments,
             and store the correspondence map and its reverse version.
         2 - For each association v -> v' in the correspondence map,
             modifies v into v' in the abtract state (in st_env, st_rev_env, st_inv)
         3 - When the function returns, we use the reverse map to update the abstract state correctly. *)
      let fargs, vmap, rvmap = create_fresh_arg_list args nctr in
      debug_info show_debug
      @@ sprintf
           "Arguments binding: %s\n"
           (list_to_string_bracket
              (fun (k, v) ->
                sprintf "%s -> %s" (ident_to_string k) (ident_to_string v))
              (List.of_seq (IdentMap.to_seq vmap)));
      let ev_call = IdentMap.filter (fun k _ -> is_arg k args) st.st_env in
      let rev_call = env_reverse ev_call in
      let inv_call = IdentMap.filter (fun k _ -> is_arg k args) st.st_inv in
      let stcall =
        let stproj =
          make_state
            ev_call
            st.st_mem
            rev_call
            st.st_rev_mem
            set_empty
            inv_call
            None
        in
        subst_var_names stproj vmap
      in
      let ce = build_cenv fdescr.params fargs in
      if args_pointsto_unique stcall fargs && wf_args stcall fargs then
        let dret = fdescr.aliasing ce nctr (AbsState stcall) in
        let d' =
          let* stret = dret in
          (* When a function returns, 
             1) st_env is the env before the call + the new binding for x to the returned locations (i.e. to st_res)
             2) st_mem is the memory returned by the call as is
             3) st_inv is the union between the invalid paths before the call
                + invalid paths after the call filter on the function args
                + the new binding for x which inherhits the invalid paths of the returned value (i.e. it is binded to st_inv_res if <> None)
                + invalid paths for all the aliases on arguments (in the initial memory) if arguments have invalid paths
             5) st_res is unchanged
             4) st_inv_res is unchanged *)
          let st' = if is_prim ty then st else env_add st x stret.st_res in
          let m_ret = stret.st_mem in
          let rm_ret = stret.st_rev_mem in
          let inv_ret =
            let iv =
              (* stret.st_inv contains the bindings with the fresh variable names created for the arguments before the call. *)
              let iv =
                IdentMap.filter (fun k _ -> is_arg k fargs) stret.st_inv
              in
              (* After filtering the invalid paths for the arguments with their fresh names, replaces the generated names by the real names. *)
              let get_old_name x =
                match IdentMap.find_opt x rvmap with
                | Some x' -> x'
                | None -> x
              in
              IdentMap.fold
                (fun k v acc ->
                  let k' = get_old_name k in
                  IdentMap.add k' v acc)
                iv
                IdentMap.empty
            in
            let iv_args_alias = aliased_paths_of_pmap st iv in
            let iv =
              match stret.st_inv_res with
              | Some t -> IdentMap.add x t iv
              | None -> iv
            in
            inv_union (inv_union st.st_inv iv) iv_args_alias
          in
          let inv_res_ret = st.st_inv_res in
          AbsState
            {
              st' with
              st_mem = m_ret;
              st_rev_mem = rm_ret;
              st_inv = inv_ret;
              st_inv_res = inv_res_ret;
            }
        in
        d'
      else Top
  | _ -> assert false

(** [exec_return a st] computes the transfer function for the statement [ret a]
    on [st]. *)
let exec_return (a : atom) (st : absstate) : absstate =
  let a_inv = invalid_paths_of_atom st.st_inv a in
  let st' =
    match a with
    | AVar (v, ty) ->
        if is_prim ty then st
        else
          let res = IdentSet.union st.st_res (IdentMap.find v st.st_env) in
          { st with st_res = res }
    | _ -> st
  in
  let inv_res =
    match (a_inv, st.st_inv_res) with
    | Some ta, Some ti -> Some (PathTree.union ta ti)
    | Some ta, None -> Some ta
    | None, Some ti -> Some ti
    | _, _ -> None
  in
  { st' with st_inv_res = inv_res }

(** [absexec ts fe ce d s nctr] computes the transfer function for the statement
    [s] on [d]. [fe] is the function descriptor environement. [ts] are the
    struct types definitions. [ce] is the calling environment, used if the
    function is analyzed by a call. [nctr] is the fresh counter used to generate
    new argument names. *)
let rec absexec (show_debug : bool) (ts : types) (fe : fenv) (ce : cenv)
    (d : absdom) (s : Imp1Typed.statement) (nctr : int ref) :
    Imp1.Aliasing_AST.statement * absdom =
  let s', _ = subst_in_statement ce s in
  match s' with
  | StSet (x, c) ->
      let d_in = d in
      begin
        match d_in with
        | AbsState st ->
            debug_info show_debug
            @@ sprintf "INV_IN: %s\n" (paths_to_string st.st_inv)
        | Top -> debug_info show_debug "INV_IN: Top\n"
      end;
      let d' =
        let* st = d in
        let c' = subst_in_comp ce c in
        match c' with
        | CpAtom (a, _) -> AbsState (exec_set_atom x a st)
        | CpStructProj (a, f, ty) -> AbsState (exec_set_struct_proj x a f ty st)
        | CpStructUpdate (a, f, v, _) ->
            AbsState (exec_set_struct_update ts x a f v st)
        | CpCall (a, args, ty) ->
            debug_info show_debug
            @@ sprintf
                 "Entering function call \"%s\" ==========\n"
                 (PrintSyntax.PrintTyped.comp_to_string c);
            let r = exec_set_call show_debug x a args ty fe st nctr in
            debug_info show_debug
            @@ sprintf
                 "Exiting function call \"%s\" ===========\n"
                 (PrintSyntax.PrintTyped.comp_to_string c);
            r
        | _ -> raise unsupported
      in
      let s', d' = (Imp1.Aliasing_AST.StSet (x, c, d_in, d'), d') in
      debug_info show_debug
      @@ sprintf "%s\n" (PrintImp1.PrintTyped.statement_to_string_pref "" s);
      begin
        match d' with
        | AbsState st' ->
            debug_info show_debug
            @@ sprintf "INV_OUT: %s\n\n" (paths_to_string st'.st_inv)
        | Top -> debug_info show_debug "INV_OUT: Top\n\n"
      end;
      (s', d')
  | StIfThenElse (a, s1, s2) ->
      let s1', d1 = absexec show_debug ts fe ce d s1 nctr in
      let s2', d2 = absexec show_debug ts fe ce d s2 nctr in
      let d' = AbsDom.union d1 d2 in
      (Imp1.Aliasing_AST.StIfThenElse (a, s1', s2'), d')
  | StSequence (s1, s2) ->
      let s1', d1 = absexec show_debug ts fe ce d s1 nctr in
      let s2', d2 = absexec show_debug ts fe ce d1 s2 nctr in
      (Imp1.Aliasing_AST.StSequence (s1', s2'), d2)
  | StReturn a ->
      begin
        match d with
        | AbsState st ->
            debug_info show_debug
            @@ sprintf "INV_IN: %s\n" (paths_to_string st.st_inv)
        | Top -> debug_info show_debug "INV_IN: Top\n"
      end;
      let d' =
        let* st = d in
        let st' = exec_return a st in
        if is_tree_locs st'.st_mem (IdentSet.elements st.st_res) then
          AbsState (exec_return a st)
        else Top
      in
      let s', d' = (Imp1.Aliasing_AST.StReturn (a, d, d'), d') in
      debug_info show_debug
      @@ sprintf "%s\n" (PrintImp1.PrintTyped.statement_to_string_pref "" s);
      begin
        match d' with
        | AbsState st' ->
            debug_info show_debug
            @@ sprintf "INV_OUT: %s\n" (paths_to_string st'.st_inv);
            begin
              match st'.st_inv_res with
              | Some t ->
                  debug_info show_debug
                  @@ sprintf
                       "INV_RES: %s.%s\n"
                       (PrintSyntax.PrintTyped.atom_to_string a)
                       (PathTree.to_string t)
              | None -> debug_info show_debug "INV_RES: None\n"
            end
        | Top -> debug_info show_debug "INV_OUT: Top\n"
      end;
      (s', d')

(** [gen_fun_descr ts fe f] generates the function descriptor for [f]. *)
let gen_fun_descr (show_debug : bool) (ts : types) (fe : fenv)
    (f : coq_function) : fun_descr =
  {
    params = f.fn_params;
    aliasing =
      (fun ce nctr st ->
        let _, d' = absexec show_debug ts fe ce st f.fn_body nctr in
        d');
  }

(** [get_fun_descr p fname] returns the function descriptions of [fname] if a
    function is defined with this name in the prohram [p]. *)
let get_fun_descr (show_debug : bool) (p : program) (fname : string) :
    fun_descr option =
  let fid = ident_of_string fname in
  let rec aux fe defs =
    match defs with
    | [] -> None
    | DefFun (x, f) :: defs' ->
        let fdescr = gen_fun_descr show_debug p.prog_types fe f in
        if Common.ident_eq_dec x fid then Some fdescr
        else aux (IdentMap.add x fdescr fe) defs'
    | _ :: defs' -> aux fe defs'
  in
  aux IdentMap.empty p.prog_defs

(** [gen_valid_call_state ts params] generates a valid call state w.r.t. the
    function parameters [params]. *)
let gen_valid_call_state (ts : types) (params : (ident * ctyp) list) : absstate
    =
  let gen_field_loc_id lid fname =
    ident_of_string
      (sprintf "%s_%s" (ident_to_string lid) (ident_to_string fname))
  in
  let gen_param_loc_id pid =
    ident_of_string (sprintf "l%s" (ident_to_string pid))
  in
  let rec gen_struct_mem_layout lid sid =
    match types_get ts sid with
    | Errors.OK fields ->
        List.fold_left
          (fun acc (fname, ftyp) ->
            if is_prim ftyp then acc
            else
              match ftyp with
              | CStruct sid' ->
                  let lid' = gen_field_loc_id lid fname in
                  let mem = gen_struct_mem_layout lid' sid' in
                  let mem' =
                    IdentPairMap.add (lid, fname) (IdentSet.singleton lid') mem
                  in
                  mem_union mem' acc
              | _ -> raise unsupported)
          mem_empty
          fields
    | Errors.Error _ -> mem_empty
  in
  let ev =
    List.fold_left
      (fun acc (pid, ptyp) ->
        match ptyp with
        | CStruct _ ->
            IdentMap.add pid (IdentSet.singleton (gen_param_loc_id pid)) acc
        | _ -> if is_prim ptyp then acc else raise unsupported)
      env_empty
      params
  in
  let m =
    List.fold_left
      (fun acc (pid, ptyp) ->
        match ptyp with
        | CStruct sid ->
            mem_union (gen_struct_mem_layout (gen_param_loc_id pid) sid) acc
        | _ -> if is_prim ptyp then acc else raise unsupported)
      mem_empty
      params
  in
  make_state2 ev m set_empty

(** [gen_aliasing_function ts fe f] generates the AST corresponding to the
    function [f] with the aliasing information. *)
let gen_aliasing_function (show_debug : bool) (ts : types) (fe : fenv)
    (f : Imp1Typed.coq_function) : Imp1.Aliasing_AST.coq_function option =
  let stcall = gen_valid_call_state ts f.fn_params in
  let args = List.map (fun (v, ty) -> Syntax.Typed.AVar (v, ty)) f.fn_params in
  assert (args_pointsto_unique stcall args);
  assert (wf_args stcall args);
  let body', d' =
    absexec show_debug ts fe IdentMap.empty (AbsState stcall) f.fn_body (ref 0)
  in
  match d' with
  | AbsState st' ->
      if wf_args st' args then
        Some
          { fn_return = f.fn_return; fn_params = f.fn_params; fn_body = body' }
      else None
  | Top -> None

(** [gen_aliasing_globdef ts fe def] generates the aliasing AST for the global
    definition [def]. It also returns the new function descriptor environment if
    the global def is a function. *)
let gen_aliasing_globdef (ts : types) (fe : fenv) (def : Imp1Typed.globdef)
    (show_debug : bool) : (Imp1.Aliasing_AST.globdef * fenv) option =
  match def with
  | DefFun (x, f) ->
      let fdescr = gen_fun_descr show_debug ts fe f in
      debug_info show_debug
      @@ sprintf "Analysing function %s...\n" (ident_to_string x);
      let r =
        match gen_aliasing_function show_debug ts fe f with
        | Some f' -> Some (DefFun (x, f'), IdentMap.add x fdescr fe)
        | None -> None
      in
      debug_info show_debug
      @@ sprintf "Analysis of function %s finished.\n\n" (ident_to_string x);
      r
  | DefConst (x, l, ty) -> Some (DefConst (x, l, ty), fe)

(** [gen_aliasing_program prog] generates the aliasing AST for the Imp1 program
    [prog]. *)
let gen_aliasing_program (show_debug : bool) (prog : Imp1Typed.program) :
    Imp1.Aliasing_AST.program MonError.coq_M =
  let rec aux fe defs =
    match defs with
    | [] -> Some []
    | d :: defs' -> begin
        match gen_aliasing_globdef prog.prog_types fe d show_debug with
        | Some (d', fe') -> begin
            match aux fe' defs' with
            | Some r -> Some (d' :: r)
            | None -> None
          end
        | None -> None
      end
  in
  match aux IdentMap.empty prog.prog_defs with
  | Some defs -> Errors.OK { prog_types = prog.prog_types; prog_defs = defs }
  | None -> Errors.Error []

module DotExport = struct
  let ident_to_dotstring (id : ident) = sprintf "\"%s\"" (ident_to_string id)

  let print_env (out : out_channel) (ev : absenv) : unit =
    let lev = List.of_seq (IdentMap.to_seq ev) in
    print_list
      out
      ""
      ""
      ""
      (fun x ->
        sprintf
          "%s%s [shape=rect; color=blue; margin=0.1];\n"
          indent
          (ident_to_dotstring x))
      (List.map fst lev);
    print_list
      out
      ""
      ""
      ""
      (fun (k, lp) ->
        let lp' = IdentSet.elements lp in
        sprintf
          "%s%s -> %s;\n"
          indent
          (ident_to_dotstring k)
          (list_to_string "{" "}" " " ident_to_dotstring lp'))
      lev

  let print_mem (out : out_channel) (m : absmem) : unit =
    let lm = List.of_seq (IdentPairMap.to_seq m) in
    print_list
      out
      ""
      ""
      ""
      (fun ((l, f), lp) ->
        let lp' = IdentSet.elements lp in
        sprintf
          "%s%s -> %s [label=\"%s\"];\n"
          indent
          (ident_to_dotstring l)
          (list_to_string "{" "}" " " ident_to_dotstring lp')
          (ident_to_string f))
      lm

  let print_rev_env (out : out_channel) (rev : rev_asbenv) : unit =
    let lrev = List.of_seq (IdentMap.to_seq rev) in
    let vars =
      IdentSet.elements
        (List.fold_left
           (fun acc s -> IdentSet.union acc s)
           IdentSet.empty
           (snd (List.split lrev)))
    in
    print_list
      out
      ""
      ""
      ""
      (fun x ->
        sprintf
          "%s%s [shape=rect; color=blue; margin=0.1];\n"
          indent
          (ident_to_dotstring x))
      vars;
    print_list
      out
      ""
      ""
      ""
      (fun (l, vl) ->
        let vl' = IdentSet.elements vl in
        sprintf
          "%s%s -> %s;\n"
          indent
          (ident_to_dotstring l)
          (list_to_string "{" "}" " " ident_to_dotstring vl'))
      lrev

  let print_rev_mem (out : out_channel) (rm : rev_absmem) : unit =
    let lrm = List.of_seq (IdentMap.to_seq rm) in
    let print_one ((l, vl) : absloc * (ident * var_set) list) : unit =
      print_list
        out
        ""
        ""
        ""
        (fun (f, vs) ->
          sprintf
            "%s%s -> %s [label=\"%s\"];\n"
            indent
            (ident_to_dotstring l)
            (list_to_string
               "{"
               "}"
               " "
               ident_to_dotstring
               (IdentSet.elements vs))
            (ident_to_string f))
        vl
    in
    List.iter print_one lrm

  let print_state (out : out_channel) (d : absdom) : unit =
    fprintf out "digraph memory {\n%sgraph [dpi=300];\n" indent;
    begin
      match d with
      | AbsState st ->
          print_env out st.st_env;
          print_mem out st.st_mem
      | Top -> ()
    end;
    fprintf out "}"

  let print_rev_state (out : out_channel) (d : absdom) : unit =
    fprintf out "digraph memory {\n%sgraph [dpi=300];\n" indent;
    begin
      match d with
      | AbsState st ->
          print_rev_env out st.st_rev_env;
          print_rev_mem out st.st_rev_mem
      | Top -> ()
    end;
    fprintf out "}"
end
