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

let paths_to_string (paths : path_map) : string =
  list_to_string_bracket
    (fun (x, t) -> sprintf "%s.%s" (ident_to_string x) (PathTree.to_string t))
    (List.of_seq (IdentMap.to_seq paths))

let is_prim (c : ctyp) : bool =
  match c with
  | CBool | CInt32 | CInt64 -> true
  | CFun (_, _) | CArray _ -> raise unsupported
  | _ -> false

let rec paths_to_loc_rec (rev : rev_asbenv) (rm : rev_absmem) (curr : absloc)
    (p : path) (paths : path_map) : path_map =
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

(** [paths_to_loc st loc] computes all paths leading to the location [loc] in
    [st]. *)
let paths_to_loc (st : absstate) (loc : absloc) : path_map =
  paths_to_loc_rec st.st_rev_env st.st_rev_mem loc [] IdentMap.empty

(** [paths_to_loc_suffix st loc suffix] computes all paths leading to the
    location [loc] in [st] and suffixes them with [suffix]. *)
let paths_to_loc_suffix (st : absstate) (loc : absloc) (suffix : path) :
    path_map =
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
          env_add st x lv
    | _ -> st
  in
  match a_inv with
  | Some t ->
      (* x inherits the invalid paths from v. *)
      inv_add st' x t
  | None ->
      (* If variable showing occurs, removes the value mapped to x in st'.st_inv *)
      { st' with st_inv = IdentMap.remove x st'.st_inv }

(** [exec_set_struct_proj x a f ty st] computes the transfer function for the
    statement [set x = a.f] on [st]. [ty] is the type of the field [f] in the
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
        | None ->
            (* If variable showing occurs, removes the value mapped to x in st'.st_inv *)
            { st' with st_inv = IdentMap.remove x st'.st_inv }
      end
  | _ -> assert false

(** [exec_set_struct_update ts x a f v st] computes the transfer function for
    the statement [set x = x.f <- v] on [st]. *)
let exec_set_struct_update (ts : types) (x : ident) (a : atom) (f : ident)
    (v : atom) (st : absstate) : absstate =
  match a with
  | AVar (y, CStruct sy) ->
      let ly = IdentMap.find y st.st_env in
      (* All paths leading to all locations pointed by y suffixed by f are now invalid. *)
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
      (* x.f inherits the invalid paths from v. *)
      let v_inv =
        match invalid_paths_of_atom st.st_inv v with
        | Some t -> Some (Node [(f, t)])
        | None -> None
      in
      (* x inherits the invalid paths from y
         - if y was already completely invalid, x.f is valid (modulo invalid paths from v) but all x.f' s.t. f' <> f are invalid;
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
  List.for_all
    (fun (a : atom) ->
      match a with
      | AVar (x, _) -> pointsto_unique st x
      | _ -> true)
    args

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
  fst (is_tree_loc_aux m curr visited)

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
    function call, i.e. that each arguments point to trees and that there is not
    inter-aliasing between arguments. *)
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
    prefixed by the variable [x]. *)
let aliased_paths_of_pmap (st : absstate) (pm : path_map) : path_map =
  IdentMap.fold
    (fun k t acc -> inv_union (aliased_paths_of_ptree st k t) acc)
    pm
    IdentMap.empty

(** [args_bjection params args] computes the bijection map from from parameters
    to arguments. It binds each parameter x to its corresponding argument y if y
    is a variable. *)
let rec args_bijection (params : ident list) (args : atom list) :
    ident IdentMap.t =
  match (args, params) with
  | [], [] -> IdentMap.empty
  | AVar (x, ty) :: args', y :: params' ->
      let r = args_bijection params' args' in
      if is_prim ty then r else IdentMap.add y x r
  | _, _ -> assert false

(** [mem_bijection ts fields loc1 loc2 m1 m2 bij] computes the bijection between
    memories [m1] and [m2], starting at location [l1] in [m1] and [l2] in [m2].
    [bij] is an accumulator for the bijection map. It associates each location
    of [m1] to a location [m2]. [ts] is the environment of struct types.
    [fields] is the list of fields corrsponding to the structure represented by
    [loc1] and [loc2]. *)
let rec mem_bijection (ts : types) (fields : (ident * ctyp) list)
    (loc1 : absloc) (loc2 : absloc) (m1 : absmem) (m2 : absmem)
    (bij : ident IdentMap.t) : ident IdentMap.t =
  match fields with
  | [] -> bij
  | (fid, ftyp) :: fields' ->
      (* debug_info true
      @@ sprintf
           "%s\n"
           (list_to_string_braces
              (fun (id, ty) ->
                sprintf
                  "%s: %s"
                  (ident_to_string id)
                  (PrintTypes.ctyp_to_string ty))
              fields); *)
      if is_prim ftyp then mem_bijection ts fields' loc1 loc2 m1 m2 bij
      else
        (* If the field is not primitive, then continuing exploring the memory loc1 and loc2 *)
        let l1 = IdentPairMap.find_opt (loc1, fid) m1 in
        let l2 = IdentPairMap.find_opt (loc2, fid) m2 in
        let bij' =
          match (l1, l2) with
          | Some l1, Some l2 ->
              if IdentSet.cardinal l1 = 1 && IdentSet.cardinal l2 = 1 then
                let lv1 = IdentSet.choose l1 in
                let lv2 = IdentSet.choose l2 in
                let sid =
                  match ftyp with
                  | CStruct sid -> sid
                  | _ -> assert false
                in
                begin
                  match types_get ts sid with
                  | Errors.OK fields_f ->
                      mem_bijection
                        ts
                        fields_f
                        lv1
                        lv2
                        m1
                        m2
                        (IdentMap.add lv1 lv2 bij)
                  | Errors.Error _ -> assert false
                end
              else failwith "mem_bijection error"
          | _, _ -> failwith "mem_bijection error"
        in
        mem_bijection ts fields' loc1 loc2 m1 m2 bij'

(** [locs_bijection ts v1 v2 ty st1 st2] computes the bijection between
    locations contained in [st1] and [st2]. It calls [mem_bijection] from the
    locations pointed by the variable [v1] of [st1] and [v2] of [st2]. [ts] is
    the environment of struct types. [ty] is the type of the varibles [v1] and
    [v2]. *)
let locs_bijection (ts : types) (v1 : ident) (v2 : ident) (ty : ctyp)
    (st1 : absstate) (st2 : absstate) : ident IdentMap.t =
  match ty with
  | CStruct sid -> begin
      match types_get ts sid with
      | Errors.OK fields ->
          (* debug_info true @@ sprintf "Trying to find %s\n" (ident_to_string v1); *)
          let l1 = IdentMap.find v1 st1.st_env in
          (* debug_info true @@ sprintf "Trying to find %s\n" (ident_to_string v2); *)
          let l2 = IdentMap.find v2 st2.st_env in
          if IdentSet.cardinal l1 = 1 && IdentSet.cardinal l2 = 1 then
            let lv1 = IdentSet.choose l1 in
            (* debug_info true
            @@ sprintf
                 "Parameter %s is linked to location %s\n"
                 (ident_to_string v1)
                 (ident_to_string lv1); *)
            let lv2 = IdentSet.choose l2 in
            (* debug_info true
            @@ sprintf
                 "Argument %s is linked to location %s\n"
                 (ident_to_string v2)
                 (ident_to_string lv2); *)
            mem_bijection
              ts
              fields
              lv1
              lv2
              st1.st_mem
              st2.st_mem
              (IdentMap.add lv1 lv2 IdentMap.empty)
          else failwith "locs_bijection_var error"
      | Errors.Error _ -> assert false
    end
  | _ -> assert false

(** [funcall_bijection ts args params stcallee stcaller] computes the bijection
    between the state of the callee and the state of the caller. It returns a
    map which associate each paramater in [params] to its corresponding argument
    in [args], and associated each location of [stcallee] to its corresponding
    location in [stcaller]. [ts] is the struct types environment. *)
let funcall_bijection (show_debug : bool) (ts : types)
    (params : (ident * ctyp) list) (args : atom list) (stcallee : absstate)
    (stcaller : absstate) : ident IdentMap.t * ident IdentMap.t =
  let vars_bij = args_bijection (List.map fst params) args in
  debug_info show_debug
  @@ sprintf
       "Parameters binding: %s\n"
       (list_to_string_bracket
          (fun (k, v) ->
            sprintf "%s -> %s" (ident_to_string k) (ident_to_string v))
          (List.of_seq (IdentMap.to_seq vars_bij)));
  let locs_bij =
    List.fold_left
      (fun acc (v, ty) ->
        IdentMap.union
          (fun _ v1 v2 ->
            if v1 <> v2 then failwith "no bijection possible" else Some v1)
          (locs_bijection ts v (IdentMap.find v vars_bij) ty stcallee stcaller)
          acc)
      IdentMap.empty
      (List.fold_right
         (fun (id, ty) acc -> if is_prim ty then acc else (id, ty) :: acc)
         params
         [])
  in
  (vars_bij, locs_bij)

let apply_ident_bijection (bij : ident IdentMap.t) (x : ident) : ident =
  match IdentMap.find_opt x bij with
  | Some x' -> x'
  | None -> x

(** [apply_state_bijection vars_bij locs_bij st] replaces each variable and
    location of [st] by its corresponding value given in [vars_bij] and
    [locs_bij]. *)
let apply_state_bijection (vars_bij : ident IdentMap.t)
    (locs_bij : ident IdentMap.t) (st : absstate) : absstate =
  let ev =
    IdentMap.fold
      (fun v ls acc ->
        let v' = apply_ident_bijection vars_bij v in
        let ls' = IdentSet.map (apply_ident_bijection locs_bij) ls in
        IdentMap.add v' ls' acc)
      st.st_env
      IdentMap.empty
  in
  let rev = env_reverse ev in
  let m =
    IdentPairMap.fold
      (fun (l, f) ls acc ->
        let l' = apply_ident_bijection locs_bij l in
        let ls' = IdentSet.map (apply_ident_bijection locs_bij) ls in
        IdentPairMap.add (l', f) ls' acc)
      st.st_mem
      IdentPairMap.empty
  in
  let rm = mem_reverse m in
  let res = IdentSet.map (apply_ident_bijection locs_bij) st.st_res in
  let inv =
    IdentMap.fold
      (fun v t acc ->
        let v' = apply_ident_bijection vars_bij v in
        IdentMap.add v' t acc)
      st.st_inv
      IdentMap.empty
  in
  let inv_res = st.st_inv_res in
  make_state ev m rev rm res inv inv_res

(** [exec_set_call x a args ty fe st nctr] computes the transfer function for
    the statement [set x = a (args)] on [st]. [fe] is the function descriptor
    environment. [ty] is the type of the return value. *)
let exec_set_call (show_debug : bool) (ts : types) (x : ident) (a : atom)
    (args : atom list) (ty : ctyp) (fe : fenv) (st : absstate) : absdom =
  match a with
  | AVar (y, _) ->
      let fdescr =
        match IdentMap.find_opt y fe with
        | Some descr -> descr
        | None -> raise unsupported
      in
      (* The call state is built by filtering the environment and invalid paths on the function arguments.
         The memory stays the same, it is just that some part of it will be inaccessible. *)
      let ev_call = IdentMap.filter (fun k _ -> is_arg k args) st.st_env in
      let rev_call = env_reverse ev_call in
      let inv_call = IdentMap.filter (fun k _ -> is_arg k args) st.st_inv in
      let stcall =
        make_state
          ev_call
          st.st_mem
          rev_call
          st.st_rev_mem
          set_empty
          inv_call
          None
      in
      (* We then build the bijections for the variables and the locations between the current call state,
         and the pre-requisite call state of the callee. *)
      let vars_bij, locs_bij =
        funcall_bijection
          show_debug
          ts
          fdescr.fd_params
          args
          fdescr.fd_callstate
          stcall
      in
      (* We check that all arguments are valid and well-formed. *)
      let args_validity = List.for_all (is_valid_atom (AbsState stcall)) args in
      if
        args_pointsto_unique stcall args && wf_args stcall args && args_validity
      then
        let d' =
          (* The return state is the one given by the function descriptor on which we apply the bijections. *)
          let* returnstate = fdescr.fd_returnstate in
          let stret = apply_state_bijection vars_bij locs_bij returnstate in
          (* The state before the call "st" and the return state "stret" must now be merged.
             The merge operation is the following:
             - The new environment is the one of the inital state + the new binding for x that points to
               the result location of the return state. This is due to the fact that, as arguments are renamed during
               compilation, we never assign an argument to another value. So for every key "v" in stret.st_env,
               s.t. "v" was an argument, the points-to set of "v" is the same in stret.st_env and st.st_env
             - The variable x of the set-call statement is binded to the result locations of the return state.
             - If a pair (l, f) is a key of the return state memory, it means that it was accessible from the arguments.
               We just keep the value associated with (l, f) from this return state in the new memory.
             - If a pair (l, f) is NOT a key of return state memory,
               then we keep the value associated with (l, f) from the initial state.
               Note that as we do not have allocation, the set of keys (l, f) in the return state memory is a subset of
               the one of the initial state memory.
             - The invalid paths of the resulting state will contain:
               + The invalid paths of the initial state;
               + The invalid paths of the return state;
               + The paths that were aliased with some arguments that themselves contained invalid paths when the function returns. *)
          let st' = if is_prim ty then st else env_add st x stret.st_res in
          let m_ret =
            IdentPairMap.merge
              (fun _ ls1 ls2 ->
                match (ls1, ls2) with
                | Some ls1, _ -> Some ls1
                | None, Some ls2 -> Some ls2
                | None, None -> None)
              stret.st_mem
              st'.st_mem
          in
          let rm_ret = mem_reverse m_ret in
          let inv_ret =
            (* If variable shadowing occurs, we must remove the binding with x in the invalid paths. *)
            let iv_args_alias =
              IdentMap.remove x (aliased_paths_of_pmap st stret.st_inv)
            in
            let iv_init = IdentMap.remove x st.st_inv in
            let iv_ret = IdentMap.remove x stret.st_inv in
            let iv =
              match stret.st_inv_res with
              | Some t -> IdentMap.add x t iv_ret
              | None -> iv_ret
            in
            inv_union (inv_union iv_init iv) iv_args_alias
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

(** [absexec ts fe ce d s] computes the transfer function for the statement [s]
    on [d]. [fe] is the function descriptor environement. [ts] is the struct
    types environment. *)
let rec absexec (show_debug : bool) (ts : types) (fe : fenv) (d : absdom)
    (s : Imp1Typed.statement) : Imp1.Aliasing_AST.statement * absdom =
  match s with
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
        match c with
        | CpAtom (a, _) -> AbsState (exec_set_atom x a st)
        | CpStructProj (a, f, ty) -> AbsState (exec_set_struct_proj x a f ty st)
        | CpStructUpdate (a, f, v, _) ->
            AbsState (exec_set_struct_update ts x a f v st)
        | CpCall (a, args, ty) ->
            debug_info show_debug
            @@ sprintf
                 "Entering function call \"%s\" ==========\n"
                 (PrintSyntax.PrintTyped.comp_to_string c);
            let r = exec_set_call show_debug ts x a args ty fe st in
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
      let s1', d1 = absexec show_debug ts fe d s1 in
      let s2', d2 = absexec show_debug ts fe d s2 in
      let d' = AbsDom.union d1 d2 in
      (Imp1.Aliasing_AST.StIfThenElse (a, s1', s2'), d')
  | StSequence (s1, s2) ->
      let s1', d1 = absexec show_debug ts fe d s1 in
      let s2', d2 = absexec show_debug ts fe d1 s2 in
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

(** [is_param v params] checks wether the variable [v] is contained in the
    parameter list [params]. *)
let is_param (v : ident) (params : (ident * ctyp) list) : bool =
  List.exists (fun (pid, _) -> v = pid) params

(** [gen_fun_descr _ ts fe f] generates the function descriptor for [f]. *)
let gen_fun_descr_and_ast (show_debug : bool) (ts : types) (fe : fenv)
    (f : coq_function) : fun_descr * Imp1.Aliasing_AST.statement =
  let callstate = gen_valid_call_state ts f.fn_params in
  let ast, returnstate =
    absexec show_debug ts fe (AbsState callstate) f.fn_body
  in
  (* We filter the returned environment and set of invalid paths to only keep the bindings
     for which the key is a function paramater. *)
  let returnstate =
    let* retstate = returnstate in
    let ev_ret =
      IdentMap.filter (fun v _ -> is_param v f.fn_params) retstate.st_env
    in
    let rev_ret = env_reverse ev_ret in
    let inv_ret =
      IdentMap.filter (fun v _ -> is_param v f.fn_params) retstate.st_inv
    in
    AbsState
      { retstate with st_env = ev_ret; st_rev_env = rev_ret; st_inv = inv_ret }
  in
  let fdescr =
    {
      fd_params = f.fn_params;
      fd_callstate = callstate;
      fd_returnstate = returnstate;
    }
  in
  (fdescr, ast)

(** [get_fun_descr p fname] returns the function descriptor of [fname] if a
    function is defined with this name in the program [p]. *)
let get_fun_descr (p : program) (fname : string) : fun_descr option =
  let fid = ident_of_string fname in
  let rec aux fe defs =
    match defs with
    | [] -> None
    | DefFun (x, f) :: defs' ->
        let fdescr, _ = gen_fun_descr_and_ast false p.prog_types fe f in
        if Common.ident_eq_dec x fid then Some fdescr
        else aux (IdentMap.add x fdescr fe) defs'
    | _ :: defs' -> aux fe defs'
  in
  aux IdentMap.empty p.prog_defs

(** [gen_aliasing_function ts fe f] generates the AST corresponding to the
    function [f] with the aliasing information. *)
let gen_aliasing_function (show_debug : bool) (ts : types) (fe : fenv)
    (x : ident) (f : Imp1Typed.coq_function) :
    (Imp1.Aliasing_AST.coq_function * fenv) option =
  let stcall = gen_valid_call_state ts f.fn_params in
  let args = List.map (fun (v, ty) -> Syntax.Typed.AVar (v, ty)) f.fn_params in
  assert (args_pointsto_unique stcall args);
  assert (wf_args stcall args);
  let fdescr, body' = gen_fun_descr_and_ast show_debug ts fe f in
  let fe' = IdentMap.add x fdescr fe in
  match fdescr.fd_returnstate with
  | AbsState st' ->
      if wf_args st' args then
        let f' =
          { fn_return = f.fn_return; fn_params = f.fn_params; fn_body = body' }
        in
        Some (f', fe')
      else None
  | Top -> None

(** [gen_aliasing_globdef ts fe def] generates the aliasing AST for the global
    definition [def]. It also returns the new function descriptor environment if
    the global def is a function. *)
let gen_aliasing_globdef (ts : types) (fe : fenv) (def : Imp1Typed.globdef)
    (show_debug : bool) : (Imp1.Aliasing_AST.globdef * fenv) option =
  match def with
  | DefFun (x, f) ->
      debug_info show_debug
      @@ sprintf "Analysing function %s...\n" (ident_to_string x);
      let r =
        match gen_aliasing_function show_debug ts fe x f with
        | Some (f', fe') -> Some (DefFun (x, f'), fe')
        | None -> None
      in
      debug_info show_debug
      @@ sprintf "Analysis of function %s finished.\n\n" (ident_to_string x);
      r
  | DefConst (x, l, ty) -> Some (DefConst (x, l, ty), fe)

(** [gen_aliasing_program prog] generates the aliasing AST for the whole Imp1
    program [prog]. *)
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
