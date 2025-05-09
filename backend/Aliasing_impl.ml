open Printf
open Types
open Syntax
open Syntax.Typed
open Typing
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
    "function pointers are not handled by the alias analysis yet"

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

(** [paths_to_string paths] transforms an invalid path map into a string. *)
let paths_to_string (paths : path_map) : string =
  list_to_string_bracket
    (fun (x, t) -> sprintf "%s.%s" (ident_to_string x) (PathTree.to_string t))
    (List.of_seq (IdentMap.to_seq paths))

(** [is_prim ty] checks wether a value of type [ty] is primitive (i.e. it's a
    boolean or integer value). *)
let is_prim (ty : ctyp) : bool =
  match ty with
  | CBool | CInt32 _ | CInt64 _ -> true
  | CFun (_, _) -> raise unsupported
  | _ -> false

(** [is_array ty] checks wether a value of type [ty] is an array. *)
let is_array (ty : ctyp) : bool =
  match ty with
  | CArray _ -> true
  | CFun (_, _) -> raise unsupported
  | _ -> false

(** [paths_to_loc_rec rev rm curr p paths] retrieves all the paths leading to
    the location [curr] given the reverse environment [rev] and reverse memory
    [rm], and stores them into a path map.
    - [p] is an accumulator which contains the current path being explored.
    - [paths] is an accumulator which contains the path map computed until now.
*)
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

(** [paths_to_loc_suffixed st loc suffix] computes all paths leading to the
    location [loc] in [st] and suffixes them with [suffix]. *)
let paths_to_loc_suffixed (st : absstate) (loc : absloc) (suffix : path) :
    path_map =
  paths_to_loc_rec st.st_rev_env st.st_rev_mem loc suffix IdentMap.empty

(** [invalid_paths_with_prefix inv x p] returns the invalid paths with prefix
    [x.p] in [inv]. *)
let invalid_paths_with_prefix (inv : path_map) (x : ident) (p : path) :
    path_tree option =
  match IdentMap.find_opt x inv with
  | Some t -> PathTree.prefixed_by t p
  | None -> None

(** [invalid_paths_of_atom inv a] returns the invalid paths of all variables
    contained in [a]. *)
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
    [set x := a] on [st]. *)
let exec_set_atom (x : ident) (a : atom) (st : absstate) : absstate =
  let a_inv = invalid_paths_of_atom st.st_inv a in
  let st' =
    match a with
    | AVar (v, ty) ->
        if is_prim ty then st
        else
          let lv = IdentMap.find v st.st_env in
          (* If v is not primitive, makes x point to all locations pointed by v. *)
          env_add st x lv
    | _ -> st
  in
  match a_inv with
  | Some t ->
      (* x inherits the invalid paths from v. *)
      inv_add st' x t
  | None ->
      (* If variable shadowing occurs, removes x from the map of invalid paths. *)
      { st' with st_inv = IdentMap.remove x st'.st_inv }

(** [vars_aliased_to_loc rev loc] returns the variable set that may point to
    [loc]. If no variable points to [loc], it returns an empty set. *)
let vars_aliased_to_loc (rev : rev_asbenv) (loc : absloc) : var_set =
  match IdentMap.find_opt loc rev with
  | Some vars -> vars
  | None -> set_empty

(** [vars_aliased_to_loc_set rev locs] returns the variable set that may point
    to the locations belonging to [locs]. *)
let vars_aliased_to_loc_set (rev : rev_asbenv) (locs : pointsto_set) : var_set =
  IdentSet.fold
    (fun li acc -> IdentSet.union (vars_aliased_to_loc rev li) acc)
    locs
    IdentSet.empty

(** [exec_set_struct_proj x a f ty st] computes the transfer function for the
    statement [set x := a.f] on [st]. [ty] is the type of the field [f] in the
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
          (* If a.f is not primitive, makes x point to all locations pointed by a.f. *)
          let st' = env_add st x ly_f in
          st'
      in
      begin
        match yf_inv with
        | Some t ->
            (* x inherits the invalid paths from y.f. *)
            inv_add st' x t
        | None ->
            (* If variable shadowing occurs, removes x from the map of invalid paths. *)
            { st' with st_inv = IdentMap.remove x st'.st_inv }
      end
  | _ -> assert false

(** [exec_set_struct_update ts x a f v st] computes the transfer function for
    the statement [set x := y.f <- v] on [st]. *)
let exec_set_struct_update (se : senv) (x : ident) (a : atom) (f : ident)
    (v : atom) (st : absstate) : absstate =
  match a with
  | AVar (y, CStruct sy) ->
      let ly = IdentMap.find y st.st_env in
      (* All paths leading to all locations pointed by y, suffixed by f, are now invalid. *)
      let inv' =
        IdentSet.fold
          (fun l acc ->
            let l_inv = paths_to_loc_suffixed st l [f] in
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
         - otherwise, if some y.f', f' <> f were invalid, then x.f' remains invalid. *)
      let y_inv =
        match invalid_paths_with_prefix st.st_inv y [] with
        | Some (Leaf | Node []) -> begin
            match senv_get se sy with
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
              (* If v is not primitive, makes x.f point to all locations pointed by v. *)
              let lv = IdentMap.find v st.st_env in
              IdentSet.fold (fun l acc -> mem_add acc (l, f) lv) ly st
        | _ -> st
      in
      (* x points to all locations pointed by y. *)
      let st' = env_add st' x ly in
      let inv' =
        match x_inv with
        | Some t -> IdentMap.add x t inv'
        | None -> inv'
      in
      { st' with st_inv = inv' }
  | _ -> assert false

let _INDEX : ident = ident_of_string "[]"

(** [exec_set_array_get x a i st] executes the transfer function for the
    statement [set x := a[i]] on [st]. If an element of the array [a] has
    already been accessed before, then accessing [a[i]] is forbidden. *)
let exec_set_array_get (x : ident) (a : atom) (i : atom) (st : absstate) :
    absdom =
  match a with
  | AVar (y, CArray ty) ->
      let ly = IdentMap.find y st.st_env in
      (* All locations in ly should be free. *)
      let all_free =
        IdentSet.for_all
          (fun l -> IdentMap.find_opt l st.st_arr_locked = None)
          ly
      in
      if all_free then
        let yi_inv = invalid_paths_with_prefix st.st_inv y [_INDEX] in
        let st' =
          if is_prim ty then st
          else
            let ly = IdentMap.find y st.st_env in
            let ly_i =
              IdentSet.fold
                (fun l acc ->
                  IdentSet.union acc (AbsDom.mem_get st.st_mem l _INDEX))
                ly
                set_empty
            in
            (* If y[i] is not primitive, makes x point to all locations pointed by y[i]. *)
            let st' = env_add st x ly_i in
            (* Updates the locked arrays environment. *)
            let al =
              IdentSet.fold
                (fun li acc -> IdentMap.add li i acc)
                ly
                st.st_arr_locked
            in
            { st' with st_arr_locked = al }
        in
        begin
          match yi_inv with
          | Some t ->
              (* x inherits the invalid paths from y[i]. *)
              AbsState (inv_add st' x t)
          | None ->
              (* If variable shadowing occurs, removes x from the map of invalid paths. *)
              AbsState { st' with st_inv = IdentMap.remove x st'.st_inv }
        end
      else Top
  | _ -> assert false

(** [exec_set_array_set x a i v st] executes the transfer function for the
    statement [set x := a[i] <- v] on [st]. *)
let exec_set_array_set (x : ident) (a : atom) (i : atom) (v : atom)
    (st : absstate) : absdom =
  match a with
  | AVar (y, CArray ty) ->
      let ly = IdentMap.find y st.st_env in
      (* All paths leading to all locations pointed by y are now invalid. *)
      let inv' =
        IdentSet.fold
          (fun l acc ->
            let l_inv = paths_to_loc st l in
            inv_union l_inv acc)
          ly
          st.st_inv
      in
      (* If variable shadowing occurs, and a had invalid paths, then removes them. *)
      let inv' = IdentMap.remove x inv' in
      let v_inv =
        match invalid_paths_of_atom st.st_inv v with
        | Some t -> Some (Node [(_INDEX, t)])
        | None -> None
      in
      let y_inv = invalid_paths_with_prefix st.st_inv y [] in
      let x_inv =
        (* If the array y is completely invalid, x also becomes invalid.
            If the array y contains invalid paths (i.e. there are invalid paths of the form
            y.[].SOMEHTING), then it means that a sub-element of the array has been modified,
            this element should be at index i (MUST BE WELL-TESTED!), so setting y[i] should
            not create invalid paths for x, modulo invalid paths from the value v we set in y[i]. *)
        match (v_inv, y_inv) with
        | _, Some (Leaf | Node []) -> Some Leaf
        | Some t1, _ -> Some t1
        | None, Some _ -> None
        | None, None -> None
      in
      (* We check that all locations pointed by y (i.e. ly) are locked with the same array index i,
         or that they are all free. *)
      let all_locked_same_index =
        IdentSet.for_all
          (fun li ->
            match IdentMap.find_opt li st.st_arr_locked with
            | Some i' -> i = i'
            | None -> false)
          ly
      in
      let all_free =
        IdentSet.for_all
          (fun li -> IdentMap.find_opt li st.st_arr_locked = None)
          ly
      in
      if all_locked_same_index || all_free then
        let st' =
          match v with
          | AVar (v, ty) ->
              if is_prim ty then st
              else
                let lv = IdentMap.find v st.st_env in
                (* x[] points to all locations pointed by v. *)
                IdentSet.fold (fun l acc -> mem_add acc (l, _INDEX) lv) ly st
          | _ -> st
        in
        (* x points to all locations pointed by y. *)
        let st' = env_add st' x ly in
        let inv' =
          match x_inv with
          | Some t -> IdentMap.add x t inv'
          | None -> inv'
        in
        (* As we can not detect sharing with our abstraction of arrays,
           variables (and its aliases) set as an element of array become invalid. *)
        let inv' =
          match v with
          | AVar (xv, ty) ->
              if is_prim ty then inv'
              else
                let lyv = IdentMap.find xv st'.st_env in
                let xv_and_aliased_vars =
                  vars_aliased_to_loc_set st.st_rev_env lyv
                in
                IdentSet.fold
                  (fun var acc -> IdentMap.add var Leaf acc)
                  xv_and_aliased_vars
                  inv'
          | _ -> inv'
        in
        (* We now unlock the locations pointed by y. *)
        let al =
          IdentSet.fold
            (fun li acc -> IdentMap.remove li acc)
            ly
            st.st_arr_locked
        in
        AbsState { st' with st_inv = inv'; st_arr_locked = al }
      else Top
  | _ -> assert false

(** [path_of_access_list acs] transforms th access list [acs] into a path. *)
let rec path_of_access_list (acs : access list) : path =
  match acs with
  | [] -> []
  | AcStructField (f, _) :: acs' -> f :: path_of_access_list acs'
  | AcArrayIndex (_, _) :: acs' -> _INDEX :: path_of_access_list acs'

(** [exec_set_deep_access x a acs ty st] executes the transfer function for the
    statement [set x := a\acs\ on [st]]. [ty] is the type of the value returned
    by the deep access. *)
let exec_set_deep_access (x : ident) (a : atom) (acs : access list) (ty : ctyp)
    (st : absstate) : absstate =
  match a with
  | AVar (y, _) ->
      if is_prim ty then
        (* x inherits the invalid paths given by the access list *)
        let acs_inv =
          invalid_paths_with_prefix st.st_inv y (path_of_access_list acs)
        in
        match acs_inv with
        | Some t -> inv_add st x t
        | None ->
            (* if variable shadowing occurs, removex x from the map of invalid paths. *)
            { st with st_inv = IdentMap.remove x st.st_inv }
      else assert false
  | _ -> assert false

(** [is_arg v args] checks wether the variable [v] is contained in the argument
    list [args]. *)
let is_arg (v : ident) (args : atom list) : bool =
  List.exists
    (fun a ->
      match a with
      | Syntax.Typed.AVar (x, _) -> if x = v then true else false
      | _ -> false)
    args

(** [pointsto_unique st x] checks wether the variable [x] points to only one
    abstract location in [st]. *)
let pointsto_unique (st : absstate) (x : ident) : bool =
  match IdentMap.find_opt x st.st_env with
  | Some locs -> IdentSet.cardinal locs = 1
  | None -> true

(** [args_points_unique st args] checks wether each function's arguments points
    to only one abstract location in [st]. *)
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
          if l = curr then List.append (IdentSet.elements locs) acc else acc)
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

let rec aliased_paths_rec (m : absmem) (rev : rev_asbenv) (rm : rev_absmem)
    (loc : absloc) (p : path) (paths : path_map) : path_map =
  match p with
  | [] ->
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
  match (params, args) with
  | [], [] -> IdentMap.empty
  | y :: params', a :: args' ->
      let r = args_bijection params' args' in
      begin
        match a with
        | AVar (x, ty) -> if is_prim ty then r else IdentMap.add y x r
        | _ -> r
      end
  | _, _ -> assert false

let rec mem_bijection (se : senv) (edges : (ident * ctyp) list) (loc1 : absloc)
    (loc2 : absloc) (m1 : absmem) (m2 : absmem) (bij : ident IdentMap.t) :
    ident IdentMap.t =
  match edges with
  | [] -> bij
  | (eid, etyp) :: edges' ->
      if is_prim etyp then mem_bijection se edges' loc1 loc2 m1 m2 bij
      else
        let l1 = IdentPairMap.find (loc1, eid) m1 in
        let l2 = IdentPairMap.find (loc2, eid) m2 in
        if IdentSet.cardinal l1 = 1 && IdentSet.cardinal l2 = 1 then
          let lv1 = IdentSet.choose l1 in
          let lv2 = IdentSet.choose l2 in
          let edges_e =
            match etyp with
            | CStruct sid -> begin
                match senv_get se sid with
                | Errors.OK fields -> fields
                | Errors.Error _ -> assert false
              end
            | CArray ta -> [(_INDEX, ta)]
            | _ -> assert false
          in
          mem_bijection se edges_e lv1 lv2 m1 m2 (IdentMap.add lv1 lv2 bij)
        else failwith "mem_bijection error"

let locs_bijection (se : senv) (v1 : ident) (v2 : ident) (ty : ctyp)
    (st1 : absstate) (st2 : absstate) : ident IdentMap.t =
  let l1 = IdentMap.find v1 st1.st_env in
  let l2 = IdentMap.find v2 st2.st_env in
  if IdentSet.cardinal l1 = 1 && IdentSet.cardinal l2 = 1 then
    let lv1 = IdentSet.choose l1 in
    let lv2 = IdentSet.choose l2 in
    let edges =
      match ty with
      | CStruct sid -> begin
          match senv_get se sid with
          | Errors.OK fields -> fields
          | Errors.Error _ -> assert false
        end
      | CArray ta -> [(_INDEX, ta)]
      | _ -> assert false
    in
    mem_bijection
      se
      edges
      lv1
      lv2
      st1.st_mem
      st2.st_mem
      (IdentMap.add lv1 lv2 IdentMap.empty)
  else failwith "locs_bijection_var error"

(** [funcall_bijection ts args params stcallee stcaller] computes the bijection
    between the state of the callee and the state of the caller. It returns a
    map which associate each paramater in [params] to its corresponding argument
    in [args], and associated each location of [stcallee] to its corresponding
    location in [stcaller]. [ts] is the struct types environment. *)
let funcall_bijection (show_debug : bool) (se : senv)
    (params : (ident * ctyp) list) (args : atom list) (stcallee : absstate)
    (stcaller : absstate) : ident IdentMap.t * ident IdentMap.t =
  let vars_bij = args_bijection (List.map fst params) args in
  debug_info show_debug
  @@ sprintf
       "Non-primitive parameters binding: %s\n"
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
          (locs_bijection se v (IdentMap.find v vars_bij) ty stcallee stcaller)
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
  (* st_arr_taken is only valid in the callee local scope.
     When apply_state_bijection is used after a function call (see set_call),
    this field is not meaningful anymore, so with set it as being empty. *)
  make_state ev m rev rm res inv inv_res IdentMap.empty

let rec vars_of_atom (a : atom) : IdentSet.t =
  match a with
  | AVar (x, _) -> IdentSet.singleton x
  | AUnaryOp (_, a1, _) -> vars_of_atom a1
  | ABinaryOp (_, a1, a2, _) ->
      IdentSet.union (vars_of_atom a1) (vars_of_atom a2)
  | _ -> set_empty

(** [proj_mem m root pmem visited] extracts the sub-memory of [m] reachable from
    [root]. [pmem] is the accumulator for the resulting memory and [visited] is
    the one for all visited locations. *)
let rec proj_mem (m : absmem) (root : absloc) (pmem : absmem)
    (visited : IdentSet.t) : absmem * IdentSet.t =
  if IdentSet.mem root visited then (pmem, visited)
  else
    let pmem', visited' =
      IdentPairMap.fold
        (fun (l, f) locs (accM, accV) ->
          if l = root then
            IdentSet.fold
              (fun loc (accM1, accV1) ->
                let accM1' =
                  IdentPairMap.update
                    (l, f)
                    (fun li ->
                      match li with
                      | Some li -> Some (IdentSet.add loc li)
                      | None -> Some (IdentSet.singleton loc))
                    accM1
                in
                proj_mem m loc accM1' accV1)
              locs
              (accM, accV)
          else (accM, accV))
        m
        (pmem, visited)
    in
    (pmem', IdentSet.add root visited')

(** [proj_state st vars] builds the projection of [st] on the variables [vars].
*)
let proj_state (st : absstate) (vars : var_set) : absstate =
  (* The environment is projected on the variables *)
  let ev = IdentMap.filter (fun k _ -> IdentSet.mem k vars) st.st_env in
  let rev = env_reverse ev in
  (* The invalid path environment is projected on the variables *)
  let inv = IdentMap.filter (fun k _ -> IdentSet.mem k vars) st.st_inv in
  let inv_res = st.st_inv_res in
  (* To build the memory projection, we make a DFS from all the locations pointed by
     the variables. *)
  let roots =
    IdentMap.fold
      (fun _ locs roots -> IdentSet.union locs roots)
      ev
      IdentSet.empty
  in
  let m, visited =
    IdentSet.fold
      (fun root (m, visited) -> proj_mem st.st_mem root m visited)
      roots
      (IdentPairMap.empty, IdentSet.empty)
  in
  let rm = mem_reverse m in
  (* The locked arrays environment is projected on all locations contained
     in the projection of the memory. *)
  let arr_locked =
    IdentMap.filter (fun k _ -> IdentSet.mem k visited) st.st_arr_locked
  in
  (* The set of retruned locations is projected on all locations contained
     in the projection of the memory. *)
  let res = IdentSet.filter (fun r -> IdentSet.mem r visited) st.st_res in
  make_state ev m rev rm res inv inv_res arr_locked

(** [build_call_state st args] build the state for a function call with
    arguments [args] from [st]. *)
let build_call_state (st : absstate) (args : atom list) : absstate =
  let vars_in_params : var_set =
    IdentMap.to_seq st.st_env |> Seq.map fst
    |> Seq.filter (fun v -> is_arg v args)
    |> IdentSet.of_seq
  in
  let stcall = proj_state st vars_in_params in
  { stcall with st_res = IdentSet.empty; st_arr_locked = IdentMap.empty }

(** [exec_set_call x a args ty fe st nctr] computes the transfer function for
    the statement [set x = a (args)] on [st]. [fe] is the function descriptor
    environment. [ty] is the type of the return value. *)
let exec_set_call (show_debug : bool) (se : senv) (x : ident) (a : atom)
    (args : atom list) (ty : ctyp) (fe : fenv) (st : absstate) : absdom =
  match a with
  | AVar (y, _) ->
      let fdescr =
        match IdentMap.find_opt y fe with
        | Some descr -> descr
        | None -> raise unsupported
      in
      let stcall = build_call_state st args in
      (* We build the bijections for the variables and the locations between the current call state,
         and the pre-requisite call state of the callee. *)
      let vars_bij, locs_bij =
        funcall_bijection
          show_debug
          se
          fdescr.fd_params
          args
          fdescr.fd_callstate
          stcall
      in
      (* Before calling the function, we must check the following things: 
         - All arguments are completely valid;
         - Each non-primitive argument points to only one abstract location;
         - Each argument points to a tree-shaped part of the memory;
         - There is no inter-aliasing between arguments. *)
      let args_validity = List.for_all (is_valid_atom (AbsState stcall)) args in
      if
        args_pointsto_unique stcall args && wf_args stcall args && args_validity
      then
        let d' =
          (* The return state is the one given by the function descriptor on which we apply the bijection. *)
          let* returnstate = fdescr.fd_returnstate in
          let stret = apply_state_bijection vars_bij locs_bij returnstate in
          (* The state before the call "st" and the return state "stret" must be merged.
             The merge operation is the following:
             - The new environment is the one of the inital state + the new binding for x that points to
               the result locations of the return state (stret.st_res). 
               As function parameters are renamed by the frontend, we never assign an argument to another value.
               So for every key "v" in stret.st_env, s.t. "v" was an argument, the points-to set of "v" is the same
               in stret.st_env and st.st_env.
             - If a pair (l, f) is a key of the return state memory, it means that it was accessible from the arguments.
               We just keep the value associated with (l, f) from this return state in the new memory.
             - If a pair (l, f) is NOT a key of the return state memory,
               then we keep the value associated with (l, f) from the initial state.
               Note that as we do not have allocation, the set of keys (l, f) in the return state memory is a subset of
               the one of the initial state memory.
             - The invalid paths of the resulting state will contain:
               + The invalid paths of the initial state;
               + The invalid paths of the return state;
               + The paths that were aliased with some arguments that themselves contained invalid paths when the function returns.
             - The locked arrays are the one of the initial state. *)
          let st' = if is_prim ty then st else env_add st x stret.st_res in
          let m_ret =
            IdentPairMap.merge
              (fun _ ls1 ls2 ->
                match (ls1, ls2) with
                | Some ls1, _ -> Some ls1
                | None, Some ls2 -> Some ls2
                | None, None -> None)
              stret.st_mem
              st.st_mem
          in
          let rm_ret = mem_reverse m_ret in
          let inv_ret =
            (* If variable shadowing occurs, we must remove the binding of x in the map of invalid paths. *)
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
          let arr_locked = st.st_arr_locked in
          AbsState
            {
              st' with
              st_mem = m_ret;
              st_rev_mem = rm_ret;
              st_inv = inv_ret;
              st_inv_res = inv_res_ret;
              st_arr_locked = arr_locked;
            }
        in
        d'
      else Top
  | _ -> assert false

(** [invalidate_parent_arrays st] invalidates the paths leading to all arrays
    for which an element is contained in the returned locations [st.st_res]. *)
let invalidate_parent_arrays (st : absstate) =
  (* Get all "[]"-linked parent locations of locations contained in res *)
  let parent_arrays =
    IdentSet.fold
      (fun loc acc ->
        let parent_assoc_list =
          match IdentMap.find_opt loc st.st_rev_mem with
          | Some assoc_list -> assoc_list
          | None -> []
        in
        let parent_arrays =
          match List.assoc_opt _INDEX parent_assoc_list with
          | Some locs -> locs
          | _ -> IdentSet.empty
        in
        IdentSet.union acc parent_arrays)
      st.st_res
      IdentSet.empty
  in
  (* Compute the invalid paths from the parent arrays. *)
  let inv =
    IdentSet.fold
      (fun loc accS ->
        let paths = paths_to_loc st loc in
        inv_union accS paths)
      parent_arrays
      IdentMap.empty
  in
  { st with st_inv = inv_union st.st_inv inv }

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
    | None, None -> None
  in
  let st' = { st' with st_inv_res = inv_res } in
  (* We must invalidate the paths leading to arrays for which an element is returned, 
     because otherwise we loset the track of the source of the element.
     This makes the corresponding arrays unsuable after the function call and prevents
     the user from writing programs that would make sharing in arrays possible
     via a function call. *)
  invalidate_parent_arrays st'

let locked_arrays_to_string (st : absstate) : string =
  let arr_locked_var =
    IdentMap.fold
      (fun l a accM ->
        let vars = vars_aliased_to_loc st.st_rev_env l in
        IdentSet.fold (fun v accS -> IdentMap.add v a accS) vars accM)
      st.st_arr_locked
      IdentMap.empty
  in
  list_to_string_bracket
    (fun (v, a) ->
      sprintf
        "%s -> %s"
        (ident_to_string v)
        (PrintSyntax.PrintTyped.atom_to_string a))
    (List.of_seq (IdentMap.to_seq arr_locked_var))

let print_dom_debug (show_debug : bool) (d : absdom) (suffix : string)
    (res : atom option) : unit =
  (match d with
  | AbsState st ->
      debug_info show_debug
      @@ sprintf
           "INV_%s: %s\nARR_LOCKED_%s: %s\n"
           suffix
           (paths_to_string st.st_inv)
           suffix
           (locked_arrays_to_string st);
      begin
        match res with
        | Some a -> begin
            match st.st_inv_res with
            | Some t ->
                debug_info show_debug
                @@ sprintf
                     "INV_RES: %s.%s\n"
                     (PrintSyntax.PrintTyped.atom_to_string a)
                     (PathTree.to_string t)
            | None -> debug_info show_debug "INV_RES: None\n"
          end
        | None -> ()
      end
  | Top -> debug_info show_debug @@ sprintf "DOM_%s: Top\n" suffix);
  if suffix = "OUT" then debug_info show_debug "\n"

(** [absexec ts fe ce d s] computes the transfer function for the statement [s]
    on [d]. [fe] is the function descriptor environement. [ts] is the struct
    types environment. *)
let rec absexec (show_debug : bool) (se : senv) (fe : fenv) (d : absdom)
    (s : Imp1Typed.statement) : Imp1.Aliasing_AST.statement * absdom =
  match s with
  | StSet (x, c) ->
      (* We check that no shadowing occurs on a variable used for an array access. *)
      let d_in = d in
      print_dom_debug show_debug d_in "IN" None;
      let d' =
        let* st = d in
        let all_vars_in_array_get =
          IdentMap.fold
            (fun _ a acc -> IdentSet.union (vars_of_atom a) acc)
            st.st_arr_locked
            IdentSet.empty
        in
        if IdentSet.mem x all_vars_in_array_get then Top
        else
          match c with
          | CpAtom (a, _) -> AbsState (exec_set_atom x a st)
          | CpStructProj (a, f, ty) ->
              AbsState (exec_set_struct_proj x a f ty st)
          | CpStructUpdate (a, f, v, _) ->
              AbsState (exec_set_struct_update se x a f v st)
          | CpCall (a, args, ty) ->
              debug_info show_debug
              @@ sprintf
                   "Entering function call \"%s\" ==========\n"
                   (PrintSyntax.PrintTyped.comp_to_string c);
              let r = exec_set_call show_debug se x a args ty fe st in
              debug_info show_debug
              @@ sprintf
                   "Exiting function call \"%s\" ===========\n"
                   (PrintSyntax.PrintTyped.comp_to_string c);
              r
          | CpArrayGet (a, i, _) -> exec_set_array_get x a i st
          | CpArraySet (a, i, v, _) -> exec_set_array_set x a i v st
          | CpDeepAccess (a, acs, ty) ->
              AbsState (exec_set_deep_access x a acs ty st)
      in
      let s', d' = (Imp1.Aliasing_AST.StSet (x, c, d_in, d'), d') in
      debug_info show_debug
      @@ sprintf ">> %s\n" (PrintImp1.PrintTyped.statement_to_string_pref "" s);
      print_dom_debug show_debug d' "OUT" None;
      (s', d')
  | StIfThenElse (a, s1, s2) ->
      let s1', d1 = absexec show_debug se fe d s1 in
      let s2', d2 = absexec show_debug se fe d s2 in
      let d' = AbsDom.union d1 d2 in
      (Imp1.Aliasing_AST.StIfThenElse (a, s1', s2'), d')
  | StSequence (s1, s2) ->
      let s1', d1 = absexec show_debug se fe d s1 in
      let s2', d2 = absexec show_debug se fe d1 s2 in
      (Imp1.Aliasing_AST.StSequence (s1', s2'), d2)
  | StReturn a ->
      print_dom_debug show_debug d "IN" None;
      debug_info show_debug
      @@ sprintf ">> %s\n" (PrintImp1.PrintTyped.statement_to_string_pref "" s);
      let d' =
        let* st = d in
        let st' = exec_return a st in
        if is_tree_locs st'.st_mem (IdentSet.elements st.st_res) then
          AbsState st'
        else Top
      in
      let s', d' = (Imp1.Aliasing_AST.StReturn (a, d, d'), d') in
      print_dom_debug show_debug d' "OUT" (Some a);
      (s', d')

(** [gen_valid_call_state ts params] generates a valid call state w.r.t. the
    function parameters [params]. *)
let gen_valid_call_state (se : senv) (params : (ident * ctyp) list) : absstate =
  let gen_field_loc_id lid fname =
    ident_of_string
      (sprintf "%s_%s" (ident_to_string lid) (ident_to_string fname))
  in
  let gen_array_elem_loc_id lid =
    ident_of_string (sprintf "%s_elem" (ident_to_string lid))
  in
  let gen_param_loc_id pid =
    ident_of_string (sprintf "l%s" (ident_to_string pid))
  in
  let rec gen_val_mem_layout (lid : absloc) (t : ctyp) : absmem =
    match t with
    | CBool | CInt32 _ | CInt64 _ -> mem_empty
    | CArray ta -> gen_array_mem_layout lid ta
    | CStruct ts -> gen_struct_mem_layout lid ts
    | _ -> raise unsupported
  and gen_array_mem_layout lid ta =
    if is_prim ta then mem_empty
    else
      let lid' = gen_array_elem_loc_id lid in
      let mem = gen_val_mem_layout lid' ta in
      IdentPairMap.add (lid, _INDEX) (IdentSet.singleton lid') mem
  and gen_struct_mem_layout lid sid =
    match senv_get se sid with
    | Errors.OK fields ->
        List.fold_left
          (fun acc (fname, ftyp) ->
            if is_prim ftyp then acc
            else
              let lid' = gen_field_loc_id lid fname in
              let mem = gen_val_mem_layout lid' ftyp in
              let mem' =
                IdentPairMap.add (lid, fname) (IdentSet.singleton lid') mem
              in
              mem_union mem' acc)
          mem_empty
          fields
    | Errors.Error _ -> mem_empty
  in
  let ev =
    List.fold_left
      (fun acc (pid, ptyp) ->
        match ptyp with
        | CStruct _ | CArray _ ->
            IdentMap.add pid (IdentSet.singleton (gen_param_loc_id pid)) acc
        | _ -> if is_prim ptyp then acc else raise unsupported)
      env_empty
      params
  in
  let m =
    List.fold_left
      (fun acc (pid, ptyp) ->
        let lid = gen_param_loc_id pid in
        let m = gen_val_mem_layout lid ptyp in
        mem_union m acc)
      mem_empty
      params
  in
  make_state2 ev m set_empty

(** [is_param v params] checks wether the variable [v] is contained in the
    parameter list [params]. *)
let is_param (v : ident) (params : (ident * ctyp) list) : bool =
  List.exists (fun (pid, _) -> v = pid) params

let build_return_state (st : absstate) (params : (ident * ctyp) list) : absstate
    =
  let streturn = proj_state st (IdentSet.of_list (List.map fst params)) in
  { streturn with st_arr_locked = IdentMap.empty }

(** [gen_fun_descr _ ts fe f] generates the function descriptor for [f]. *)
let gen_fun_descr_and_ast (show_debug : bool) (se : senv) (fe : fenv)
    (f : coq_function) : fun_descr * Imp1.Aliasing_AST.statement =
  let callstate = gen_valid_call_state se f.fn_params in
  let ast, returnstate =
    absexec show_debug se fe (AbsState callstate) f.fn_body
  in
  (* We filter the returned environment and set of invalid paths to only keep the bindings
     for which the key is a function paramater. *)
  let returnstate =
    let* retstate = returnstate in
    (* let ev_ret =
      IdentMap.filter (fun v _ -> is_param v f.fn_params) retstate.st_env
    in
    let rev_ret = env_reverse ev_ret in
    let inv_ret =
      IdentMap.filter (fun v _ -> is_param v f.fn_params) retstate.st_inv
    in *)
    (* Arrays are treated linearly when used in a function call so we invalidate all parameters
       which type is array, if the returned value is not primivite.
       Thus, if a function returns a (non-primitive) sub element of an array, the array will be
        unusable after the function call. *)
    (* let all_array_params =
      List.fold_right
        (fun (fid, ftyp) acc ->
          match ftyp with
          | CArray _ -> fid :: acc
          | _ -> acc)
        f.fn_params
        []
    in *)
    (* let inv_ret =
      if is_prim f.fn_return then inv_ret
      else
        List.fold_left
          (fun acc a -> IdentMap.add a Leaf acc)
          inv_ret
          all_array_params
    in *)
    (* AbsState
      { retstate with st_env = ev_ret; st_rev_env = rev_ret; st_inv = inv_ret } *)
    AbsState (build_return_state retstate f.fn_params)
  in
  let fdescr =
    {
      fd_params = f.fn_params;
      fd_callstate = callstate;
      fd_returnstate = returnstate;
    }
  in
  (match fdescr.fd_returnstate with
  | AbsState st ->
      debug_info show_debug
      @@ sprintf "INV_RET: %s\n" (paths_to_string st.st_inv)
  | Top -> debug_info show_debug @@ sprintf "INV_RET: Top\n");
  (fdescr, ast)

let senv_from_struct_defs (l : struct_def list) : senv =
  List.fold_left
    (fun acc st -> Utils.tset acc st.sd_name st.sd_fields)
    Maps.PTree.empty
    l

(** [get_fun_descr p fname] returns the function descriptor of [fname] if a
    function is defined with this name in the program [p]. *)
let get_fun_descr (p : program) (fname : string) : fun_descr option =
  let fid = ident_of_string fname in
  let rec aux fe defs =
    match defs with
    | [] -> None
    | DefFun (x, f) :: defs' ->
        let se = senv_from_struct_defs p.prog_types in
        let fdescr, _ = gen_fun_descr_and_ast false se fe f in
        if x = fid then Some fdescr else aux (IdentMap.add x fdescr fe) defs'
    | _ :: defs' -> aux fe defs'
  in
  aux IdentMap.empty p.prog_defs

(** [gen_aliasing_function ts fe f] generates the AST corresponding to the
    function [f] with the aliasing information. *)
let gen_aliasing_function (show_debug : bool) (se : senv) (fe : fenv)
    (x : ident) (f : Imp1Typed.coq_function) :
    (Imp1.Aliasing_AST.coq_function * fenv) option =
  let stcall = gen_valid_call_state se f.fn_params in
  let args = List.map (fun (v, ty) -> Syntax.Typed.AVar (v, ty)) f.fn_params in
  assert (args_pointsto_unique stcall args);
  assert (wf_args stcall args);
  let fdescr, body' = gen_fun_descr_and_ast show_debug se fe f in
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
let gen_aliasing_globdef (se : senv) (fe : fenv) (def : Imp1Typed.globdef)
    (show_debug : bool) : (Imp1.Aliasing_AST.globdef * fenv) option =
  match def with
  | DefFun (x, f) ->
      debug_info show_debug
      @@ sprintf "Analysing function %s...\n\n" (ident_to_string x);
      let r =
        match gen_aliasing_function show_debug se fe x f with
        | Some (f', fe') -> Some (DefFun (x, f'), fe')
        | None -> None
      in
      debug_info show_debug
      @@ sprintf "\nAnalysis of function %s finished.\n\n" (ident_to_string x);
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
        let se = senv_from_struct_defs prog.prog_types in
        match gen_aliasing_globdef se fe d show_debug with
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
