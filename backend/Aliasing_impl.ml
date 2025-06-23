open Printf
open BinPosDef
open Types
open Syntax
open Syntax.Typed
open Typing
open Imp1
open Imp1Typed
open Aliasing_defs
open Aliasing_defs.PathTree
open Aliasing_defs.AbsDom
open PrintCommon

let top (msg : string) = Top (mk_err_info msg)

exception UnsupportedFeature of string

let unsupported =
  UnsupportedFeature
    "function pointers are not handled by the alias analysis yet"

let debug_info (b : bool) (s : string) : unit = if b then eprintf "%s" s else ()

let ( let* ) = AbsDom.dbind

(** [absloc_to_string l] converts an abstract location to a string. *)
let absloc_to_string (l : absloc) : string =
  ident_to_string (Ident.concat (ident_of_string "l") (Ident.of_str_pos l))

(** [paths_to_string paths] transforms an invalid path map into a string. *)
let paths_to_string (paths : path_map) : string =
  list_to_string_bracket
    (fun (x, t) -> sprintf "%s.%s" (ident_to_string x) (PathTree.to_string t))
    (List.of_seq (IdentMap.to_seq paths))

(** [is_prim ty] checks wether a value of type [ty] is primitive (i.e. it's a
    boolean or integer value). *)
let is_prim (ty : btyp) : bool =
  match ty with
  | BBool | BInt32 _ | BInt64 _ -> true
  | BFun (_, _) -> raise unsupported
  | _ -> false

(** [is_array ty] checks wether a value of type [ty] is an array. *)
let is_array (ty : btyp) : bool =
  match ty with
  | BArray _ -> true
  | BFun (_, _) -> raise unsupported
  | _ -> false

(** [inv_paths_to_loc_rec rev rm curr p paths] retrieves all the paths leading
    to the location [curr] given the reverse environment [rev] and reverse
    memory [rm], and stores them into a map of invalid paths.
    - [p] is an accumulator which contains the current path being explored.
    - [paths] is an accumulator which contains the path map computed until now.
*)
let rec inv_paths_to_loc_rec (rev : rev_absenv) (rm : rev_absmem)
    (curr : absloc) (p : path) (paths : path_map) : path_map =
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
            (fun n accS -> inv_paths_to_loc_rec rev rm n (f :: p) accS)
            lf
            accL)
        paths'
        adj
  | None -> paths'

(** [inv_paths_to_loc st loc] computes the map of all paths leading to the
    location [loc] in [st]. *)
let inv_paths_to_loc (st : absstate) (loc : absloc) : path_map =
  inv_paths_to_loc_rec st.st_rev_env st.st_rev_mem loc [] IdentMap.empty

(** [inv_paths_to_loc_suffixed st loc suffix] computes the map of all paths
    leading to the location [loc] in [st] and suffixes them with [suffix]. *)
let inv_paths_to_loc_suffixed (st : absstate) (loc : absloc) (suffix : path) :
    path_map =
  inv_paths_to_loc_rec st.st_rev_env st.st_rev_mem loc suffix IdentMap.empty

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
let vars_aliased_to_loc (rev : rev_absenv) (loc : absloc) : var_set =
  match IdentMap.find_opt loc rev with
  | Some vars -> vars
  | None -> set_empty

(** [vars_aliased_to_locs rev locs] returns the variable set that may point to
    at least one location belonging to [locs]. *)
let vars_aliased_to_locs (rev : rev_absenv) (locs : pointsto_set) : var_set =
  IdentSet.fold
    (fun li acc -> IdentSet.union (vars_aliased_to_loc rev li) acc)
    locs
    set_empty

(** [exec_set_struct_proj x a f ty st] computes the transfer function for the
    statement [set x := a.f] on [st]. [ty] is the type of the field [f] in the
    struct [a]. *)
let exec_set_struct_proj (x : ident) (a : atom) (f : ident) (ty : btyp)
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

(** [exec_set_struct_update  x a f v st] computes the transfer function for the
    statement [set x := y.f <- v] on [st]. *)
let exec_set_struct_update (se : senv) (x : ident) (a : atom) (f : ident)
    (v : atom) (st : absstate) : absstate =
  match a with
  | AVar (y, BStruct sy) ->
      let ly = IdentMap.find y st.st_env in
      (* All paths leading to all locations pointed by y, suffixed by f, are now invalid. *)
      let inv' =
        IdentSet.fold
          (fun l acc ->
            let l_inv = inv_paths_to_loc_suffixed st l [f] in
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
              (* If v is not primitive, we update the memory. *)
              let lv = IdentMap.find v st.st_env in
              IdentSet.fold (fun l acc -> mem_weak_update acc (l, f) lv) ly st
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

(** [exec_set_array_get x a i st] executes the transfer function for the
    statement [set x := a[i]] on [st]. If an element of the array [a] has
    already been accessed before, then accessing [a[i]] is forbidden. *)
let exec_set_array_get (x : ident) (a : atom) (i : atom) (st : absstate) :
    absdom =
  match a with
  | AVar (y, BArray ty) ->
      let ly = IdentMap.find y st.st_env in
      (* All locations in ly should be free. *)
      let all_free =
        IdentSet.for_all
          (fun l -> IdentMap.find_opt l st.st_arr_locked = None)
          ly
      in
      if all_free then
        let yi_inv = invalid_paths_with_prefix st.st_inv y [_CONTENT] in
        let st' =
          if is_prim ty then st
          else
            let ly = IdentMap.find y st.st_env in
            let ly_i =
              IdentSet.fold
                (fun l acc ->
                  IdentSet.union acc (AbsDom.mem_get st.st_mem l _CONTENT))
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
      else top "impossible array get, the array is not free"
  | _ -> assert false

(** [exec_set_array_set x a i v st] executes the transfer function for the
    statement [set x := a[i] <- v] on [st]. *)
let exec_set_array_set (x : ident) (a : atom) (i : atom) (v : atom)
    (st : absstate) : absdom =
  match a with
  | AVar (y, BArray ty) ->
      let ly = IdentMap.find y st.st_env in
      (* All paths leading to all locations pointed by y, suffixed by [], are now invalid. *)
      let inv' =
        IdentSet.fold
          (fun l acc ->
            let l_inv = inv_paths_to_loc_suffixed st l [_CONTENT] in
            inv_union l_inv acc)
          ly
          st.st_inv
      in
      (* If variable shadowing occurs, and a had invalid paths, then removes them. *)
      let inv' = IdentMap.remove x inv' in
      let v_inv =
        match invalid_paths_of_atom st.st_inv v with
        | Some t -> Some (Node [(_CONTENT, t)])
        | None -> None
      in
      let y_inv = invalid_paths_with_prefix st.st_inv y [] in
      let x_inv =
        (*  If the array y is completely invalid (i.e. y_inv is y or y.[]), x also becomes invalid.
            If the array y contains invalid paths (i.e. there are invalid paths of the form
            y.[].SOMEHTING), then it means that a non-primitive sub-element of the array has been modified,
            this element should be at index i (MUST BE WELL-TESTED!), so setting y[i] should
            not create invalid paths for x, modulo invalid paths from the value v we set in y[i]. *)
        match (v_inv, y_inv) with
        | _, Some (Leaf | Node []) -> Some Leaf
        | _, Some (Node [(_CONTENT, (Leaf | Node []))]) ->
            Some (Node [(_CONTENT, Leaf)])
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
                (* Update the locations pointed by x[]. *)
                IdentSet.fold
                  (fun l acc -> mem_weak_update acc (l, _CONTENT) lv)
                  ly
                  st
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
                  vars_aliased_to_locs st.st_rev_env lyv
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
      else
        top
          "impossible array set, the array is not free of locked on the right \
           index"
  | _ -> assert false

(** [exec_set_deep_access x a acs ty st] executes the transfer function for the
    statement [set x := a acs] on [st]. [ty] is the type of the value returned
    by the deep access. *)
let exec_set_deep_access (x : ident) (a : atom) (acs : access list) (ty : btyp)
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
(* let is_arg (v : ident) (args : atom list) : bool =
  List.exists
    (fun a ->
      match a with
      | Syntax.Typed.AVar (x, _) -> if x = v then true else false
      | _ -> false)
    args *)

(** [pointsto_unique st x] checks wether the variable [x] points to only one
    abstract location in [st]. *)
let pointsto_unique (st : absstate) (x : ident) : bool =
  match IdentMap.find_opt x st.st_env with
  | Some locs -> IdentSet.cardinal locs = 1
  | None -> true

(** [vars_of_atom a] returns the set of variables contained in [a]. *)
let rec vars_of_atom (a : atom) : IdentSet.t =
  match a with
  | AVar (x, _) -> IdentSet.singleton x
  | AUnaryOp (_, a1, _) -> vars_of_atom a1
  | ABinaryOp (_, a1, a2, _) ->
      IdentSet.union (vars_of_atom a1) (vars_of_atom a2)
  | _ -> set_empty

(** [args_points_unique st args] checks wether each function argument belonging
    to [args] points to only one abstract location in [st]. *)
let args_pointsto_unique (st : absstate) (args : atom list) : bool =
  List.for_all
    (fun (a : atom) -> IdentSet.for_all (pointsto_unique st) (vars_of_atom a))
    args

(** [is_tree_loc_aux m curr visited] checks that the memory region reachable
    from the location [curr] is a tree, given the already visited locations
    [visited]. *)
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

(** [is_tree_locs_aux m (b, vis) locs] checks that the memory region reachable
    from the location [locs] is a multi-rooted tree, given that the
    alread-explored memory region composed of the locations [vis] is itself a
    tree or not (according to [b]). *)
and is_tree_locs_aux (m : absmem) ((b, vis) : bool * IdentSet.t)
    (locs : absloc list) : bool * IdentSet.t =
  match locs with
  | [] -> (b, vis)
  | l :: locs' ->
      let b', vis' = is_tree_loc_aux m l vis in
      let visu = IdentSet.union vis vis' in
      if b' then is_tree_locs_aux m (b', visu) locs' else (false, visu)

(** [is_tree_loc m curr visited] checks wether the memory layout of [m] is a
    tree starting from [root] and given the already visited nodes [visited]. *)
let is_tree_loc (m : absmem) (root : absloc) (visited : IdentSet.t) : bool =
  fst (is_tree_loc_aux m root visited)

(** [is_tree_locs m locs] checks wether the memory layout of [m] is a
    multi-rooted tree starting from the locations [roots]. *)
let is_tree_locs (m : absmem) (roots : ident list) : bool =
  fst (is_tree_locs_aux m (true, set_empty) roots)

(** [is_tree_var st x] checks wether the memory layout in [st] is a tree
    starting from the variable [x]. *)
let is_tree_var (st : absstate) (x : ident) : bool =
  match IdentMap.find_opt x st.st_env with
  | Some locs -> is_tree_locs st.st_mem (IdentSet.elements locs)
  | None -> false

(** [wf_args st args] checks that all arguments [args] are well-formed at
    function call, i.e. that each non-primitive arguments point to trees and
    that there is not inter-aliasing between arguments. *)
let wf_args (st : absstate) (args : atom list) : bool =
  let arg_roots =
    List.fold_left
      (fun acc (a : atom) ->
        if btyp_is_prim (typof_atom a) then acc
        else List.append (IdentSet.elements (vars_of_atom a)) acc)
      []
      args
  in
  is_tree_locs st.st_mem arg_roots

let rec aliased_paths_rec (m : absmem) (rev : rev_absenv) (rm : rev_absmem)
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

(** [aliased_path st x p] returns the map of paths aliased with [x.p] in [st].
*)
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

(** [sub_aliases_of_loc_aux st root visited] returns the map of paths aliased
    with sub-elements of the location [root] in the state [st]. [visited] are
    the already visited locations. *)
let rec sub_aliases_of_loc_aux (st : absstate) (root : absloc)
    (visited : IdentSet.t) : path_map * IdentSet.t =
  if IdentSet.mem root visited then (IdentMap.empty, visited)
  else
    let vars = vars_aliased_to_loc st.st_rev_env root in
    let iv =
      IdentSet.fold
        (fun v iv ->
          let v_inv = aliased_paths st v [] in
          inv_union iv v_inv)
        vars
        IdentMap.empty
    in
    let adjacents =
      IdentPairMap.fold
        (fun (l, f) locs acc ->
          if l = root then List.append (IdentSet.elements locs) acc else acc)
        st.st_mem
        []
    in
    let iv', visited' = sub_aliases_of_locs_aux st adjacents visited in
    let visited' = IdentSet.add root visited' in
    (inv_union iv iv', visited')

(** [sub_aliases_of_locs_aux rev m roots visited] returns the map of paths
    aliased with the sub-elements of the locations contained in [roots] given
    the state [st] and already visited locations [visited]. *)
and sub_aliases_of_locs_aux (st : absstate) (roots : absloc list)
    (visited : IdentSet.t) : path_map * IdentSet.t =
  List.fold_left
    (fun (iv, visited) root ->
      let iv', visited' = sub_aliases_of_loc_aux st root visited in
      (inv_union iv iv', visited'))
    (IdentMap.empty, visited)
    roots

(** [sub_aliases_of_loc st loc] returns the map of paths aliased with the
    sub-elements of the location [loc] in [st]. *)
let sub_aliases_of_loc (st : absstate) (loc : absloc) : path_map =
  fst (sub_aliases_of_loc_aux st loc set_empty)

(** [sub_aliases_of_locs st locs] returns the map of paths aliased with the
    sub-elements of the locations contained in [locs] given [st]. *)
let sub_aliases_of_locs (st : absstate) (locs : pointsto_set) : path_map =
  fst (sub_aliases_of_locs_aux st (IdentSet.elements locs) set_empty)

(** [follow_path_from_loc m p root] returns the set of locations reachable from
    [root] via [p] in the memory [m]. *)
let rec follow_path_from_loc (m : absmem) (p : path) (root : absloc) :
    pointsto_set =
  match p with
  | [] -> IdentSet.singleton root
  | f :: [] -> mem_get m root f
  | f :: p' ->
      let adjacents = mem_get m root f in
      IdentSet.fold
        (fun l acc -> IdentSet.union (follow_path_from_loc m p' l) acc)
        adjacents
        set_empty

(** [follow_path_from_var ev m v p] returns the set of locations reachable from
    [v] via [p] in the memory [m] and environment [ev]. *)
let follow_path_from_var (ev : absenv) (m : absmem) (v : ident) (p : path) :
    pointsto_set =
  match IdentMap.find_opt v ev with
  | Some locs ->
      IdentSet.fold
        (fun l acc -> IdentSet.union (follow_path_from_loc m p l) acc)
        locs
        set_empty
  | None -> set_empty

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

(** [mem_bijection se edges loc1 loc2 m1 m2 bij] computes the bijection between
    the memories [m1] and [m2], starting at locations [loc1] in [m1] and [loc2]
    in [m2]. [se] is the struct type environment, [edges] is a list of typed
    edges that should go out [loc1] and [loc2]. [bij] is an accumulator storing
    the bijection computed until now. *)
let rec mem_bijection (se : senv) (edges : (ident * btyp) list) (loc1 : absloc)
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
            | BStruct sid -> begin
                match senv_get se sid with
                | Errors.OK fields -> fields
                | Errors.Error _ -> assert false
              end
            | BArray ta -> [(_CONTENT, ta)]
            | BAbs _ -> []
            | _ -> assert false
          in
          let bij' =
            mem_bijection se edges_e lv1 lv2 m1 m2 (IdentMap.add lv1 lv2 bij)
          in
          mem_bijection se edges' loc1 loc2 m1 m2 bij'
        else assert false

(** [locs_bijection se v1 v2 ty st1 st2] computes the bijection between all
    locations contained in [st1] and [st2], starting from the variables [v1] of
    [st1] and [v2] of [st2]. [se] is the struct type environment. [ty] is the
    type of the variables. *)
let locs_bijection (se : senv) (v1 : ident) (v2 : ident) (ty : btyp)
    (st1 : absstate) (st2 : absstate) : ident IdentMap.t =
  let l1 = IdentMap.find v1 st1.st_env in
  let l2 = IdentMap.find v2 st2.st_env in
  if IdentSet.cardinal l1 = 1 && IdentSet.cardinal l2 = 1 then
    let lv1 = IdentSet.choose l1 in
    let lv2 = IdentSet.choose l2 in
    let edges =
      match ty with
      | BStruct sid -> begin
          match senv_get se sid with
          | Errors.OK fields -> fields
          | Errors.Error _ -> assert false
        end
      | BArray ta -> [(_CONTENT, ta)]
      | BAbs _ -> []
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
  else assert false

(** [funcall_bijection se args params stcallee stcaller] computes the bijection
    between the state of the callee and the state of the caller. It returns a
    map which associate each paramater in [params] to its corresponding argument
    in [args], and associated each location of [stcallee] to its corresponding
    location in [stcaller]. [se] is the struct type environment. *)
let funcall_bijection (show_debug : bool) (se : senv)
    (params : (ident * btyp) list) (args : atom list) (stcallee : absstate)
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
          (fun _ l1 l2 -> if l1 <> l2 then assert false else Some l1)
          (locs_bijection se v (IdentMap.find v vars_bij) ty stcallee stcaller)
          acc)
      IdentMap.empty
      (List.fold_right
         (fun (id, ty) acc -> if is_prim ty then acc else (id, ty) :: acc)
         params
         [])
  in
  debug_info show_debug
  @@ sprintf
       "Vars bij: %s\n"
       (list_to_string_braces
          (fun (v1, v2) ->
            sprintf "%s -> %s" (ident_to_string v1) (ident_to_string v2))
          (IdentMap.to_seq vars_bij |> List.of_seq));

  debug_info show_debug
  @@ sprintf
       "Locs bij: %s\n"
       (list_to_string_braces
          (fun (l1, l2) ->
            sprintf "%s -> %s" (absloc_to_string l1) (absloc_to_string l2))
          (IdentMap.to_seq locs_bij |> List.of_seq));
  (vars_bij, locs_bij)

(** [apply_ident_bijection bij] return the bijection of [x] stored in [bij]. If
    it does not exist, it returns [x] itself. *)
let apply_ident_bijection (bij : ident IdentMap.t) (x : ident) : ident =
  match IdentMap.find_opt x bij with
  | Some x' -> x'
  | None -> x

(** [apply_state_bijection vars_bij locs_bij st] replaces each variable and
    location of [st] by its corresponding value given in the bijections
    [vars_bij] and [locs_bij]. *)
let apply_state_bijection (vars_bij : ident IdentMap.t)
    (locs_bij : ident IdentMap.t) (next_loc : ident) (st : absstate) : absstate
    =
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
  make_state ev m rev rm res inv inv_res IdentMap.empty next_loc

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

(** [proj_state_aux st vars locs] builds the projection of [st] on the variables
    [vars] and the abstract locations [locs]. *)
let proj_state_aux (st : absstate) (vars : var_set) (locs : pointsto_set) :
    absstate =
  (* The environment is projected on the variables *)
  let ev = IdentMap.filter (fun k _ -> IdentSet.mem k vars) st.st_env in
  let rev = env_reverse ev in
  (* The invalid path environment is projected on the variables *)
  let iv = IdentMap.filter (fun k _ -> IdentSet.mem k vars) st.st_inv in
  let iv_res = st.st_inv_res in
  (* To build the memory projection, we make a DFS from all the locations pointed by
     the variables. *)
  let roots =
    let roots_of_vars =
      IdentMap.fold (fun _ locs roots -> IdentSet.union locs roots) ev set_empty
    in
    IdentSet.union locs roots_of_vars
  in
  let m, visited =
    IdentSet.fold
      (fun root (m, visited) -> proj_mem st.st_mem root m visited)
      roots
      (IdentPairMap.empty, set_empty)
  in
  let rm = mem_reverse m in
  (* The locked arrays environment is projected on all locations contained
     in the projection of the memory. *)
  let arr_locked =
    IdentMap.filter (fun k _ -> IdentSet.mem k visited) st.st_arr_locked
  in
  (* The set of returned locations is projected on all locations contained
     in the projection of the memory. *)
  let res = IdentSet.filter (fun r -> IdentSet.mem r visited) st.st_res in
  let next_loc = st.st_next_loc in
  make_state ev m rev rm res iv iv_res arr_locked next_loc

(** [proj_state st vars] builds the projection of [st] on the variables [vars].
*)
let proj_state st vars = proj_state_aux st vars set_empty

(** [build_call_state st args] build the state for a function call with
    arguments [args] from [st]. *)
let build_call_state (st : absstate) (args : atom list) : absstate =
  let vars =
    List.fold_left
      (fun acc a -> IdentSet.union (vars_of_atom a) acc)
      set_empty
      args
  in
  let stcall = proj_state st vars in
  { stcall with st_res = set_empty }

(** [exec_set_call x a args ty fe st nctr] computes the transfer function for
    the statement [set x = a (args)] on [st]. [fe] is the function descriptor
    environment. [ty] is the type of the return value. *)
let exec_set_call (show_debug : bool) (se : senv) (x : ident) (a : atom)
    (args : atom list) (ty : btyp) (fe : fenv) (st : absstate) : absdom =
  match a with
  | AVar (y, _) ->
      let fd_params, fd_callstate, fd_returnstate =
        match IdentMap.find_opt y fe with
        | Some fdescr ->
            (fdescr.fd_params, fdescr.fd_callstate, fdescr.fd_returnstate)
        | None -> raise unsupported
      in
      let* fd_returnstate = fd_returnstate in

      let stcall = build_call_state st args in

      (* Before calling the function, we must check the following things: 
            - All arguments are completely valid;
            - Each non-primitive argument points to only one abstract location;
            - Each argument points to a tree-shaped part of the memory;
            - There is no inter-aliasing between arguments
            - There is no locked arrays passed as arguments. *)
      let args_validity =
        List.for_all (Aliasing_check.check_atom (AbsState stcall)) args
      in
      let no_locked_arrays = IdentMap.is_empty stcall.st_arr_locked in
      let errmsg cause =
        sprintf "when calling function %s: %s" (ident_to_string y) cause
      in
      if not (args_pointsto_unique stcall args) then
        top (errmsg "some arguments point to multiple location")
      else if not no_locked_arrays then
        top (errmsg "some arguments contain locked arrays")
      else if not (wf_args stcall args) then
        top (errmsg "intra- or inter-argument aliasing")
      else if not args_validity then top (errmsg "some arguments are not valid")
      else
        (* We build the bijections for the variables and the locations between the current call state,
            and the pre-requisite call state of the callee. *)
        let vars_bij, locs_bij =
          funcall_bijection show_debug se fd_params args fd_callstate stcall
        in

        (* The return state is the one given by the function descriptor on which we apply the bijection. *)
        let stret =
          apply_state_bijection vars_bij locs_bij st.st_next_loc fd_returnstate
        in
        (* The state before the call "st" and the return state "stret" must be merged.
             The merge operation is the following:
             - The new environment is the one of the inital state + the new binding for x that points to
               the result locations of the return state (stret.st_res). 
               As function parameters are renamed by the frontend, we never assign an argument to another value.
               So for every key "v" in stret.st_env, s.t. "v" was an argument, the points-to set of "v" is the same
               in stret.st_env and st.st_env.
             - If a pair (l, f) is a key of the return state memory, it means that it was accessible from the arguments
                (and it's also contained in st).
                We just keep the value associated with (l, f) from this return state in the new memory.
             - If a pair (l, f) is NOT a key of the return state memory,
               then we keep the value associated with (l, f) from the initial state.
             - The invalid paths of the resulting state will contain:
               + The invalid paths of the initial state;
               + The invalid paths of the return state;
               + The paths that were aliased with some arguments that themselves contained invalid paths when the function returns.
             - The locked arrays are the one of the initial state.
             - The next fresh location is the one of the initial state. *)
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
          let iv_args_alias =
            let iv_args = aliased_paths_of_pmap st stret.st_inv in
            (* We gather all of the locations pointed by the paths in iv_args *)
            let locs =
              IdentMap.fold
                (fun v t accM ->
                  let paths = PathTree.flatten t in
                  List.fold_left
                    (fun accL p ->
                      IdentSet.union
                        accL
                        (follow_path_from_var st.st_env st.st_mem v p))
                    accM
                    paths)
                iv_args
                set_empty
            in
            (* We invalidate all paths aliased with sub-elements of the
              invalid paths returned by the return state. *)
            let iv_sub = sub_aliases_of_locs st locs in
            let iv_args = inv_union iv_sub iv_args in
            (* If variable shadowing occurs, we must remove the binding of x in the map of invalid paths. *)
            IdentMap.remove x iv_args
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
        let arr_locked_ret = st.st_arr_locked in
        let next_loc = st.st_next_loc in
        AbsState
          {
            st' with
            st_mem = m_ret;
            st_rev_mem = rm_ret;
            st_inv = inv_ret;
            st_inv_res = inv_res_ret;
            st_arr_locked = arr_locked_ret;
            st_next_loc = next_loc;
          }
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
          match List.assoc_opt _CONTENT parent_assoc_list with
          | Some locs -> locs
          | _ -> set_empty
        in
        IdentSet.union acc parent_arrays)
      st.st_res
      set_empty
  in
  (* Compute the invalid paths from the parent arrays. *)
  let inv =
    IdentSet.fold
      (fun loc accS ->
        let paths = inv_paths_to_loc st loc in
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
     because otherwise we lose the track of the source of the element.
     This makes the corresponding arrays unsuable after the function call and prevents
     the user from writing programs that would make sharing in arrays possible
     by getting an array element via a function call. *)
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
        (PrintSyntax.Typed.atom_to_string a))
    (List.of_seq (IdentMap.to_seq arr_locked_var))

let print_dom_debug (show_debug : bool) (d : absdom) (suffix : string)
    (inv_res : bool) : unit =
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
        if inv_res then
          match st.st_inv_res with
          | Some t ->
              debug_info show_debug
              @@ sprintf "INV_RES: %s\n" (PathTree.to_string t)
          | None -> debug_info show_debug "INV_RES: None\n"
        else ()
      end
  | Top _ -> debug_info show_debug @@ sprintf "DOM_%s: Top\n" suffix);
  if suffix = "OUT" then debug_info show_debug "\n"

let update_err_stmt (stmt : Imp1Typed.statement) (err : err_info) : err_info =
  match stmt with
  | StIfThenElse _ | StSequence _ -> err
  | _ ->
      if err.ei_stmt = None then
        mk_err_info_with_stmt
          (PrintImp1.Typed.statement_to_string_pref "" stmt)
          err.ei_msg
      else err

(** [absexec se fe ce d s] computes the transfer function for the statement [s]
    on [d]. [fe] is the function descriptor environement. [se] is the struct
    types environment. *)
let rec absexec (show_debug : bool) (se : senv) (fe : fenv) (d : absdom)
    (s : Imp1Typed.statement) : Imp1.Aliasing_AST.statement * absdom =
  let d_in = d in
  let s', d_out =
    match s with
    | StSet (x, c) ->
        (* We check that no shadowing occurs on a variable used for an array access. *)
        print_dom_debug show_debug d_in "IN" false;
        let d' =
          let* st = d in
          let all_vars_in_array_get =
            IdentMap.fold
              (fun _ a acc -> IdentSet.union (vars_of_atom a) acc)
              st.st_arr_locked
              set_empty
          in
          if IdentSet.mem x all_vars_in_array_get then
            top
              "shadowing of variables used to access array elements is \
               forbidden"
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
                     (PrintSyntax.Typed.comp_to_string c);
                let r = exec_set_call show_debug se x a args ty fe st in
                debug_info show_debug
                @@ sprintf
                     "Exiting function call \"%s\" ===========\n"
                     (PrintSyntax.Typed.comp_to_string c);
                r
            | CpArrayGet (a, i, _) -> exec_set_array_get x a i st
            | CpArraySet (a, i, v, _) -> exec_set_array_set x a i v st
            | CpDeepAccess (a, acs, ty) ->
                AbsState (exec_set_deep_access x a acs ty st)
        in
        let s', d' = (Imp1.Aliasing_AST.StSet (x, c, d_in, d'), d') in
        debug_info show_debug
        @@ sprintf ">> %s\n" (PrintImp1.Typed.statement_to_string_pref "" s);
        print_dom_debug show_debug d' "OUT" false;
        (s', d')
    | StIfThenElse (a, s1, s2) ->
        print_dom_debug show_debug d_in "IN" false;
        debug_info show_debug
        @@ sprintf
             ">> Entering if-then-else \"if %s\" ======================\n"
             (PrintSyntax.Typed.atom_to_string a);
        let s1', d1 = absexec show_debug se fe d s1 in
        let s2', d2 = absexec show_debug se fe d s2 in
        let d_out =
          match AbsDom.union d1 d2 with
          | Top err -> Top err
          | _ as d' -> d'
        in
        debug_info show_debug
        @@ sprintf
             ">> Exiting if-then-else \"if %s\", joint point ==========\n"
             (PrintSyntax.Typed.atom_to_string a);
        print_dom_debug show_debug d_out "OUT" true;
        (Imp1.Aliasing_AST.StIfThenElse (a, s1', s2', d_in, d_out), d_out)
    | StSequence (s1, s2) ->
        let s1', d1 = absexec show_debug se fe d s1 in
        let s2', d2 = absexec show_debug se fe d1 s2 in
        (Imp1.Aliasing_AST.StSequence (s1', s2'), d2)
    | StReturn a ->
        print_dom_debug show_debug d "IN" false;
        debug_info show_debug
        @@ sprintf ">> %s\n" (PrintImp1.Typed.statement_to_string_pref "" s);
        let d' =
          let* st = d in
          let st' = exec_return a st in
          if is_tree_locs st'.st_mem (IdentSet.elements st.st_res) then
            AbsState st'
          else top "ill-formed return value"
        in
        let s', d' = (Imp1.Aliasing_AST.StReturn (a, d, d'), d') in
        print_dom_debug show_debug d' "OUT" true;
        (s', d')
  in
  let d_out =
    match d_out with
    | Top err -> Top (update_err_stmt s err)
    | _ -> d_out
  in
  (s', d_out)

let fresh_loc (l : absloc) : absloc = Pos.add BinNums.Coq_xH l

(** [add_memory_object_aux se st ty] adds a new memory object reflecting type
    [ty] in [st] and attached it to root [root]. [se] is the struct type
    environment. *)
let add_memory_object_aux (se : senv) (st : absstate) (root : absloc)
    (ty : btyp) : absstate =
  let next_loc = ref st.st_next_loc in
  let fresh_loc () =
    let r = !next_loc in
    next_loc := fresh_loc !next_loc;
    r
  in
  let rec gen_val_mem_layout (m : absmem) (root : absloc) (ty : btyp) : absmem =
    match ty with
    | BBool | BInt32 _ | BInt64 _ | BAbs _ -> m
    | BArray ta -> gen_array_mem_layout m root ta
    | BStruct ts -> gen_struct_mem_layout m root ts
    | _ -> raise unsupported
  and gen_array_mem_layout (m : absmem) (root : absloc) (ta : btyp) : absmem =
    if is_prim ta then m
    else
      let lid = fresh_loc () in
      let m = gen_val_mem_layout m lid ta in
      IdentPairMap.add (root, _CONTENT) (IdentSet.singleton lid) m
  and gen_struct_mem_layout (m : absmem) (root : absloc) (sid : ident) : absmem
      =
    match senv_get se sid with
    | Errors.OK fields ->
        (* Printf.printf "Fields: %s\n" (PrintTypes.structtyp_to_string PrintTypes.btyp_to_string fields); *)
        List.fold_left
          (fun acc (fname, fty) ->
            if is_prim fty then acc
            else
              let lid = fresh_loc () in
              (* Printf.printf "Fresh loc: %s\n" (absloc_to_string lid); *)
              let m = gen_val_mem_layout acc lid fty in
              IdentPairMap.add (root, fname) (IdentSet.singleton lid) m)
          m
          fields
    | Errors.Error _ -> assert false
  in
  let m = gen_val_mem_layout st.st_mem root ty in
  let rm = mem_reverse m in
  { st with st_mem = m; st_rev_mem = rm; st_next_loc = !next_loc }

let add_memory_object (se : senv) (st : absstate) (ty : btyp) : ident * absstate
    =
  let root = st.st_next_loc in
  let st = { st with st_next_loc = fresh_loc st.st_next_loc } in
  (root, add_memory_object_aux se st root ty)

(** [gen_valid_call_state se params] generates a valid call state w.r.t. the
    function parameters [params]. *)
let gen_valid_call_state (se : senv) (params : (ident * btyp) list) : absstate =
  List.fold_left
    (fun st (pid, pty) ->
      if is_prim pty then st
      else
        let root, st' = add_memory_object se st pty in
        env_add st' pid (IdentSet.singleton root))
    (make_state2 IdentMap.empty IdentPairMap.empty)
    params

(** [is_param v params] checks wether the variable [v] is contained in the
    parameter list [params]. *)
let is_param (v : ident) (params : (ident * btyp) list) : bool =
  List.exists (fun (pid, _) -> v = pid) params

(** [build_return_state st params] builds the projection of the return state
    [st] on the function parameters [params]. *)
let build_return_state (st : absstate) (params : (ident * btyp) list) : absstate
    =
  let streturn =
    proj_state_aux st (IdentSet.of_list (List.map fst params)) st.st_res
  in
  { streturn with st_arr_locked = IdentMap.empty }

(** [wf_return_val st] checks that the return value in [st] is well-formed, i.e.
    it has a tree structure. *)
let wf_return_val (st : absstate) : bool =
  is_tree_locs st.st_mem (IdentSet.elements st.st_res)

(** [wf_params st params] check that the parameters [params] of the function are
    well-formed in [st], i.e. each parameter points to a tree and there is no
    inter-aliasing between the parameters. *)
let wf_params (st : absstate) (params : (ident * btyp) list) : bool =
  let param_roots =
    List.fold_left
      (fun roots (pid, pty) ->
        if is_prim pty then roots
        else
          let pid_roots = IdentMap.find pid st.st_env in
          List.append (IdentSet.elements pid_roots) roots)
      []
      params
  in
  is_tree_locs st.st_mem param_roots

(** [params_pointsto_unique st params] checks that each parameter in [params]
    points to a unique location in [st]. *)
let params_pointsto_unique (st : absstate) (params : ident list) : bool =
  List.for_all (pointsto_unique st) params

(** [gen_fun_descr show_debug se fe f] generates the function descriptor for
    [f]. *)
let gen_fun_descr_and_ast (show_debug : bool) (se : senv) (fe : fenv)
    (f : coq_function) : fun_descr * Imp1.Aliasing_AST.statement =
  let callstate = gen_valid_call_state se f.fn_params in
  assert (wf_params callstate f.fn_params);
  assert (params_pointsto_unique callstate (List.map fst f.fn_params));
  let ast, returnstate =
    absexec show_debug se fe (AbsState callstate) f.fn_body
  in
  let returnstate =
    let* retstate = returnstate in
    let retstate = build_return_state retstate f.fn_params in
    (* Well-formedness checks for the resulting memory. *)
    if not (wf_return_val retstate) then
      top "ill-formed return value after complete function analysis"
    else if not (wf_params retstate f.fn_params) then
      top "the return state contains intra- or inter-parameter aliasing"
    else AbsState retstate
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
  | Top _ -> debug_info show_debug @@ sprintf "INV_RET: Top\n");
  (fdescr, ast)

(** [senv_from_struct_defs l] build the struct type environment from the list of
    struct definition [l]. *)
let senv_from_struct_defs (l : struct_def list) : senv =
  List.fold_left
    (fun acc st -> Utils.tset acc st.sd_name st.sd_fields)
    Maps.PTree.empty
    l

(** [gen_asbfun_descr se fe tparams tret] generates the function descriptor for
    abstract function described by [tparams] and [tret]. *)
let gen_absfun_descr (se : senv) (fe : fenv)
    (tparams : (param_attr * btyp) list) (tret : btyp) : fun_descr =
  let gen_param_id pos = ident_of_string (sprintf "p%d" pos) in
  let params1 =
    List.fold_left
      (fun (ctr, params) (attr, pty) ->
        let pid = gen_param_id ctr in
        (ctr + 1, (attr, (pid, pty)) :: params))
      (0, [])
      tparams
    |> snd |> List.rev
  in
  let params = List.map snd params1 in
  let callstate = gen_valid_call_state se params in
  assert (wf_params callstate params);
  assert (params_pointsto_unique callstate (List.map fst params));
  let returnstate =
    let root =
      if is_prim tret then IdentSet.empty
      else
        let wparam, _ = List.assoc AttrWrite params1 in
        IdentMap.find wparam callstate.st_env
    in
    let st = { callstate with st_res = root } in
    let st =
      List.fold_left
        (fun (ctr, st) (attr, pty) ->
          if is_prim pty || attr = AttrReadonly then (ctr + 1, st)
          else
            let st' = inv_add st (gen_param_id ctr) PathTree.Leaf in
            (ctr + 1, st'))
        (0, st)
        tparams
      |> snd
    in
    assert (wf_return_val st);
    AbsState st
  in
  { fd_callstate = callstate; fd_params = params; fd_returnstate = returnstate }

(** [get_fun_descr p fname] returns the function descriptor of [fname] if a
    function is defined or declared with this name in the program [p]. *)
let get_fun_descr (p : program) (fname : string) : fun_descr option =
  let fid = ident_of_string fname in
  let se = senv_from_struct_defs (get_struct_defs p.prog_types) in
  let rec aux fe defs =
    match defs with
    | [] -> None
    | DefFun (x, f) :: defs' ->
        let fdescr, _ = gen_fun_descr_and_ast false se fe f in
        if x = fid then Some fdescr else aux (IdentMap.add x fdescr fe) defs'
    | DeclFun (x, tparams, tret) :: defs' ->
        let fdescr = gen_absfun_descr se fe tparams tret in
        if x = fid then Some fdescr else aux (IdentMap.add x fdescr fe) defs'
    | _ :: defs' -> aux fe defs'
  in
  aux IdentMap.empty p.prog_defs

(** [gen_aliasing_function se fe f] generates the AST corresponding to the
    function [f] with the aliasing information. *)
let gen_aliasing_function (show_debug : bool) (se : senv) (fe : fenv)
    (x : ident) (f : Imp1Typed.coq_function) :
    (Imp1.Aliasing_AST.coq_function * fenv) Errors.res =
  let fdescr, body' = gen_fun_descr_and_ast show_debug se fe f in
  let fe' = IdentMap.add x fdescr fe in
  match fdescr.fd_returnstate with
  | AbsState st' ->
      let f' =
        { fn_return = f.fn_return; fn_params = f.fn_params; fn_body = body' }
      in
      Errors.OK (f', fe')
  | Top err ->
      let stmt_info =
        match err.ei_stmt with
        | Some str -> sprintf ", statement \"%s\"" str
        | None -> ""
      in
      let msg =
        sprintf
          "alias analysis of function %s%s\n> %s"
          (ident_to_string x)
          stmt_info
          err.ei_msg
      in
      Errors.Error (Errors.msg (Camlcoq.coqstring_of_camlstring msg))

(** [gen_aliasing_globdef se fe def] generates the aliasing AST for the global
    definition [def]. It also returns the new function descriptor environment if
    the global def is a function. *)
let gen_aliasing_globdef (se : senv) (fe : fenv) (def : Imp1Typed.globdef)
    (show_debug : bool) : (Imp1.Aliasing_AST.globdef * fenv) Errors.res =
  match def with
  | DefFun (x, f) ->
      debug_info show_debug
      @@ sprintf "Analysing function %s...\n\n" (ident_to_string x);
      let r =
        match gen_aliasing_function show_debug se fe x f with
        | Errors.OK (f', fe') -> Errors.OK (DefFun (x, f'), fe')
        | Errors.Error _ as err -> err
      in
      debug_info show_debug
      @@ sprintf "\nAnalysis of function %s finished.\n\n" (ident_to_string x);
      r
  | DefConst (x, l, ty) -> Errors.OK (DefConst (x, l, ty), fe)
  | DeclConst (x, ty) -> Errors.OK (DeclConst (x, ty), fe)
  | DeclFun (x, tparams, tret) ->
      let fdescr = gen_absfun_descr se fe tparams tret in
      let fe' = IdentMap.add x fdescr fe in
      Errors.OK (DeclFun (x, tparams, tret), fe')

(** [gen_aliasing_program prog] generates the aliasing AST for the whole Imp1
    program [prog]. *)
let gen_aliasing_program (show_debug : bool) (prog : Imp1Typed.program) :
    Imp1.Aliasing_AST.program Errors.res =
  let rec aux fe defs =
    match defs with
    | [] -> Errors.OK []
    | d :: defs' -> begin
        let se = senv_from_struct_defs (get_struct_defs prog.prog_types) in
        match gen_aliasing_globdef se fe d show_debug with
        | Errors.OK (d', fe') -> begin
            match aux fe' defs' with
            | Errors.OK r -> Errors.OK (d' :: r)
            | Errors.Error _ as err -> err
          end
        | Errors.Error _ as err -> err
      end
  in
  match aux IdentMap.empty prog.prog_defs with
  | Errors.OK defs ->
      Errors.OK { prog_types = prog.prog_types; prog_defs = defs }
  | Errors.Error _ as err -> err

module DotExport = struct
  let ident_to_dotstring (id : ident) : string =
    sprintf "\"%s\"" (ident_to_string id)

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
          (list_to_string "{" "}" " " absloc_to_string lp'))
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
          (absloc_to_string l)
          (list_to_string "{" "}" " " absloc_to_string lp')
          (ident_to_string f))
      lm

  let print_rev_env (out : out_channel) (rev : rev_absenv) : unit =
    let lrev = List.of_seq (IdentMap.to_seq rev) in
    let vars =
      IdentSet.elements
        (List.fold_left
           (fun acc s -> IdentSet.union acc s)
           set_empty
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
          (absloc_to_string l)
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
            (absloc_to_string l)
            (list_to_string "{" "}" " " absloc_to_string (IdentSet.elements vs))
            (ident_to_string f))
        vl
    in
    List.iter print_one lrm

  let print_res (out : out_channel) (locs : pointsto_set) : unit =
    if IdentSet.is_empty locs then ()
    else begin
      fprintf out "%s\"res\" [shape=rect; color=red; margin=0.1];\n" indent;
      fprintf
        out
        "%s\"res\" -> %s\n"
        indent
        (list_to_string "{" "}" " " absloc_to_string (IdentSet.elements locs))
    end

  let print_state (out : out_channel) (d : absdom) : unit =
    fprintf
      out
      "digraph memory {\n\
       %sgraph [fontname=\"Heltvica\",dpi=300];node [fontname = \
       \"Heltvica\"];edge [fontname = \"Heltvica\"];\n"
      indent;
    begin
      match d with
      | AbsState st ->
          print_env out st.st_env;
          print_mem out st.st_mem;
          print_res out st.st_res
      | Top _ -> ()
    end;
    fprintf out "}"

  let print_rev_state (out : out_channel) (d : absdom) : unit =
    fprintf out "digraph memory {\n%sgraph [dpi=300];\n" indent;
    begin
      match d with
      | AbsState st ->
          print_rev_env out st.st_rev_env;
          print_rev_mem out st.st_rev_mem
      | Top _ -> ()
    end;
    fprintf out "}"
end
