open BinPosDef
open Syntax
open Types
open PrintCommon

type path = ident list

(** [_CONTENT] is the label given to memory edges whose source is an array (c.f.
    AbsDom). *)
let _CONTENT : ident = ident_of_string "[*]"

let path_to_string (p : path) : string =
  list_to_string
    ~delim:("", "")
    ~sep:""
    (fun f ->
      let fstr = ident_to_string f in
      if f = _CONTENT then fstr else Printf.sprintf ".%s" fstr)
    p

(** [path_of_access_list acs] transforms the access list [acs] into a path. *)
let rec path_of_access_list (acs : Syntax.Typed.access list) : path =
  match acs with
  | [] -> []
  | Syntax.Typed.AcRecordField (f, _) :: acs' -> f :: path_of_access_list acs'
  | Syntax.Typed.AcArrayIndex (_, _) :: acs' ->
      _CONTENT :: path_of_access_list acs'

module PathTree = struct
  (** Tree representing invalid paths in the abstract memory. A path is a
      succession of struct field names or "[]" (used when accessing an array
      element). If a path p is contained in a tree (i.e., following the path
      leads to a leaf), then p and every paths prefixed by p are considered
      invalid. *)

  (** [Leaf] and [Node []] are two possible representations for leaves. *)

  type t =
    | Leaf
    | Node of (ident * t) list

  (** [create p] creates a path tree from the path [p]. *)
  let rec create (p : path) : t =
    match p with
    | [] -> Leaf
    | x :: p' -> Node [(x, create p')]

  (** [add t p] adds the path [p] into [t]. If [t] already contains a prefix of
      [p], then [t] is unchanged. If [p] is a prefix of some paths contained in
      [t], then those paths are replaced by [p]. *)
  let rec add (t : t) (p : path) : t =
    match (t, p) with
    | _, [] -> t
    | (Leaf | Node []), _ -> Leaf
    | Node ln, x :: p' -> Node (add_list x p' ln)

  (** [add_list x p l] adds the path [x.p] into the node list [ln]. *)
  and add_list (x : ident) (p : path) (ln : (ident * t) list) =
    match ln with
    | [] -> [(x, create p)]
    | (y, ty) :: ln' ->
        if x = y then (y, add ty p) :: ln' else (y, ty) :: add_list x p ln'

  (** [union t1 t2] computes the union of [t1] and [t2]. Similarly to [add], if
      [t1] (resp. [t2]) contains prefixes of some paths in [t2] (resp. [t1]),
      the result only keeps the concerned paths of [t1] (resp [t2]). *)
  let rec union (t1 : t) (t2 : t) : t =
    match (t1, t2) with
    | Leaf, Leaf | Node _, Leaf | Leaf, Node _ | Node [], _ | _, Node [] -> Leaf
    | Node l1, Node l2 -> Node (union_list l1 l2)

  (** [union_list ln1 ln2] computes the union of the node lists [ln1] and [ln2].
  *)
  and union_list (ln1 : (ident * t) list) (ln2 : (ident * t) list) =
    match ln1 with
    | [] -> ln2
    | (f1, t1) :: ln1' -> begin
        match List.assoc_opt f1 ln2 with
        | Some t2 ->
            (f1, union t1 t2) :: union_list ln1' (List.remove_assoc f1 ln2)
        | None -> (f1, t1) :: union_list ln1' ln2
      end

  (** [flatten t] collects all paths of [t] in a list of paths. *)
  let rec flatten (t : t) : path list =
    match t with
    | Leaf | Node [] -> [[]]
    | Node ln -> flatten_list ln

  (** [flatten_list l] flattens the node list [l]. *)
  and flatten_list (ln : (ident * t) list) : path list =
    match ln with
    | [] -> []
    | (f, t) :: ln' ->
        List.append (List.map (fun p -> f :: p) (flatten t)) (flatten_list ln')

  (** [to_string t] transforms all paths of [t] into a string. *)
  let to_string (t : t) : string =
    list_to_string_braces path_to_string (flatten t)

  (** [is_completely_valid_path t p] checks wether [p] is a valid path in [t],
      i.e. [t] does not contain a path prefixed by [p], or a prefix of [p]. *)
  let rec is_completely_valid_path (t : t) (p : path) : bool =
    match (t, p) with
    | (Node [] | Leaf), _ -> false
    | Node ln, f1 :: p' -> begin
        match List.assoc_opt f1 ln with
        | Some t1 -> is_completely_valid_path t1 p'
        | None -> true
      end
    | Node ln, [] -> false

  (** [prefixed_by t p] returns the sub tree of [t] prefixed by the path [p]. If
      a prefix of [p] is already invalid, then it returns [Some Leaf]. If [p] is
      valid, it returns [None]. *)
  let rec prefixed_by (t : t) (p : path) : t option =
    match (t, p) with
    | (Leaf | Node []), _ -> Some Leaf
    | _, [] -> Some t
    | Node ln, f :: p' -> begin
        match List.assoc_opt f ln with
        | Some tf -> prefixed_by tf p'
        | None -> None
      end
end

type path_tree = PathTree.t

(** An abstract location is an identifer. *)
type absloc = ident

let comparison_to_int (c : Datatypes.comparison) : int =
  match c with
  | Datatypes.Eq -> 0
  | Datatypes.Lt -> -1
  | Datatypes.Gt -> 1

module Ident1 = struct
  type t = ident

  let compare (x : t) (y : t) : int = comparison_to_int (Pos.compare x y)
end

module IdentPair = struct
  type t = ident * ident

  let compare ((x1, y1) : t) ((x2, y2) : t) : int =
    match Pos.compare x1 x2 with
    | Datatypes.Eq -> comparison_to_int (Pos.compare y1 y2)
    | _ as c -> comparison_to_int c
end

module IdentMap = Map.Make (Ident1)
module IdentPairMap = Map.Make (IdentPair)
module IdentSet = Set.Make (Ident1)

module AbsDom = struct
  (** Abstract domain for the alias analysis. The two possible values are
      - A valid abstract state containing the alias information OR
      - Top *)

  type pointsto_set = IdentSet.t

  type var_set = IdentSet.t

  (** Abstract environement. Bindings in a map of type [absenv] are of the form
      x -> \{l1, ..., ln\}. It means that the variable x may point to the
      abstract locations \{l1, ..., ln\}. *)
  type absenv = pointsto_set IdentMap.t

  (** Reverse abstract environment. Bindings in a map of type [rev_absenv] are
      of the form l -> \{x1, ..., xn\}. It means that the abstract location l
      may be pointed by the variables \{x1, ..., xn\}. *)
  type rev_absenv = var_set IdentMap.t

  (** Abstract memory. Bindings in a map of type [absmem] are of the form (l, f)
      -> \{l1, ..., ln\}. Following the path [f] from l leads to locations \{l1,
      ..., ln\}. It means that the field or abstract array index f of the
      abstract location l may point to \{l1, ..., ln\}. If an abstract location
      l corresponds to a concrete array in memory, then only one edge labelled
      "[]" pointing to the reprensetation of the array elements (if they are
      non-primitve) is going out l (i.e. all array elements are condensed into
      one abastract element). *)
  type absmem = pointsto_set IdentPairMap.t

  (** Reverse abstract memory. Bindings in a map of type [rev_absmem] are of the
      form l -> \{(f1, \{l1_1, ..., l1_n\}), ..., (fm, \{lm_1, ..., lm_n\})\}.
      We assume that f1, ..., fm are different for the same binding key l. It
      means that the abstract location l may be pointed by the field or abstract
      array index fi of location li_j. This representation is better to traverse
      all the graph from a given location than a map with bindings of types (f,
      l) -> \{l1, ..., ln\}. *)
  type rev_absmem = (ident * pointsto_set) list IdentMap.t

  (** Invalid paths environment. It binds each variables to a set of invalid
      paths. *)
  type path_map = path_tree IdentMap.t

  (** The abstract state. It contains:
      - The abstract environment [st_env] and its reverse version [st_rev_env];
      - The abstract memory [st_mem] and its reverse version [st_rev_mem];
      - The set of locations [st_res] pointed by the return value of the
        function;
      - The invalid paths environment [st_inv];
      - The invalid paths [st_inv_res] of the return value of the function;
      - The environment of locked arrays;
      - The next fresh location identifier [st_next_loc]. *)
  type absstate = {
    st_env : absenv;
    st_mem : absmem;
    st_rev_env : rev_absenv;
    st_rev_mem : rev_absmem;
    st_res : pointsto_set;
    st_inv : path_map;
    st_inv_res : path_tree option;
    st_arr_locked : Typed.atom IdentMap.t;
    st_next_loc : ident;
  }

  type err_info = {
    ei_stmt : string option;
    ei_msg : string;
  }

  let mk_err_info (msg : string) : err_info = { ei_stmt = None; ei_msg = msg }

  let mk_err_info_with_stmt (stmt : string) (msg : string) : err_info =
    { ei_stmt = Some stmt; ei_msg = msg }

  type t =
    | AbsState of absstate
    | Top of err_info

  let dbind (a : t) (f : absstate -> t) : t =
    match a with
    | AbsState a -> f a
    | Top err -> Top err

  let env_empty : absenv = IdentMap.empty

  let mem_empty : absmem = IdentPairMap.empty

  let set_empty : IdentSet.t = IdentSet.empty

  (** [env_reverse_single x ls rev] reverses the binding [x] -> [ls] into the
      reverse environment [rev]. *)
  let env_reverse_single (x : ident) (ls : pointsto_set) (rev : rev_absenv) :
      rev_absenv =
    IdentSet.fold
      (fun l accS ->
        IdentMap.update
          l
          (fun vars ->
            match vars with
            | Some vars -> Some (IdentSet.add x vars)
            | None -> Some (IdentSet.singleton x))
          accS)
      ls
      rev

  (** [env_reverse ev] reverses the abstract environment [ev]. *)
  let env_reverse (ev : absenv) : rev_absenv =
    IdentMap.fold env_reverse_single ev IdentMap.empty

  (** [add_loc_from_id lip f l] adds the location [l] coming from path [[f]] in
      the reverse memory value [lip]. *)
  let rec add_loc_from_id (lip : (ident * pointsto_set) list) (f : ident)
      (l : absloc) : (ident * pointsto_set) list =
    match lip with
    | [] -> [(f, IdentSet.singleton l)]
    | (fi, ls) :: lip' ->
        if fi = f then (fi, IdentSet.add l ls) :: lip'
        else (fi, ls) :: add_loc_from_id lip' f l

  (** [mem_reverse_single (l, f) ls] reverses the binding [(l, f)] -> [ls] into
      the reverse memory [rm]. *)
  let mem_reverse_single ((l, f) : absloc * ident) (ls : pointsto_set)
      (rm : rev_absmem) : rev_absmem =
    IdentSet.fold
      (fun li accS ->
        IdentMap.update
          li
          (fun lr ->
            match lr with
            | Some lr -> Some (add_loc_from_id lr f l)
            | None -> Some [(f, IdentSet.singleton l)])
          accS)
      ls
      rm

  (** [mem_reverse m] reverses the abstract memory [m]. *)
  let mem_reverse (m : absmem) : rev_absmem =
    IdentPairMap.fold
      (fun (l, f) ls accM -> mem_reverse_single (l, f) ls accM)
      m
      IdentMap.empty

  (** [env_add st x locs] adds the binding [x] -> [locs] in the state [st] and
      reflects this change in the reverse environment. *)
  let env_add (st : absstate) (x : ident) (locs : pointsto_set) : absstate =
    let ev = IdentMap.add x locs st.st_env in
    (* If x -> {l1, ..., ln} is the old binding of st.st_env, then removes x
       in the var set associated with l1, ..., ln in st.st_rev_env. *)
    (* As st.st_rev_env should be the reverse graph of st.st_env,
       removing x in the var set mapped for a li not belonging to {l1, ..., ln} does nothing. *)
    let rev = IdentMap.map (fun l -> IdentSet.remove x l) st.st_rev_env in
    (* Adds the new reverse bindings *)
    (* If x -> {m1, ..., mn} is the new binding added in st.st_env,
       then adds x to all vi such that mi -> vi belongs to rev, for mi in {m1, ..., mn}. *)
    let rev = env_reverse_single x locs rev in
    { st with st_env = ev; st_rev_env = rev }

  (** [mem_weak_update st (l, f) locs] adds the locations [locs] into the set of
      locations already pointed by [(l, f)] in [st], and reflects the change in
      the reverse memory. *)
  let mem_weak_update (st : absstate) ((l, f) : ident * ident)
      (locs : pointsto_set) : absstate =
    let m =
      IdentPairMap.update
        (l, f)
        (fun f_locs ->
          match f_locs with
          | Some f_locs -> Some (IdentSet.union f_locs locs)
          | None -> Some locs)
        st.st_mem
    in
    {
      st with
      st_mem = m;
      st_rev_mem = mem_reverse m;
      st_next_loc = Pos.add BinNums.Coq_xH (Pos.max st.st_next_loc l);
    }

  (** [mem_get m l f] returns the points-to set associated with [(l, f)] in [m].
      Returns an empty set if [(l, f)] is not a key of [m]. *)

  let mem_get (m : absmem) (l : absloc) (f : ident) : pointsto_set =
    match IdentPairMap.find_opt (l, f) m with
    | Some l_f -> l_f
    | None -> set_empty

  (** [env_unions e1 e2] computes the union of the environments [e1] and [e2].
  *)
  let env_union (e1 : absenv) (e2 : absenv) : absenv =
    IdentMap.union (fun _ x y -> Some (IdentSet.union x y)) e1 e2

  (** [rev_env_unions e1 e2] computes the union of the reverse environments
      [re1] and [re2]. *)
  let rev_env_union (re1 : rev_absenv) (re2 : rev_absenv) : rev_absenv =
    IdentMap.union (fun _ x y -> Some (IdentSet.union x y)) re1 re2

  (** [mem_union m1 m2] computes the union of the memories [m1] and [m2]. *)
  let mem_union (m1 : absmem) (m2 : absmem) : absmem =
    IdentPairMap.union (fun _ x y -> Some (IdentSet.union x y)) m1 m2

  (** [mem_union m1 m2] computes the union of the reverse memories [rm1] and
      [rm2]. *)
  let rev_mem_union (rm1 : rev_absmem) (rm2 : rev_absmem) : rev_absmem =
    let rec union_rev_mem_val (l1 : (ident * pointsto_set) list)
        (l2 : (ident * pointsto_set) list) : (ident * pointsto_set) list =
      match l1 with
      | [] -> l2
      | (f1, locs1) :: l1' -> begin
          match List.assoc_opt f1 l2 with
          | Some locs2 ->
              let locs' = IdentSet.union locs1 locs2 in
              (f1, locs') :: union_rev_mem_val l1' (List.remove_assoc f1 l2)
          | None -> (f1, locs1) :: union_rev_mem_val l1' l2
        end
    in
    IdentMap.union (fun _ lx ly -> Some (union_rev_mem_val lx ly)) rm1 rm2

  (** [inv_add st x t] binds the variabled [x] to the invalid paths [t] in [st].
  *)
  let inv_add (st : absstate) (x : ident) (t : path_tree) : absstate =
    { st with st_inv = IdentMap.add x t st.st_inv }

  (** [inv_union iv1 iv2] computes the union of the invalid paths environments
      [iv1] and [iv2]. *)
  let inv_union (iv1 : path_map) (iv2 : path_map) : path_map =
    IdentMap.union (fun _ t1 t2 -> Some (PathTree.union t1 t2)) iv1 iv2

  (** [arr_locked_union at1 at2] computes the union of the accessed array
      indexes. The union fails if the same array in [at1] and [at2] are locked
      with different indexes. *)
  let arr_locked_union (at1 : Typed.atom IdentMap.t)
      (at2 : Typed.atom IdentMap.t) : Typed.atom IdentMap.t option =
    try
      Some
        (IdentMap.union
           (fun _ i1 i2 -> if i1 <> i2 then failwith "" else Some i1)
           at1
           at2)
    with Failure _ -> None

  let make_state (ev : absenv) (m : absmem) (rev : rev_absenv) (rm : rev_absmem)
      (r : pointsto_set) (iv : path_map) (ivr : path_tree option)
      (al : Typed.atom IdentMap.t) (nl : ident) : absstate =
    {
      st_env = ev;
      st_mem = m;
      st_rev_env = rev;
      st_rev_mem = rm;
      st_res = r;
      st_inv = iv;
      st_inv_res = ivr;
      st_arr_locked = al;
      st_next_loc = nl;
    }

  let make_state2 (ev : absenv) (m : absmem) : absstate =
    {
      st_env = ev;
      st_mem = m;
      st_rev_env = env_reverse ev;
      st_rev_mem = mem_reverse m;
      st_res = set_empty;
      st_inv = IdentMap.empty;
      st_inv_res = None;
      st_arr_locked = IdentMap.empty;
      st_next_loc = BinNums.Coq_xH;
    }

  (** [union d1 d2] computes the union of the two abstract domains [d1] and
      [d2]. *)
  let union (d1 : t) (d2 : t) : t =
    let aux st1 st2 =
      let ev = env_union st1.st_env st2.st_env in
      let m = mem_union st1.st_mem st2.st_mem in
      let rev = rev_env_union st1.st_rev_env st2.st_rev_env in
      let rm = rev_mem_union st1.st_rev_mem st2.st_rev_mem in
      let res = IdentSet.union st1.st_res st2.st_res in
      let inv = inv_union st1.st_inv st2.st_inv in
      let inv_res =
        match (st1.st_inv_res, st2.st_inv_res) with
        | Some t1, Some t2 -> Some (PathTree.union t1 t2)
        | Some t1, None -> Some t1
        | None, Some t2 -> Some t2
        | None, None -> None
      in
      let next_loc =
        Pos.add BinNums.Coq_xH (Pos.max st1.st_next_loc st2.st_next_loc)
      in
      let al_union = arr_locked_union st1.st_arr_locked st2.st_arr_locked in
      match al_union with
      | Some al -> AbsState (make_state ev m rev rm res inv inv_res al next_loc)
      | None ->
          Top
            (mk_err_info
               "impossible domain union, some arrays are locked on different \
                indexes")
    in
    match (d1, d2) with
    | AbsState st1, AbsState st2 -> aux st1 st2
    | Top err, _ | _, Top err -> Top err

  (* Validity check *)

  (** [is_valid_path d x p] checks wether the path [x.p] is valid in [d]. *)
  let is_valid_path (d : t) (x : ident) (p : path) : bool =
    match d with
    | AbsState st -> begin
        match IdentMap.find_opt x st.st_inv with
        | Some t -> PathTree.is_completely_valid_path t p
        | None -> true
      end
    | Top _ -> false

  (** [is_valid_return] checks wether the return value of the function being
      analysed is valid, i.e. st_inv_res is [None] if [d] is a valid abstract
      state. *)
  let is_valid_return (d : t) : bool =
    match d with
    | AbsState st -> if st.st_inv_res = None then true else false
    | _ -> false
end

type absdom = AbsDom.t

(** A function descriptor. It contains:
    - The parameter list [fd_params];
    - The call state [fd_callstate] built such that no inter-aliasing occurs
      between parameters, and that each of them points to a unique tree-shaped
      part of the memory;
    - The return state [fd_returnstate]. The way this return state is
      constructed depends wether the function is defined or abstract. *)

type fun_descr = {
  fd_params : (ident * btyp) list;
  fd_callstate : AbsDom.absstate;
  fd_returnstate : absdom;
}

type fenv = fun_descr IdentMap.t
