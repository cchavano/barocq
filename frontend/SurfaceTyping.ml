open Printf
open Integers
open Intop
open Syntax
open Location
open SurfaceAST

(** Name of the module being analyzed. *)
let curr_mname : string ref = ref ""

type btyp =
  | BBool
  | BInt32 of Types.signedness
  | BInt64 of Types.signedness
  | BArray of btyp
  | BEnum of string * string
  | BRecord of string * string
  | BAbs of string * string
  | BFun of btyp list * btyp

type expected_typ =
  | Expect_typ of btyp
  | Expect_int
  | Expect_int_or_bool
  | Expect_int_or_bool_or_enum
  | Expect_array
  | Expect_enum
  | Expect_record
  | Expect_function

type current_typ =
  | Current_typ of btyp
  | Current_array
  | Current_record

type error_cause =
  | Type_mismatch of expected_typ * current_typ
  | Forbidden_cast of btyp * btyp
  | Undefined_ident of string
  | Undefined_type of string
  | Undefined_enum_elem of string * btyp
  | Unknown_field of string * string
  | Module_not_found of string
  | Wrong_argument_number of int * int
  | Variable_shadowing_diff_type of string * btyp
  | Already_defined_type of string
  | Already_defined_glob of string
  | Duplicate_record_field of string * string
  | Duplicate_param of string * string
  | Duplicate_module of string
  | Missing_record_fields of string list
  | Missing_param_write of string * btyp
  | Too_many_param_write of string
  | Mismatch_type_param_write of string * btyp * btyp
  | Const_var_enum_unsupported
  | Const_var_not_prim of string
  | Const_var_abstract of string
  | Invalid_operand of string * string
  | Use_of_non_prim_glob
  | Redundant_pattern of string
  | Non_exhaustive_pattern_matching of string

exception Error of error_cause * unit Location.t option

let rec btyp_to_string (ty : btyp) : string =
  match ty with
  | BBool -> "bool"
  | BInt32 Types.Signed -> "i32"
  | BInt32 Types.Unsigned -> "u32"
  | BInt64 Types.Signed -> "i64"
  | BInt64 Types.Unsigned -> "u64"
  | BArray (BArray ta) -> sprintf "array (%s)" (btyp_to_string ta)
  | BArray ta -> sprintf "array %s" (btyp_to_string ta)
  | BEnum (mname, tid) | BRecord (mname, tid) | BAbs (mname, tid) ->
      if mname = !curr_mname then tid else sprintf "%s::%s" mname tid
  | BFun (tparams, tret) ->
      PrintTypes.funtyp_to_string btyp_to_string tparams tret

let btyp_is_prim (ty : btyp) : bool =
  match ty with
  | BBool | BInt32 _ | BInt64 _ | BEnum _ -> true
  | _ -> false

let msg_from_failure (cause : error_cause) : string =
  match cause with
  | Undefined_ident x -> sprintf "undefined identifier %s" x
  | Type_mismatch (ety, ty) ->
      let prefix =
        match ty with
        | Current_typ ty ->
            sprintf "this expression has type %s" (btyp_to_string ty)
        | Current_array -> sprintf "this expression is an array"
        | Current_record -> sprintf "this expression is a record"
      in
      let suffix =
        match ety with
        | Expect_typ ty ->
            sprintf
              "but an expression was expected of type %s"
              (btyp_to_string ty)
        | Expect_int -> sprintf "but an integer expression was expected"
        | Expect_int_or_bool ->
            sprintf "but a boolean or integer expression was expected"
        | Expect_int_or_bool_or_enum ->
            sprintf "but a boolean, integer or enum expression was expected"
        | Expect_array -> sprintf "but an array was expected"
        | Expect_enum -> sprintf "but an enum was expected"
        | Expect_record -> sprintf "but a record was expected"
        | Expect_function -> sprintf "but a function was expected"
      in
      sprintf "%s %s" prefix suffix
  | Unknown_field (f, rc) ->
      sprintf "field %s is not defined for record type %s" f rc
  | Wrong_argument_number (exp, curr) ->
      let plurial = if exp > 1 then "s" else "" in
      let verb = if curr > 1 then "are" else "is" in
      sprintf
        "this function call expects %d argument%s, but %d %s given"
        exp
        plurial
        curr
        verb
  | Variable_shadowing_diff_type (id, ty) ->
      sprintf
        "cannot shadow variable %s with a value of type %s"
        id
        (btyp_to_string ty)
  | Already_defined_type tid -> sprintf "type %s is already defined" tid
  | Already_defined_glob gid ->
      sprintf "global identifier %s is already used" gid
  | Undefined_type tid -> sprintf "type %s is not defined" tid
  | Duplicate_record_field (fname, rid) ->
      sprintf "field %s is a duplicated in record type %s" fname rid
  | Duplicate_param (p, f) ->
      sprintf "parameter %s is duplicated in the definition of function %s" p f
  | Forbidden_cast (t1, t2) ->
      sprintf
        "cannot cast a value of type %s to a value of type %s"
        (btyp_to_string t1)
        (btyp_to_string t2)
  | Module_not_found mname -> sprintf "module %s not found" mname
  | Duplicate_module mname ->
      sprintf "a module with name %s already exists" mname
  | Missing_record_fields mfields ->
      sprintf
        "the following record fields are missing: %s"
        (PrintUtils.list_to_string ~sep:", " (fun x -> x) mfields)
  | Too_many_param_write id ->
      sprintf
        "abstract function %s must only contain one @write-annotated parameter"
        id
  | Missing_param_write (fid, ty) ->
      sprintf
        "abstract function %s returns a value of type %s, but no parameter of \
         this type is annotated with @write"
        fid
        (btyp_to_string ty)
  | Mismatch_type_param_write (fid, tw, tret) ->
      sprintf
        "abstract function %s writes in a parameter of type %s, but returns a \
         value of type %s"
        fid
        (btyp_to_string tw)
        (btyp_to_string tret)
  | Const_var_enum_unsupported ->
      "using an enum constructor in a constant definition is not yet supported"
  | Const_var_not_prim id ->
      sprintf
        "%s is not primitive, it cannot be used in a constant definition"
        id
  | Const_var_abstract id ->
      sprintf "%s is abstract, it cannot be used in a constant definition" id
  | Invalid_operand (op, ty) -> sprintf "invalid left operand for %s %s" op ty
  | Use_of_non_prim_glob ->
      "the use of non-primitive global constants is forbidden"
  | Redundant_pattern p -> sprintf "pattern %s is redundant" p
  | Non_exhaustive_pattern_matching u ->
      sprintf
        "this pattern-matching is not exhaustive. Example: pattern %s is not \
         matched"
        u
  | Undefined_enum_elem (e, t) ->
      sprintf
        "there is no enum constructor of type %s named %s"
        (btyp_to_string t)
        e

let error ?(loc : 'a Location.t option = None) (c : error_cause) =
  let loc =
    match loc with
    | Some loc -> Some (Location.make loc.startpos loc.endpos ())
    | None -> None
  in
  raise (Error (c, loc))

let update_error_loc (cause : error_cause) (loc1 : unit Location.t option)
    (loc2 : 'a Location.t) =
  match loc1 with
  | Some _ -> error cause ~loc:loc1
  | None -> error cause ~loc:(Some loc2)

module IdentMap = Map.Make (String)
module IdentSet = Set.Make (String)

type type_def =
  | TdEnum of string list
  | TdRecord of (string * btyp) list
  | TdAbstract of string
  | TdAlias of btyp

type tenv = {
  tenv_defs : type_def IdentMap.t;
  tenv_constr_types : string IdentMap.t;
}

let tenv_empty =
  { tenv_defs = IdentMap.empty; tenv_constr_types = IdentMap.empty }

type gtenv = {
  gtenv_local : tenv;
  gtenv_extern : tenv IdentMap.t;
}

let gtenv_empty = { gtenv_local = tenv_empty; gtenv_extern = IdentMap.empty }

let compose_idents (mname : string) (id : string) : string =
  Printf.sprintf "%s::%s" mname id

let compose_loc_idents (mname : ident) (id : ident) : ident =
  let v = compose_idents mname.content id.content in
  Location.make mname.startpos id.endpos v

let loc_of_cident (cid : cident) : unit Location.t =
  match cid with
  | IdSimple id -> Location.make id.startpos id.endpos ()
  | IdPrefixed (mname, id) -> Location.make mname.startpos id.endpos ()

let tenv_get_def (mname : string) (te : tenv) (tid : ident) : btyp option =
  let tid = tid.content in
  match IdentMap.find_opt tid te.tenv_defs with
  | Some td ->
      let ty =
        match td with
        | TdEnum _ -> BEnum (mname, tid)
        | TdRecord _ -> BRecord (mname, tid)
        | TdAbstract _ -> BAbs (mname, tid)
        | TdAlias ty -> ty
      in
      Some ty
  | None -> None

let tenv_get_constr_typ (mname : string) (te : tenv) (cname : ident) :
    btyp option =
  match IdentMap.find_opt cname.content te.tenv_constr_types with
  | Some eid -> Some (BEnum (mname, eid))
  | _ -> None

let tenv_update_defs (te : tenv) (tid : ident) (td : type_def) : tenv =
  let tid_str = tid.content in
  match IdentMap.find_opt tid_str te.tenv_defs with
  | Some _ -> error (Already_defined_type tid_str) ~loc:(Some tid)
  | None -> { te with tenv_defs = IdentMap.add tid_str td te.tenv_defs }

let tenv_update_constr_types (te : tenv) (cname : ident) (eid : string) : tenv =
  match IdentMap.find_opt cname.content te.tenv_constr_types with
  | Some _ -> error (Already_defined_glob cname.content) ~loc:(Some cname)
  | None ->
      {
        te with
        tenv_constr_types = IdentMap.add cname.content eid te.tenv_constr_types;
      }

let gtenv_get_def (imports : ident list) (gte : gtenv) (cid : cident) : btyp =
  let gtenv_get_prefixed (mname : ident) (tid : ident) : btyp option =
    match IdentMap.find_opt mname.content gte.gtenv_extern with
    | Some te -> tenv_get_def mname.content te tid
    | None -> error (Module_not_found mname.content) ~loc:(Some mname)
  in
  let rec gtenv_get_imports (imports : ident list) (tid : ident) : btyp =
    match imports with
    | [] -> error (Undefined_type tid.content) ~loc:(Some tid)
    | m1 :: imports' -> begin
        match gtenv_get_prefixed m1 tid with
        | Some ty -> ty
        | None -> gtenv_get_imports imports' tid
      end
  in
  match cid with
  | IdSimple tid -> begin
      match tenv_get_def !curr_mname gte.gtenv_local tid with
      | Some ty -> ty
      | None -> gtenv_get_imports imports tid
    end
  | IdPrefixed (mname, tid) -> begin
      match gtenv_get_prefixed mname tid with
      | Some ty -> ty
      | None ->
          let tid' = compose_loc_idents mname tid in
          error (Undefined_type tid'.content) ~loc:(Some tid')
    end

let gtenv_get_constr_typ (imports : ident list) (gte : gtenv) (cid : cident) :
    btyp =
  let gtenv_get_prefixed (mname : ident) (cname : ident) : btyp option =
    match IdentMap.find_opt mname.content gte.gtenv_extern with
    | Some te -> tenv_get_constr_typ mname.content te cname
    | None -> error (Module_not_found mname.content) ~loc:(Some mname)
  in
  let rec gtenv_get_imports (imports : ident list) (cname : ident) : btyp =
    match imports with
    | [] -> error (Undefined_ident cname.content) ~loc:(Some cname)
    | m1 :: imports' -> begin
        match gtenv_get_prefixed m1 cname with
        | Some ty -> ty
        | None -> gtenv_get_imports imports' cname
      end
  in
  match cid with
  | IdSimple cname -> begin
      match tenv_get_constr_typ !curr_mname gte.gtenv_local cname with
      | Some ty -> ty
      | None -> gtenv_get_imports imports cname
    end
  | IdPrefixed (mname, cname) -> begin
      match gtenv_get_prefixed mname cname with
      | Some ty -> ty
      | None ->
          let tid' = compose_loc_idents mname cname in
          error (Undefined_ident tid'.content) ~loc:(Some tid')
    end

let gtenv_update_local_enums (gte : gtenv) (eid : ident) (elems : string list) :
    gtenv =
  { gte with gtenv_local = tenv_update_defs gte.gtenv_local eid (TdEnum elems) }

let gtenv_update_local_records (gte : gtenv) (rid : ident)
    (fields : (string * btyp) list) : gtenv =
  {
    gte with
    gtenv_local = tenv_update_defs gte.gtenv_local rid (TdRecord fields);
  }

let gtenv_update_local_abstracts (gte : gtenv) (tid : ident) : gtenv =
  {
    gte with
    gtenv_local = tenv_update_defs gte.gtenv_local tid (TdAbstract tid.content);
  }

let gtenv_update_local_aliases (gte : gtenv) (alias : ident) (ty : btyp) : gtenv
    =
  { gte with gtenv_local = tenv_update_defs gte.gtenv_local alias (TdAlias ty) }

type gcontext = {
  gx_local : btyp IdentMap.t;
  gx_extern : btyp IdentMap.t IdentMap.t;
}

let gtenv_update_local_constr_types (gte : gtenv) (elem : ident) (eid : string)
    : gtenv =
  { gte with gtenv_local = tenv_update_constr_types gte.gtenv_local elem eid }

let gcontext_empty = { gx_local = IdentMap.empty; gx_extern = IdentMap.empty }

type var_kind =
  | VarLocal
  | VarParam

type lcontext = (btyp * var_kind) IdentMap.t

let lcontext_empty = IdentMap.empty

let rec styp_to_btyp (imports : ident list) (gte : gtenv) (sty : styp) : btyp =
  match sty with
  | SBool -> BBool
  | SInt32 s -> BInt32 s
  | SInt64 s -> BInt64 s
  | SArray sta -> BArray (styp_to_btyp imports gte sta)
  | SIdent stid -> gtenv_get_def imports gte stid
  | SFun (stparams, stret) ->
      let tparams =
        List.map (fun (_, sty) -> styp_to_btyp imports gte sty) stparams
      in
      let tret = styp_to_btyp imports gte stret in
      BFun (tparams, tret)

type cvalue =
  | VBool of bool
  | VInt32 of Int.int * Types.signedness
  | VInt64 of Int64.int * Types.signedness
  | VEnum
  | VNotprim
  | VAbs

type cenv = {
  cenv_local : cvalue IdentMap.t;
  cenv_extern : cvalue IdentMap.t IdentMap.t;
}

let cenv_get (imports : ident list) (ce : cenv) (cid : cident) : cvalue =
  let check_cval (id : ident) (v : cvalue) : cvalue =
    match v with
    | VEnum -> error Const_var_enum_unsupported ~loc:(Some id)
    | VAbs -> error (Const_var_abstract id.content) ~loc:(Some id)
    | VNotprim -> error (Const_var_not_prim id.content) ~loc:(Some id)
    | _ -> v
  in
  let cenv_get_prefixed (mname : ident) (id : ident) : cvalue option =
    match IdentMap.find_opt mname.content ce.cenv_extern with
    | Some mx -> IdentMap.find_opt id.content mx
    | None -> error (Module_not_found mname.content) ~loc:(Some mname)
  in
  let rec cenv_get_imports (imports : ident list) (id : ident) : cvalue =
    match imports with
    | [] -> error (Undefined_ident id.content) ~loc:(Some id)
    | m1 :: imports' -> begin
        match cenv_get_prefixed m1 id with
        | Some v -> v
        | None -> cenv_get_imports imports' id
      end
  in
  match cid with
  | IdSimple id -> begin
      match IdentMap.find_opt id.content ce.cenv_local with
      | Some v -> check_cval id v
      | None -> cenv_get_imports imports id
    end
  | IdPrefixed (mname, id) -> begin
      match cenv_get_prefixed mname id with
      | Some v -> check_cval id v
      | None ->
          let id' = compose_loc_idents mname id in
          error (Undefined_ident id'.content) ~loc:(Some id')
    end

let cenv_update_local (ce : cenv) (x : ident) (v : cvalue) : cenv =
  match IdentMap.find_opt x.content ce.cenv_local with
  | Some _ -> error (Already_defined_glob x.content) ~loc:(Some x)
  | None -> { ce with cenv_local = IdentMap.add x.content v ce.cenv_local }

let cenv_empty : cenv =
  { cenv_local = IdentMap.empty; cenv_extern = IdentMap.empty }

let eval_cunop (op : unary_op) (v : cvalue) : cvalue =
  match (op, v) with
  | UopNotbool, VBool b -> VBool (not b)
  | UopNotint, VInt32 (i, s) -> VInt32 (Int.not i, s)
  | UopNeg, VInt32 (i, s) -> VInt32 (Int.neg i, s)
  | UopPlus, VInt32 (i, s) -> v
  | UopNotint, VInt64 (i, s) -> VInt64 (Int64.not i, s)
  | UopNeg, VInt64 (i, s) -> VInt64 (Int64.neg i, s)
  | UopPlus, VInt64 (i, s) -> v
  | _ -> assert false

let eval_cbinop (op : binary_op) (v1 : cvalue) (v2 : cvalue) : cvalue =
  match op with
  | BopAndbool -> begin
      match (v1, v2) with
      | VBool b1, VBool b2 -> VBool (b1 && b2)
      | _ -> assert false
    end
  | BopOrbool -> begin
      match (v1, v2) with
      | VBool b1, VBool b2 -> VBool (b1 || b2)
      | _ -> assert false
    end
  | BopXorbool -> begin
      match (v1, v2) with
      | VBool b1, VBool b2 -> VBool (Datatypes.xorb b1 b2)
      | _ -> assert false
    end
  | BopAdd -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then VInt32 (Int.add i1 i2, s1) else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then VInt64 (Int64.add i1 i2, s1) else assert false
      | _ -> assert false
    end
  | BopSub -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then VInt32 (Int.sub i1 i2, s1) else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then VInt64 (Int64.sub i1 i2, s1) else assert false
      | _ -> assert false
    end
  | BopMul -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then VInt32 (Int.mul i1 i2, s1) else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then VInt64 (Int64.mul i1 i2, s1) else assert false
      | _ -> assert false
    end
  | BopDiv -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then
            let div, ty =
              if s1 = Types.Signed then (I32.div, "i32") else (U32.div, "u32")
            in
            let r =
              match div i1 i2 with
              | Errors.OK r -> r
              | Errors.Error _ -> error (Invalid_operand (ty, "division"))
            in
            VInt32 (r, s1)
          else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then
            let div, ty =
              if s1 = Types.Signed then (I64.div, "i64") else (U64.div, "u64")
            in
            let r =
              match div i1 i2 with
              | Errors.OK r -> r
              | Errors.Error _ -> error (Invalid_operand (ty, "division"))
            in
            VInt64 (r, s1)
          else assert false
      | _ -> assert false
    end
  | BopMod -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then
            let coq_mod, ty =
              if s1 = Types.Signed then (I32.coq_mod, "i32")
              else (U32.coq_mod, "u32")
            in
            let r =
              match coq_mod i1 i2 with
              | Errors.OK r -> r
              | Errors.Error _ -> error (Invalid_operand (ty, "modulo"))
            in
            VInt32 (r, s1)
          else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then
            let coq_mod, ty =
              if s1 = Types.Signed then (I64.coq_mod, "i64")
              else (U64.coq_mod, "u64")
            in
            let r =
              match coq_mod i1 i2 with
              | Errors.OK r -> r
              | Errors.Error _ -> error (Invalid_operand (ty, "modulo"))
            in
            VInt64 (r, s1)
          else assert false
      | _ -> assert false
    end
  | BopAndint -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then VInt32 (Int.coq_and i1 i2, s1) else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then VInt64 (Int64.coq_and i1 i2, s1) else assert false
      | _ -> assert false
    end
  | BopOrint -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then VInt32 (Int.coq_or i1 i2, s1) else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then VInt64 (Int64.coq_or i1 i2, s1) else assert false
      | _ -> assert false
    end
  | BopXorint -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then VInt32 (Int.xor i1 i2, s1) else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then VInt64 (Int64.xor i1 i2, s1) else assert false
      | _ -> assert false
    end
  | BopShl -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then VInt32 (Int.shl i1 i2, s1) else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then VInt64 (Int64.shl i1 i2, s1) else assert false
      | _ -> assert false
    end
  | BopShr -> begin
      match (v1, v2) with
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then
            let shr = if s1 = Types.Signed then Int.shr else Int.shru in
            VInt32 (shr i1 i2, s1)
          else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then
            let shr = if s1 = Types.Signed then Int64.shr else Int64.shru in
            VInt64 (shr i1 i2, s1)
          else assert false
      | _ -> assert false
    end
  | BopEq -> begin
      match (v1, v2) with
      | VBool b1, VBool b2 -> VBool (b1 = b2)
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then VBool (Int.eq i1 i2) else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then VBool (Int64.eq i1 i2) else assert false
      | _ -> assert false
    end
  | BopNeq -> begin
      match (v1, v2) with
      | VBool b1, VBool b2 -> VBool (b1 <> b2)
      | VInt32 (i1, s1), VInt32 (i2, s2) ->
          if s1 = s2 then
            let cmp = if s1 = Types.Signed then Int.cmp else Int.cmp in
            VBool (cmp Cne i1 i2)
          else assert false
      | VInt64 (i1, s1), VInt64 (i2, s2) ->
          if s1 = s2 then
            let cmp = if s1 = Types.Signed then Int64.cmp else Int64.cmp in
            VBool (cmp Cne i1 i2)
          else assert false
      | _ -> assert false
    end
  | _ ->
      let cop =
        match op with
        | BopLt -> Clt
        | BopGt -> Cgt
        | BopLe -> Cle
        | BopGe -> Cge
        | _ -> assert false
      in
      begin
        match (v1, v2) with
        | VInt32 (i1, s1), VInt32 (i2, s2) ->
            if s1 = s2 then
              let cmp = if s1 = Types.Signed then Int.cmp else Int.cmp in
              VBool (cmp cop i1 i2)
            else assert false
        | VInt64 (i1, s1), VInt64 (i2, s2) ->
            if s1 = s2 then
              let cmp = if s1 = Types.Signed then Int64.cmp else Int64.cmp in
              VBool (cmp cop i1 i2)
            else assert false
        | _ -> assert false
      end

let eval_ccast (v : cvalue) (dst_ty : btyp) : cvalue =
  match v with
  | VBool b -> begin
      match dst_ty with
      | BBool -> VBool b
      | BInt32 Types.Signed -> VInt32 (I32.of_bool b, Types.Signed)
      | BInt32 Types.Unsigned -> VInt32 (U32.of_bool b, Types.Unsigned)
      | BInt64 Types.Signed -> VInt64 (I64.of_bool b, Types.Signed)
      | BInt64 Types.Unsigned -> VInt64 (U64.of_bool b, Types.Unsigned)
      | _ -> assert false
    end
  | VInt32 (i, s) -> begin
      match dst_ty with
      | BBool ->
          if s = Types.Signed then VBool (I32.to_bool i)
          else VBool (U32.to_bool i)
      | BInt32 s' -> begin
          match (s, s') with
          | Types.Signed, Types.Unsigned -> VInt32 (U32.of_i32 i, s')
          | Types.Unsigned, Types.Signed -> VInt32 (I32.of_u32 i, s')
          | _ -> VInt32 (i, s)
        end
      | BInt64 s' -> begin
          match (s, s') with
          | Types.Signed, Types.Signed -> VInt64 (I64.of_i32 i, s')
          | Types.Signed, Types.Unsigned -> VInt64 (U64.of_i32 i, s')
          | Types.Unsigned, Types.Signed -> VInt64 (I64.of_u32 i, s')
          | Types.Unsigned, Types.Unsigned -> VInt64 (U64.of_u32 i, s')
        end
      | _ -> assert false
    end
  | VInt64 (i, s) -> begin
      match dst_ty with
      | BBool ->
          if s = Types.Signed then VBool (I64.to_bool i)
          else VBool (U64.to_bool i)
      | BInt32 s' -> begin
          match (s, s') with
          | Types.Signed, Types.Signed -> VInt32 (I32.of_i64 i, s')
          | Types.Signed, Types.Unsigned -> VInt32 (U32.of_i64 i, s')
          | Types.Unsigned, Types.Signed -> VInt32 (I32.of_u64 i, s')
          | Types.Unsigned, Types.Unsigned -> VInt32 (U32.of_u64 i, s')
        end
      | BInt64 s' -> begin
          match (s, s') with
          | Types.Signed, Types.Unsigned -> VInt64 (U64.of_i64 i, s')
          | Types.Unsigned, Types.Signed -> VInt64 (I64.of_u64 i, s')
          | _ -> VInt64 (i, s)
        end
      | _ -> assert false
    end
  | _ -> assert false

let rec eval_const (imports : ident list) (gte : gtenv) (ce : cenv) (c : const)
    : cvalue =
  match c.content with
  | CTrue -> VBool true
  | CFalse -> VBool false
  | CInt32 (i, s) -> VInt32 (i, s)
  | CInt64 (i, s) -> VInt64 (i, s)
  | CVar x -> cenv_get imports ce x
  | CUnop (op, c1) ->
      let v1 = eval_const imports gte ce c1 in
      eval_cunop op v1
  | CBinop (op, c1, c2) ->
      let v1 = eval_const imports gte ce c1 in
      let v2 = eval_const imports gte ce c2 in
      eval_cbinop op v1 v2
  | CCast (c1, ty) ->
      let v1 = eval_const imports gte ce c1 in
      let ty = styp_to_btyp imports gte ty in
      eval_ccast v1 ty
  | _ -> assert false

let gcontext_get (imports : ident list) (gx : gcontext) (cid : cident) : btyp =
  let gcontext_get_prefixed (mname : ident) (id : ident) : btyp option =
    match IdentMap.find_opt mname.content gx.gx_extern with
    | Some mx -> IdentMap.find_opt id.content mx
    | None -> error (Module_not_found mname.content) ~loc:(Some mname)
  in
  let rec gcontext_get_imports (imports : ident list) (id : ident) : btyp =
    match imports with
    | [] -> error (Undefined_ident id.content) ~loc:(Some id)
    | m1 :: imports' -> begin
        match gcontext_get_prefixed m1 id with
        | Some ty -> ty
        | None -> gcontext_get_imports imports' id
      end
  in
  let ty =
    match cid with
    | IdSimple id -> begin
        match IdentMap.find_opt id.content gx.gx_local with
        | Some ty -> ty
        | None -> gcontext_get_imports imports id
      end
    | IdPrefixed (mname, id) -> begin
        match gcontext_get_prefixed mname id with
        | Some ty -> ty
        | None ->
            let id' = compose_loc_idents mname id in
            error (Undefined_ident id'.content) ~loc:(Some id')
      end
  in
  match ty with
  | BArray _ | BRecord _ | BAbs _ -> error Use_of_non_prim_glob
  | _ -> ty

let gcontext_update_local (gte : gtenv) (gx : gcontext) (x : ident) (ty : btyp)
    : gcontext =
  match IdentMap.find_opt x.content gx.gx_local with
  | Some _ -> error (Already_defined_glob x.content) ~loc:(Some x)
  | None -> begin
      match IdentMap.find_opt x.content gte.gtenv_local.tenv_constr_types with
      | Some _ -> error (Already_defined_glob x.content) ~loc:(Some x)
      | None -> { gx with gx_local = IdentMap.add x.content ty gx.gx_local }
    end

let lcontext_update (lx : lcontext) (x : ident) (ty : btyp) : lcontext =
  match IdentMap.find_opt x.content lx with
  | Some (ty1, _) ->
      if ty1 = ty then IdentMap.add x.content (ty, VarLocal) lx
      else error (Variable_shadowing_diff_type (x.content, ty)) ~loc:(Some x)
  | None -> IdentMap.add x.content (ty, VarLocal) lx

let cident_to_string (cid : cident) : string =
  match cid with
  | IdSimple id -> id.content
  | IdPrefixed (mname, id) -> compose_idents mname.content id.content

let pattern_to_string (p : pattern) : string =
  match p with
  | PIdent cid -> cident_to_string cid
  | PWildcard _ -> "_"

let typof_constr (imports : ident list) (gte : gtenv) (x : cident) : btyp =
  gtenv_get_constr_typ imports gte x

let typof_var (imports : ident list) (gx : gcontext) (lx : lcontext)
    (x : cident) : btyp =
  match x with
  | IdSimple x' -> begin
      match IdentMap.find_opt x'.content lx with
      | Some (ty, _) -> ty
      | None -> gcontext_get imports gx x
    end
  | IdPrefixed _ -> gcontext_get imports gx x

let typecheck_unary_op (op : unary_op) (ty : btyp) : btyp =
  match (op, ty) with
  | UopNotbool, BBool
  | UopNotint, BInt32 _
  | UopNotint, BInt64 _
  | UopNeg, (BInt32 _ | BInt64 _)
  | UopPlus, (BInt32 _ | BInt64 _) -> ty
  | _, _ -> assert false

let typecheck_binary_op (op : binary_op) (ty1 : btyp) (ty2 : btyp) : btyp =
  match op with
  | BopAndbool | BopOrbool | BopXorbool -> begin
      match (ty1, ty2) with
      | BBool, BBool -> BBool
      | _, _ -> assert false
    end
  | BopEq | BopNeq -> begin
      match (ty1, ty2) with
      | BBool, BBool -> BBool
      | BInt32 s1, BInt32 s2 | BInt64 s1, BInt64 s2 ->
          if s1 = s2 then BBool else assert false
      | BEnum (mname1, t1), BEnum (mname2, t2) ->
          if mname1 = mname2 && t1 = t2 then BBool else assert false
      | _, _ -> assert false
    end
  | BopLt | BopLe | BopGt | BopGe -> begin
      match (ty1, ty2) with
      | BInt32 s1, BInt32 s2 | BInt64 s1, BInt64 s2 ->
          if s1 = s2 then BBool else assert false
      | _, _ -> assert false
    end
  | _ -> begin
      match (ty1, ty2) with
      | BInt32 s1, BInt32 s2 | BInt64 s1, BInt64 s2 ->
          if s1 = s2 then ty1 else assert false
      | _, _ -> assert false
    end

let typecheck_cast (from_ty : btyp) (to_ty : btyp) : btyp =
  match from_ty with
  | BBool | BInt32 _ | BInt64 _ -> begin
      match to_ty with
      | BBool | BInt32 _ | BInt64 _ | BEnum _ -> to_ty
      | _ -> error (Forbidden_cast (from_ty, to_ty))
    end
  | BEnum _ -> begin
      match to_ty with
      | BBool | BInt32 _ | BInt64 _ -> to_ty
      | _ -> error (Forbidden_cast (from_ty, to_ty))
    end
  | _ -> error (Forbidden_cast (from_ty, to_ty))

let typecheck_record_proj (gte : gtenv) (mname : string) (rid : string)
    (f : ident) : btyp =
  let te, rid' =
    if mname = !curr_mname then (gte.gtenv_local, rid)
    else
      match IdentMap.find_opt mname gte.gtenv_extern with
      | Some te -> (te, compose_idents mname rid)
      | None -> assert false (* Ill-typed environment *)
  in
  match IdentMap.find_opt rid te.tenv_defs with
  | Some (TdRecord fields) -> begin
      match List.assoc_opt f.content fields with
      | Some tf -> tf
      | None -> error (Unknown_field (f.content, rid'))
    end
  | _ -> assert false (* Ill-typed environment *)

let rec mname_of_ident (imports : ident list) (gte : gtenv) (gx : gcontext)
    (id : ident) : string =
  match imports with
  | [] -> error (Undefined_ident id.content) ~loc:(Some id)
  | m1 :: imports' ->
      let m1_gx = IdentMap.find m1.content gx.gx_extern in
      begin
        match IdentMap.find_opt id.content m1_gx with
        | Some _ -> m1.content
        | None -> begin
            let m1_te = IdentMap.find m1.content gte.gtenv_extern in
            match IdentMap.find_opt id.content m1_te.tenv_constr_types with
            | Some _ -> m1.content
            | None -> mname_of_ident imports' gte gx id
          end
      end

let transl_var_name (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (x : cident) : Syntax.ident =
  let x' =
    match x with
    | IdSimple x ->
        let prefix =
          match IdentMap.find_opt x.content lx with
          | Some (_, VarLocal) -> "u"
          | Some (_, VarParam) -> "p"
          | None -> begin
              match IdentMap.find_opt x.content gx.gx_local with
              | Some _ -> !curr_mname
              | None -> mname_of_ident imports gte gx x
            end
        in
        sprintf "%s_%s" prefix x.content
    | IdPrefixed (mname, x) -> Printf.sprintf "%s_%s" mname.content x.content
  in
  PrintUtils.ident_of_string x'

let transl_constr_name (imports : ident list) (gte : gtenv) (gx : gcontext)
    (x : cident) : Syntax.ident =
  let x' =
    match x with
    | IdSimple x ->
        let prefix =
          begin
            match
              IdentMap.find_opt x.content gte.gtenv_local.tenv_constr_types
            with
            | Some _ -> !curr_mname
            | None -> mname_of_ident imports gte gx x
          end
        in
        sprintf "%s_%s" prefix x.content
    | IdPrefixed (mname, x) -> Printf.sprintf "%s_%s" mname.content x.content
  in
  PrintUtils.ident_of_string x'

let transl_pattern (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (p : pattern) : Benum.pattern =
  match p with
  | PIdent cid ->
      let id = transl_constr_name imports gte gx cid in
      Benum.PIdent id
  | PWildcard _ -> Benum.PWildcard

let transl_field_name (f : ident) : Syntax.ident =
  PrintUtils.ident_of_string f.content

let rec transl_btyp (ty : btyp) : Types.btyp =
  match ty with
  | BBool -> Types.BBool
  | BInt32 s -> Types.BInt32 s
  | BInt64 s -> Types.BInt64 s
  | BArray ta -> Types.BArray (transl_btyp ta)
  | BEnum (mname, eid) ->
      let eid' = PrintUtils.ident_of_string (sprintf "%s_%s" mname eid) in
      Types.BEnum eid'
  | BRecord (mname, rid) ->
      let rid' = PrintUtils.ident_of_string (sprintf "%s_%s" mname rid) in
      Types.BRecord rid'
  | BAbs (mname, tid) ->
      let tid' = PrintUtils.ident_of_string (sprintf "%s_%s" mname tid) in
      Types.BAbs tid'
  | BFun (tparams, tret) ->
      let tparams' = List.map transl_btyp tparams in
      let tret' = transl_btyp tret in
      Types.BFun (tparams', tret')

let arr_index_btyp : btyp ref =
  ref (if Archi.ptr64 then BInt64 Types.Unsigned else BInt32 Types.Unsigned)

let set_arr_index_btyp (arch : Target.archi) : unit =
  arr_index_btyp :=
    match arch with
    | Target.Ptr32 -> BInt32 Types.Unsigned
    | Target.Ptr64 -> BInt64 Types.Unsigned

let check_expected_typ (texp : expected_typ) (ty : btyp) (r : 'a) : 'a =
  match texp with
  | Expect_typ t ->
      if t = ty then r else error (Type_mismatch (texp, Current_typ ty))
  | Expect_int -> begin
      match ty with
      | BInt32 _ | BInt64 _ -> r
      | _ -> error (Type_mismatch (texp, Current_typ ty))
    end
  | Expect_int_or_bool -> begin
      match ty with
      | BBool | BInt32 _ | BInt64 _ -> r
      | _ -> error (Type_mismatch (texp, Current_typ ty))
    end
  | Expect_int_or_bool_or_enum -> begin
      match ty with
      | BBool | BInt32 _ | BInt64 _ | BEnum _ -> r
      | _ -> error (Type_mismatch (texp, Current_typ ty))
    end
  | Expect_array -> begin
      match ty with
      | BArray _ -> r
      | _ -> error (Type_mismatch (texp, Current_typ ty))
    end
  | Expect_enum -> begin
      match ty with
      | BEnum _ -> r
      | _ -> error (Type_mismatch (texp, Current_typ ty))
    end
  | Expect_record -> begin
      match ty with
      | BRecord _ -> r
      | _ -> error (Type_mismatch (texp, Current_typ ty))
    end
  | Expect_function -> begin
      match ty with
      | BFun _ -> r
      | _ -> error (Type_mismatch (texp, Current_typ ty))
    end

let typecheck_pattern (imports : ident list) (gte : gtenv) (gx : gcontext)
    (mname : string) (eid : string) (x : pattern) (elems : string list)
    (unmatched : string list) : string list =
  let xloc =
    match x with
    | PIdent cid -> loc_of_cident cid
    | PWildcard loc -> loc
  in
  if unmatched = [] then
    error (Redundant_pattern (pattern_to_string x)) ~loc:(Some xloc)
  else
    match x with
    | PWildcard _ -> []
    | PIdent x ->
        let xstr =
          match x with
          | IdSimple id | IdPrefixed (_, id) -> id.content
        in
        let xstr_full = cident_to_string x in
        (* We need to check that the pattern:
         - has the correct enum type;
         - corresponds to a constructor of that type;
         - has not already been matched. *)
        let tx =
          try gtenv_get_constr_typ imports gte x
          with Error (Undefined_ident _, loc) ->
            error (Undefined_enum_elem (xstr_full, BEnum (mname, eid))) ~loc
        in
        if tx = BEnum (mname, eid) then
          if List.mem xstr elems then
            if List.mem xstr unmatched then
              List0.remove String.equal xstr unmatched
            else error (Redundant_pattern xstr_full) ~loc:(Some xloc)
          else error (Undefined_enum_elem (xstr_full, BEnum (mname, eid)))
        else
          error
            (Type_mismatch (Expect_typ (BEnum (mname, eid)), Current_typ tx))
            ~loc:(Some xloc)

let rec typecheck_raw_expr (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (e : raw_expr) : Barocq.expr * btyp =
  match e with
  | ETrue -> (Barocq.ETrue, BBool)
  | EFalse -> (Barocq.EFalse, BBool)
  | EInt32 (i, s) -> (Barocq.EInt32 (i, s), BInt32 s)
  | EInt64 (i, s) -> (Barocq.EInt64 (i, s), BInt64 s)
  | EConstr x ->
      let ty = typof_constr imports gte x in
      let x' = transl_constr_name imports gte gx x in
      (Barocq.EConstr x', ty)
  | EVar x ->
      let ty = typof_var imports gx lx x in
      let x' = transl_var_name imports gte gx lx x in
      (Barocq.EVar x', ty)
  | ECast (e1, sty) ->
      let ty = styp_to_btyp imports gte sty in
      let e1', t1 = typecheck_expr imports gte gx lx e1 in
      (Barocq.ECast (e1', transl_btyp ty), typecheck_cast t1 ty)
  | EUnaryOp (op, e1) ->
      let texp =
        match op with
        | UopNeg | UopNotint | UopPlus -> Expect_int
        | UopNotbool -> Expect_typ BBool
      in
      let e1', t1 = typecheck_expr_expecting imports gte gx lx e1 texp in
      let t = typecheck_unary_op op t1 in
      (Barocq.EUnaryOp (op, e1'), t)
  | EBinaryOp (op, e1, e2) ->
      let texp =
        match op with
        | BopAndbool | BopOrbool | BopXorbool -> Expect_typ BBool
        | BopEq | BopNeq -> Expect_int_or_bool_or_enum
        | _ -> Expect_int
      in
      let e1', t1 = typecheck_expr_expecting imports gte gx lx e1 texp in
      let e2', t2 =
        typecheck_expr_expecting imports gte gx lx e2 (Expect_typ t1)
      in
      let t = typecheck_binary_op op t1 t2 in
      (Barocq.EBinaryOp (op, e1', e2'), t)
  | EArrayGet (e1, e2) ->
      let e1', t1 =
        typecheck_expr_expecting imports gte gx lx e1 Expect_array
      in
      let e2', _ =
        typecheck_expr_expecting
          imports
          gte
          gx
          lx
          e2
          (Expect_typ !arr_index_btyp)
      in
      begin
        match t1 with
        | BArray ta -> (Barocq.EArrayGet (e1', e2'), ta)
        | _ -> assert false
      end
  | EArraySet (e1, e2, e3) ->
      let e1', t1 =
        typecheck_expr_expecting imports gte gx lx e1 Expect_array
      in
      let e2', _ =
        typecheck_expr_expecting
          imports
          gte
          gx
          lx
          e2
          (Expect_typ !arr_index_btyp)
      in
      begin
        match t1 with
        | BArray ta ->
            let e3', _ =
              typecheck_expr_expecting imports gte gx lx e3 (Expect_typ ta)
            in
            (Barocq.EArraySet (e1', e2', e3'), t1)
        | _ -> assert false
      end
  | ERecordProj (e1, f) ->
      let e1', t1 =
        typecheck_expr_expecting imports gte gx lx e1 Expect_record
      in
      begin
        match t1 with
        | BRecord (mname, rid) ->
            let f' = transl_field_name f in
            let t = typecheck_record_proj gte mname rid f in
            (Barocq.ERecordProj (e1', f'), t)
        | _ -> assert false
      end
  | ERecordUpdate (e1, le) -> typecheck_record_update imports gte gx lx e1 le
  | EApp (e1, args) ->
      let e1', t1 =
        typecheck_expr_expecting imports gte gx lx e1 Expect_function
      in
      begin
        match t1 with
        | BFun (tparams, tret) ->
            let args', t = typecheck_app imports gte gx lx tparams tret args in
            (Barocq.EApp (e1', args'), t)
        | _ -> assert false
      end
  | EIfThenElse (e1, e2, e3) ->
      let e1', _ =
        typecheck_expr_expecting imports gte gx lx e1 (Expect_typ BBool)
      in
      let e2', t2 = typecheck_expr imports gte gx lx e2 in
      let e3', _ =
        typecheck_expr_expecting imports gte gx lx e3 (Expect_typ t2)
      in
      (Barocq.EIfThenElse (e1', e2', e3'), t2)
  | EMatch (e1, cases) ->
      let e1', t1 = typecheck_expr_expecting imports gte gx lx e1 Expect_enum in
      begin
        match t1 with
        | BEnum (mname, eid) ->
            let cases', t = typecheck_match imports gte gx lx mname eid cases in
            (Barocq.EMatch (e1', cases'), t)
        | _ -> assert false
      end
  | ELetIn (le, e) -> begin
      match le with
      | [] -> assert false
      | _ -> typecheck_let_in imports gte gx lx le e
    end

and typecheck_expr (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (e : expr) : Barocq.expr * btyp =
  try typecheck_raw_expr imports gte gx lx e.content
  with Error (cause, loc) -> update_error_loc cause loc e

and typecheck_expr_expecting (imports : ident list) (gte : gtenv)
    (gx : gcontext) (lx : lcontext) (e : expr) (texp : expected_typ) :
    Barocq.expr * btyp =
  try
    let ((e', ty) as r) = typecheck_raw_expr imports gte gx lx e.content in
    check_expected_typ texp ty r
  with Error (cause, loc) -> update_error_loc cause loc e

and typecheck_record_update (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (e : expr) (le : (ident * expr) list) : Barocq.expr * btyp =
  let check_one_update (st_mname : string) (st_sid : string) ste f e =
    let f' = transl_field_name f in
    let tf = typecheck_record_proj gte st_mname st_sid f in
    let e', _ = typecheck_expr_expecting imports gte gx lx e (Expect_typ tf) in
    (Barocq.ERecordUpdate (ste, f', e'), BRecord (st_mname, st_sid))
  in
  let rec check_update_list (st_mname : string) (st_sid : string)
      (e : Barocq.expr) (le : (ident * expr) list) : Barocq.expr * btyp =
    match le with
    | [] -> assert false
    | (fi, ei) :: [] -> check_one_update st_mname st_sid e fi ei
    | (fi, ei) :: le' ->
        let bei, ti = check_one_update st_mname st_sid e fi ei in
        check_update_list st_mname st_sid bei le'
  in
  let e', t = typecheck_expr_expecting imports gte gx lx e Expect_record in
  match t with
  | BRecord (mname, rid) -> check_update_list mname rid e' le
  | _ -> assert false

and typecheck_app (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (tparams : btyp list) (tret : btyp) (args : expr list) :
    Barocq.expr list * btyp =
  let arity = List.length tparams in
  let nbargs = List.length args in
  let rec aux tparams args =
    match (tparams, args) with
    | [], [] -> ([], tret)
    | tp :: tparams', a :: args' ->
        let a', _ =
          typecheck_expr_expecting imports gte gx lx a (Expect_typ tp)
        in
        let bargs, t = aux tparams' args' in
        (a' :: bargs, t)
    | _, _ -> error (Wrong_argument_number (arity, nbargs))
  in
  aux tparams args

and typecheck_match (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (mname : string) (eid : string)
    (cases : (pattern * expr) list) : (Benum.pattern * Barocq.expr) list * btyp
    =
  let rec aux (elems : string list) (unmatched : string list)
      (cases : (pattern * expr) list) (tr : btyp) :
      (Benum.pattern * Barocq.expr) list =
    match cases with
    | [] ->
        if unmatched <> [] then
          let u = List.hd unmatched in
          let u =
            if mname != !curr_mname then sprintf "%s::%s" mname u else u
          in
          error (Non_exhaustive_pattern_matching u)
        else []
    | (x, ex) :: cases' ->
        let unmatched' =
          typecheck_pattern imports gte gx mname eid x elems unmatched
        in
        let ber = aux elems unmatched' cases' tr in
        let bex, tx =
          typecheck_expr_expecting imports gte gx lx ex (Expect_typ tr)
        in
        (transl_pattern imports gte gx lx x, bex) :: ber
  in
  let te =
    if mname = !curr_mname then gte.gtenv_local
    else
      match IdentMap.find_opt mname gte.gtenv_extern with
      | Some te -> te
      | None -> assert false (* Ill-typed environment *)
  in
  match IdentMap.find_opt eid te.tenv_defs with
  | Some (TdEnum elems) -> begin
      match cases with
      | [] -> assert false (* Ill-parsed program *)
      | (x, ex) :: cases' ->
          let unmatched =
            typecheck_pattern imports gte gx mname eid x elems elems
          in
          let bex, tx = typecheck_expr imports gte gx lx ex in
          let ber = aux elems unmatched cases' tx in
          ((transl_pattern imports gte gx lx x, bex) :: ber, tx)
    end
  | _ -> assert false

and typecheck_let_in (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (le : (ident * expr) list) (e : expr) : Barocq.expr * btyp =
  match le with
  | [] ->
      let e', t = typecheck_expr imports gte gx lx e in
      (e', t)
  | (xi, ei) :: le' ->
      let xi' = PrintUtils.ident_of_string ("u_" ^ xi.content) in
      let ei', ti = typecheck_expr imports gte gx lx ei in
      let lx' = lcontext_update lx xi ti in
      let er, tr = typecheck_let_in imports gte gx lx' le' e in
      (Barocq.ELetIn (xi', ei', er), tr)

let cvalue_to_literal (v : cvalue) : Syntax.literal =
  match v with
  | VBool true -> Syntax.LTrue
  | VBool false -> Syntax.LFalse
  | VInt32 (i, s) -> Syntax.LInt32 (i, s)
  | VInt64 (i, s) -> Syntax.LInt64 (i, s)
  | _ -> assert false

let rec typecheck_const (imports : ident list) (gte : gtenv) (ce : cenv)
    (gx : gcontext) (ty : btyp) (c : const) : Syntax.literal * btyp =
  try
    match (c.content, ty) with
    | ( ( CTrue
        | CFalse
        | CInt32 _
        | CInt64 _
        | CVar _
        | CUnop _
        | CBinop _
        | CCast _ ),
        _ ) -> typecheck_const_op_expecting imports gte ce gx c (Expect_typ ty)
    | CArray a, BArray ta ->
        let a' =
          List.map (fun c -> fst (typecheck_const imports gte ce gx ta c)) a
        in
        (Syntax.LArray a', ty)
    | CRecord rc, BRecord (mname, rid) ->
        let fields, rid' =
          let te, rid' =
            if mname <> !curr_mname then
              match IdentMap.find_opt mname gte.gtenv_extern with
              | Some te -> (te, compose_idents mname rid)
              | None -> assert false (* Ill-typed environment *)
            else (gte.gtenv_local, rid)
          in
          let fields =
            match IdentMap.find_opt rid te.tenv_defs with
            | Some (TdRecord fields) -> fields
            | _ -> assert false (* Ill-typed environment *)
          in
          (fields, rid')
        in
        let rc' = typecheck_const_record imports gte ce gx rid' rc fields in
        let rid =
          match transl_btyp ty with
          | Types.BRecord rid -> rid
          | _ -> assert false
        in
        (Syntax.LRecord (rc', rid), ty)
    | CArray _, _ -> error (Type_mismatch (Expect_typ ty, Current_array))
    | CRecord _, _ -> error (Type_mismatch (Expect_typ ty, Current_record))
  with Error (cause, loc) -> update_error_loc cause loc c

and typecheck_const_op (imports : ident list) (gte : gtenv) (ce : cenv)
    (gx : gcontext) (c : const) : Syntax.literal * btyp =
  let t =
    match c.content with
    | CTrue -> BBool
    | CFalse -> BBool
    | CInt32 (_, s) -> BInt32 s
    | CInt64 (_, s) -> BInt64 s
    | CVar x -> gcontext_get imports gx x
    | CUnop (op, c1) ->
        let texp =
          match op with
          | UopNeg | UopNotint | UopPlus -> Expect_int
          | UopNotbool -> Expect_typ BBool
        in
        let _, t1 = typecheck_const_op_expecting imports gte ce gx c1 texp in
        typecheck_unary_op op t1
    | CBinop (op, c1, c2) ->
        let texp =
          match op with
          | BopAndbool | BopOrbool | BopXorbool -> Expect_typ BBool
          | BopEq | BopNeq -> Expect_int_or_bool
          | _ -> Expect_int
        in
        let _, t1 = typecheck_const_op_expecting imports gte ce gx c1 texp in
        let _, t2 =
          typecheck_const_op_expecting imports gte ce gx c2 (Expect_typ t1)
        in
        typecheck_binary_op op t1 t2
    | CCast (c1, ty) ->
        let ty' = styp_to_btyp imports gte ty in
        let _, t1 = typecheck_const_op imports gte ce gx c1 in
        typecheck_cast t1 ty'
    | _ -> assert false
  in
  let v = eval_const imports gte ce c in
  (cvalue_to_literal v, t)

and typecheck_const_op_expecting (imports : ident list) (gte : gtenv)
    (ce : cenv) (gx : gcontext) (c : const) (texp : expected_typ) :
    Syntax.literal * btyp =
  try
    let ((c', ty) as r) = typecheck_const_op imports gte ce gx c in
    check_expected_typ texp ty r
  with Error (cause, loc) -> update_error_loc cause loc c

and typecheck_const_record (imports : ident list) (gte : gtenv) (ce : cenv)
    (gx : gcontext) (rid : string) (rc : (ident * const) list)
    (fields : (string * btyp) list) : (Syntax.ident * Syntax.literal) list =
  match rc with
  | [] ->
      if List.length fields = 0 then []
      else error (Missing_record_fields (List.map fst fields))
  | (fname, lit) :: rc' -> begin
      match List.assoc_opt fname.content fields with
      | Some ftyp ->
          let c', _ = typecheck_const imports gte ce gx ftyp lit in
          let r =
            typecheck_const_record
              imports
              gte
              ce
              gx
              rid
              rc'
              (List.remove_assoc fname.content fields)
          in
          let fname' = transl_field_name fname in
          (fname', c') :: r
      | None -> error (Unknown_field (fname.content, rid)) ~loc:(Some fname)
    end

let find_duplicate_ident (l : ident list) : ident option =
  let rec aux (l : ident list) =
    match l with
    | [] -> None
    | id :: l' ->
        if List.exists (fun (x : ident) -> x.content = id.content) l' then
          Some id
        else aux l'
  in
  aux (List.rev l)

let typecheck_function (imports : ident list) (gte : gtenv) (gx : gcontext)
    (x : ident) (f : func) : Barocq.coq_function * btyp =
  match find_duplicate_ident (List.map fst f.fn_params) with
  | Some p -> error (Duplicate_param (p.content, x.content)) ~loc:(Some p)
  | None ->
      let tret = styp_to_btyp imports gte f.fn_return in
      let params =
        List.map
          (fun ((pid, ptyp) : ident * styp) ->
            (pid.content, styp_to_btyp imports gte ptyp))
          f.fn_params
      in
      let ty = BFun (List.map snd params, tret) in
      let lx =
        List.fold_left
          (fun acc (pid, ptyp) -> IdentMap.add pid (ptyp, VarParam) acc)
          lcontext_empty
          params
      in
      let body, tb =
        typecheck_expr_expecting imports gte gx lx f.fn_body (Expect_typ tret)
      in
      let bparams =
        List.map
          (fun (pid, ptyp) ->
            let pid' = PrintUtils.ident_of_string ("p_" ^ pid) in
            let ptyp' = transl_btyp ptyp in
            (pid', ptyp'))
          params
      in
      let bf =
        {
          Syntax.fn_return = transl_btyp tret;
          Syntax.fn_params = bparams;
          Syntax.fn_body = body;
        }
      in
      (bf, ty)

let transl_globdef_name (mname : string) (x : ident) : Syntax.ident =
  PrintUtils.ident_of_string (sprintf "%s_%s" mname x.content)

let typecheck_abs_function (x : ident) (tparams : (param_attr * btyp) list)
    (tret : btyp) : btyp =
  let rec check_write_param tparams tret write =
    match tparams with
    | [] -> begin
        match write with
        | Some tw ->
            if tw = tret then ()
            else
              error
                (Mismatch_type_param_write (x.content, tw, tret))
                ~loc:(Some x)
        | None ->
            if btyp_is_prim tret then ()
            else error (Missing_param_write (x.content, tret)) ~loc:(Some x)
      end
    | (attr, t) :: tparams' -> begin
        match attr with
        | AttrWrite ->
            if write <> None then
              error (Too_many_param_write x.content) ~loc:(Some x)
            else check_write_param tparams' tret (Some t)
        | _ -> check_write_param tparams' tret write
      end
  in
  let _ = check_write_param tparams tret None in
  BFun (List.map snd tparams, tret)

let typecheck_type_def (imports : ident list) (gte : gtenv) (ce : cenv)
    (gx : gcontext) (tid : ident) (td : SurfaceAST.type_def) :
    Barocq.globdef option * gtenv * cenv * gcontext =
  match td with
  | SurfaceAST.TdEnum elems -> begin
      match find_duplicate_ident elems with
      | Some elem -> error (Already_defined_glob elem.content) ~loc:(Some elem)
      | _ ->
          let gte' =
            gtenv_update_local_enums
              gte
              tid
              (List.map (fun e -> e.content) elems)
          in
          (* Every enum constructor is added as a global symbol in the type environment *)
          let gte' =
            List.fold_left
              (fun acc e -> gtenv_update_local_constr_types acc e tid.content)
              gte'
              elems
          in
          (* Every enum constructor is added in the constant environment
             (using them in constant definitions is not supported though). *)
          let ce' =
            List.fold_left (fun acc e -> cenv_update_local acc e VEnum) ce elems
          in
          let bid = transl_globdef_name !curr_mname tid in
          let belems = List.map (transl_globdef_name !curr_mname) elems in
          (Some (Barocq.DefType (bid, Types.Adt_enum belems)), gte', ce', gx)
    end
  | SurfaceAST.TdRecord fields -> begin
      match find_duplicate_ident (List.map fst fields) with
      | Some fname ->
          error
            (Duplicate_record_field (fname.content, tid.content))
            ~loc:(Some fname)
      | None ->
          let fields' =
            List.map
              (fun ((fname, ftyp) : ident * styp) ->
                (fname.content, styp_to_btyp imports gte ftyp))
              fields
          in
          let bid = transl_globdef_name !curr_mname tid in
          let bfields =
            List.map
              (fun (fname, ftyp) ->
                let fname' = PrintUtils.ident_of_string fname in
                let ftyp' = transl_btyp ftyp in
                (fname', ftyp'))
              fields'
          in
          let gte' = gtenv_update_local_records gte tid fields' in
          (Some (Barocq.DefType (bid, Types.Adt_record bfields)), gte', ce, gx)
    end
  | SurfaceAST.TdAlias ty ->
      let ty = styp_to_btyp imports gte ty in
      (None, gtenv_update_local_aliases gte tid ty, ce, gx)

let typecheck_globdef (imports : ident list) (gte : gtenv) (ce : cenv)
    (gx : gcontext) (def : globdef) :
    Barocq.globdef option * gtenv * cenv * gcontext =
  match def with
  | DefType (tid, td) -> typecheck_type_def imports gte ce gx tid td
  | DefConst (id, c, sty) ->
      let ty = styp_to_btyp imports gte sty in
      let l', _ = typecheck_const imports gte ce gx ty c in
      let gx' = gcontext_update_local gte gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      let bty = transl_btyp ty in
      let ce' =
        let v =
          if btyp_is_prim ty then eval_const imports gte ce c else VNotprim
        in
        cenv_update_local ce id v
      in
      (Some (Barocq.DefConst (bid, l', bty)), gte, ce', gx')
  | DefFun (id, f) ->
      let bf, ty = typecheck_function imports gte gx id f in
      let gx' = gcontext_update_local gte gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      (Some (Barocq.DefFun (bid, bf)), gte, ce, gx')
  | DeclType (tid, tk) ->
      let gte' = gtenv_update_local_abstracts gte tid in
      let bid = transl_globdef_name !curr_mname tid in
      (Some (Barocq.DeclType (bid, tk)), gte', ce, gx)
  | DeclConst (id, sty) ->
      let ty = styp_to_btyp imports gte sty in
      let gx' = gcontext_update_local gte gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      let bty = transl_btyp ty in
      let ce' = cenv_update_local ce id VAbs in
      (Some (Barocq.DeclConst (bid, bty)), gte, ce', gx')
  | DeclFun (id, tparams, tret) ->
      let tparams' =
        List.map
          (fun (attr, sty) ->
            let bty = styp_to_btyp imports gte sty in
            (attr, bty))
          tparams
      in
      let tret' = styp_to_btyp imports gte tret in
      let ty = typecheck_abs_function id tparams' tret' in
      let gx' = gcontext_update_local gte gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      let btparams =
        List.map
          (fun (attr, bty) ->
            let bty' = transl_btyp bty in
            (attr, bty'))
          tparams'
      in
      let btret = transl_btyp tret' in
      (Some (Barocq.DeclFun (bid, btparams, btret)), gte, ce, gx')

let rec typecheck_imports (imports : ident list) (gx : gcontext) : unit =
  match imports with
  | [] -> ()
  | m1 :: imports' -> begin
      match IdentMap.find_opt m1.content gx.gx_extern with
      | Some _ -> typecheck_imports imports' gx
      | None -> error (Module_not_found m1.content) ~loc:(Some m1)
    end

let typecheck_modul (gte : gtenv) (ce : cenv) (gx : gcontext) (md : modul) :
    Barocq.program * gtenv * cenv * gcontext =
  let mname = md.md_name in
  match IdentMap.find_opt mname.content gx.gx_extern with
  | Some _ -> error (Duplicate_module mname.content) ~loc:(Some mname)
  | _ ->
      curr_mname := md.md_name.content;
      (* Initialization of gte and gtx *)
      let gte = { gte with gtenv_local = tenv_empty } in
      let gx = { gx with gx_local = IdentMap.empty } in
      (* Type checking *)
      typecheck_imports md.md_imports gx;
      let defs, gte, ce, gx =
        List.fold_left
          (fun (acc_defs, acc_gte, acc_ce, acc_gx) def ->
            let d, gte, ce, gx =
              typecheck_globdef md.md_imports acc_gte acc_ce acc_gx def
            in
            let acc_defs' =
              match d with
              | Some d -> d :: acc_defs
              | None -> acc_defs
            in
            (acc_defs', gte, ce, gx))
          ([], gte, ce, gx)
          md.md_defs
      in
      (* Once the type checking is finished, we update the global environment and
         global context to add the definitions of the new module. *)
      let gte' =
        {
          gtenv_local = tenv_empty;
          gtenv_extern =
            IdentMap.add md.md_name.content gte.gtenv_local gte.gtenv_extern;
        }
      in
      let ce' =
        {
          cenv_local = IdentMap.empty;
          cenv_extern =
            IdentMap.add md.md_name.content ce.cenv_local ce.cenv_extern;
        }
      in
      let gx' =
        {
          gx_local = IdentMap.empty;
          gx_extern = IdentMap.add md.md_name.content gx.gx_local gx.gx_extern;
        }
      in
      let bprog = List.rev defs in
      (bprog, gte', ce', gx')

let typecheck_program (prog : program) : Barocq.program =
  let bprog, _, _, _ =
    List.fold_left
      (fun (acc_prog, acc_gte, acc_ce, acc_gx) md ->
        let bprog, gte, ce, gx = typecheck_modul acc_gte acc_ce acc_gx md in
        let bprog' = List.append acc_prog bprog in
        (bprog', gte, ce, gx))
      ([], gtenv_empty, cenv_empty, gcontext_empty)
      prog
  in
  bprog

let typecheck_command (imports : ident list) (gte : gtenv) (ce : cenv)
    (gx : gcontext) (cmd : command) :
    Barocq.command option * gtenv * cenv * gcontext =
  match cmd with
  | CmdDef d ->
      let bd, gte', ce', gx' = typecheck_globdef imports gte ce gx d in
      begin
        match bd with
        | Some bd -> (Some (Barocq.CmdDef bd), gte', ce', gx')
        | None -> (None, gte', ce', gx')
      end
  | CmdExpr e ->
      let be, _ = typecheck_expr imports gte gx lcontext_empty e in
      (Some (Barocq.CmdExpr be), gte, ce, gx)

let typecheck_imodul (gte : gtenv) (ce : cenv) (gx : gcontext) (imd : imodul) :
    Barocq.iprogram * gtenv * cenv * gcontext =
  let mname = imd.imd_name in
  match IdentMap.find_opt mname.content gx.gx_extern with
  | Some _ -> error (Duplicate_module mname.content) ~loc:(Some mname)
  | _ ->
      curr_mname := imd.imd_name.content;
      (* Initialization of gte and gtx *)
      let gte = { gte with gtenv_local = tenv_empty } in
      let gx = { gx with gx_local = IdentMap.empty } in
      typecheck_imports imd.imd_imports gx;
      (* Type checking *)
      let cmds, gte, ce, gx =
        List.fold_left
          (fun (acc_cmds, acc_gte, acc_ce, acc_gx) cmd ->
            let cmd, gte, ce, gx =
              typecheck_command imd.imd_imports acc_gte acc_ce acc_gx cmd
            in
            let acc_defs' =
              match cmd with
              | Some cmd -> cmd :: acc_cmds
              | None -> acc_cmds
            in
            (acc_defs', gte, ce, gx))
          ([], gte, ce, gx)
          imd.imd_cmds
      in
      (* Once the type checking is finished, we update the global environment and
         global context to add the definitions of the new module. *)
      let gte' =
        {
          gtenv_local = tenv_empty;
          gtenv_extern =
            IdentMap.add imd.imd_name.content gte.gtenv_local gte.gtenv_extern;
        }
      in
      let ce' =
        {
          cenv_local = IdentMap.empty;
          cenv_extern =
            IdentMap.add imd.imd_name.content ce.cenv_local ce.cenv_extern;
        }
      in
      let gx' =
        {
          gx_local = IdentMap.empty;
          gx_extern = IdentMap.add imd.imd_name.content gx.gx_local gx.gx_extern;
        }
      in
      let bprog = List.rev cmds in
      (bprog, gte', ce', gx')

type gdef_kind =
  | KType
  | KDecl
  | KDef

let kind_of_gdef gd =
  match gd with
  | Barocq.DefType _ | Barocq.DeclType _ -> KType
  | Barocq.DeclConst _ | Barocq.DeclFun _ -> KDecl
  | Barocq.DefConst _ | Barocq.DefFun _ -> KDef

let kind_of_command c1 =
  match c1 with
  | Barocq.CmdExpr _ -> None
  | Barocq.CmdDef d -> Some (kind_of_gdef d)

(** [sort_iprogam] puts type declaration and definition first, declaration of
    function followed by definition of function *)
let sort_iprogam p =
  let cmp_gdef gd1 gd2 =
    match (kind_of_command gd1, kind_of_command gd2) with
    | None, None -> 0
    | Some _, None -> -1
    | None, Some _ -> 1
    | Some gd1, Some gd2 -> (
        match (gd1, gd2) with
        | KType, KType -> 0
        | KType, _ -> -1
        | _, KType -> 1
        | KDecl, KDecl -> 0
        | KDecl, KDef -> -1
        | KDef, KDecl -> 1
        | KDef, KDef -> 0)
  in
  List.stable_sort cmp_gdef p

let typecheck_iprogram (iprog : iprogram) : Barocq.iprogram =
  let biprog, _, _, gx =
    List.fold_left
      (fun (acc_iprog, acc_gte, acc_ce, acc_gx) md ->
        let biprog, gte, ce, gx = typecheck_imodul acc_gte acc_ce acc_gx md in
        let biprog' = List.append acc_iprog biprog in
        (biprog', gte, ce, gx))
      ([], gtenv_empty, cenv_empty, gcontext_empty)
      iprog
  in
  sort_iprogam biprog
