open Printf
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
  | BStruct of string * string
  | BAbs of string * string
  | BFun of btyp list * btyp

type expected_typ =
  | Expect_typ of btyp
  | Expect_int
  | Expect_int_or_bool
  | Expect_array
  | Expect_struct
  | Expect_function

type current_typ =
  | Current_typ of btyp
  | Current_array
  | Current_struct

type error_cause =
  | Type_mismatch of expected_typ * current_typ
  | Forbidden_cast of btyp * btyp
  | Undefined_ident of string
  | Undefined_type of string
  | Unknown_field of string * string
  | Module_not_found of string
  | Wrong_argument_number of int * int
  | Variable_shadowing_diff_type of string * btyp
  | Already_defined_type of string
  | Already_defined_glob of string
  | Duplicated_struct_field of string * string
  | Duplicated_param of string * string
  | Duplicated_module of string
  | Missing_struct_fields of string list
  | Missing_param_write of string * btyp
  | Too_many_param_write of string
  | Mismatch_type_param_write of string * btyp * btyp

exception Error of error_cause * unit Location.t option

let rec btyp_to_string (ty : btyp) : string =
  match ty with
  | BBool -> "bool"
  | BInt32 Types.Signed -> "i32"
  | BInt32 Types.Unsigned -> "u32"
  | BInt64 Types.Signed -> "i64"
  | BInt64 Types.Unsigned -> "u64"
  | BArray (BArray t) -> sprintf "array (%s)" (btyp_to_string t)
  | BArray t -> sprintf "array %s" (btyp_to_string t)
  | BStruct (mname, cid) | BAbs (mname, cid) ->
      if mname = !curr_mname then cid else sprintf "%s::%s" mname cid
  | BFun (tparams, tret) ->
      PrintTypes.funtyp_to_string btyp_to_string tparams tret

let btyp_is_prim (ty : btyp) : bool =
  match ty with
  | BBool | BInt32 _ | BInt64 _ -> true
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
        | Current_struct -> sprintf "this expression is a struct"
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
        | Expect_array -> sprintf "but an array was expected"
        | Expect_struct -> sprintf "but a struct was expected"
        | Expect_function -> sprintf "but a function was expected"
      in
      sprintf "%s %s" prefix suffix
  | Unknown_field (f, st) ->
      sprintf "field %s is not defined for struct type %s" f st
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
      sprintf "global identifier %s cannot be redefined" gid
  | Undefined_type tid -> sprintf "type %s is not defined" tid
  | Duplicated_struct_field (fname, sid) ->
      sprintf "field %s is duplicated in struct type %s" fname sid
  | Duplicated_param (p, f) ->
      sprintf "parameter %s is duplicated in the definition of function %s" p f
  | Forbidden_cast (t1, t2) ->
      sprintf
        "cannot cast a value of type %s to a value of type %s"
        (btyp_to_string t1)
        (btyp_to_string t2)
  | Module_not_found mname -> sprintf "module %s not found" mname
  | Duplicated_module mname ->
      sprintf "a module with name %s already exists" mname
  | Missing_struct_fields mfields ->
      sprintf
        "the following struct fields are missing: %s"
        (PrintCommon.list_to_string "" "" ", " (fun x -> x) mfields)
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

type senv = (string * btyp) list IdentMap.t

type tenv = {
  tenv_aliases : btyp IdentMap.t;
  tenv_structs : senv;
  tenv_abstracts : IdentSet.t;
}

let tenv_empty =
  {
    tenv_aliases = IdentMap.empty;
    tenv_structs = IdentMap.empty;
    tenv_abstracts = IdentSet.empty;
  }

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

let tenv_get (mname : string) (te : tenv) (tid : ident) : btyp option =
  match IdentMap.find_opt tid.content te.tenv_aliases with
  | Some ty -> Some ty
  | None -> begin
      match IdentMap.find_opt tid.content te.tenv_structs with
      | Some _ -> Some (BStruct (mname, tid.content))
      | None -> begin
          match IdentSet.find_opt tid.content te.tenv_abstracts with
          | Some _ -> Some (BAbs (mname, tid.content))
          | None -> None
        end
    end

let gtenv_get (imports : ident list) (gte : gtenv) (cid : cident) : btyp =
  let gtenv_get_prefixed (mname : ident) (tid : ident) : btyp option =
    match IdentMap.find_opt mname.content gte.gtenv_extern with
    | Some te -> tenv_get mname.content te tid
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
      match tenv_get !curr_mname gte.gtenv_local tid with
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

let gtenv_get_fields (imports : ident list) (gte : gtenv) (cid : cident) :
    (string * btyp) list =
  let ty = gtenv_get imports gte cid in
  match ty with
  | BStruct (mname, sid) ->
      let se, sid' =
        if mname = !curr_mname then (gte.gtenv_local.tenv_structs, sid)
        else
          match IdentMap.find_opt mname gte.gtenv_extern with
          | Some te -> (te.tenv_structs, compose_idents mname sid)
          | None -> assert false (* Ill-typed environment *)
      in
      begin
        match IdentMap.find_opt sid se with
        | Some fields -> fields
        | _ -> assert false (* Ill-typed environment *)
      end
  | _ -> error (Type_mismatch (Expect_struct, Current_typ ty))

let is_local_type_defined (te : tenv) (tid : string) : bool =
  match IdentMap.find_opt tid te.tenv_aliases with
  | Some _ -> true
  | None -> begin
      match IdentMap.find_opt tid te.tenv_structs with
      | Some _ -> true
      | None -> false
    end

let tenv_update_aliases (te : tenv) (alias : ident) (ty : btyp) : tenv =
  if is_local_type_defined te alias.content then
    error (Already_defined_type alias.content) ~loc:(Some alias)
  else { te with tenv_aliases = IdentMap.add alias.content ty te.tenv_aliases }

let tenv_update_structs (te : tenv) (sid : ident)
    (fields : (string * btyp) list) : tenv =
  if is_local_type_defined te sid.content then
    error (Already_defined_type sid.content) ~loc:(Some sid)
  else
    { te with tenv_structs = IdentMap.add sid.content fields te.tenv_structs }

let tenv_update_abstracts (te : tenv) (tid : ident) : tenv =
  if is_local_type_defined te tid.content then
    error (Already_defined_type tid.content) ~loc:(Some tid)
  else { te with tenv_abstracts = IdentSet.add tid.content te.tenv_abstracts }

let gtenv_update_local_aliases (gte : gtenv) (alias : ident) (ty : btyp) : gtenv
    =
  { gte with gtenv_local = tenv_update_aliases gte.gtenv_local alias ty }

let gtenv_update_local_structs (gte : gtenv) (sid : ident)
    (fields : (string * btyp) list) : gtenv =
  { gte with gtenv_local = tenv_update_structs gte.gtenv_local sid fields }

let gtenv_update_local_abstracts (gte : gtenv) (tid : ident) : gtenv =
  { gte with gtenv_local = tenv_update_abstracts gte.gtenv_local tid }

type gcontext = {
  gx_local : btyp IdentMap.t;
  gx_extern : btyp IdentMap.t IdentMap.t;
}

let gcontext_empty = { gx_local = IdentMap.empty; gx_extern = IdentMap.empty }

type var_kind =
  | VarLocal
  | VarParam

type lcontext = (btyp * var_kind) IdentMap.t

let lcontext_empty = IdentMap.empty

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

let gcontext_update_local (gx : gcontext) (x : ident) (ty : btyp) : gcontext =
  match IdentMap.find_opt x.content gx.gx_local with
  | Some _ -> error (Already_defined_glob x.content) ~loc:(Some x)
  | None -> { gx with gx_local = IdentMap.add x.content ty gx.gx_local }

let lcontext_update (lx : lcontext) (x : ident) (ty : btyp) : lcontext =
  match IdentMap.find_opt x.content lx with
  | Some (ty1, _) ->
      if ty1 = ty then IdentMap.add x.content (ty, VarLocal) lx
      else error (Variable_shadowing_diff_type (x.content, ty)) ~loc:(Some x)
  | None -> IdentMap.add x.content (ty, VarLocal) lx

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
      | BBool | BInt32 _ | BInt64 _ -> to_ty
      | _ -> error (Forbidden_cast (from_ty, to_ty))
    end
  | _ -> error (Forbidden_cast (from_ty, to_ty))

let typecheck_struct_proj (gte : gtenv) (mname : string) (sid : string)
    (f : ident) : btyp =
  let se, sid' =
    if mname = !curr_mname then (gte.gtenv_local.tenv_structs, sid)
    else
      match IdentMap.find_opt mname gte.gtenv_extern with
      | Some te -> (te.tenv_structs, compose_idents mname sid)
      | None -> assert false (* Ill-typed environment *)
  in
  match IdentMap.find_opt sid se with
  | Some fields -> begin
      match List.assoc_opt f.content fields with
      | Some tf -> tf
      | None -> error (Unknown_field (f.content, sid'))
    end
  | None -> assert false (* Ill-typed environment *)

let rec styp_to_btyp (imports : ident list) (gte : gtenv) (sty : styp) : btyp =
  match sty with
  | SBool -> BBool
  | SInt32 s -> BInt32 s
  | SInt64 s -> BInt64 s
  | SArray sta -> BArray (styp_to_btyp imports gte sta)
  | SIdent stid -> gtenv_get imports gte stid
  | SFun (stparams, stret) ->
      let tparams =
        List.map (fun (_, sty) -> styp_to_btyp imports gte sty) stparams
      in
      let tret = styp_to_btyp imports gte stret in
      BFun (tparams, tret)

let transl_var_name (imports : ident list) (gx : gcontext) (lx : lcontext)
    (x : cident) : Syntax.ident =
  let rec mname_of_ident (imports : ident list) (id : ident) : string =
    match imports with
    | [] -> error (Undefined_ident id.content) ~loc:(Some id)
    | m1 :: imports' ->
        let m1_gx = IdentMap.find m1.content gx.gx_extern in
        begin
          match IdentMap.find_opt id.content m1_gx with
          | Some _ -> m1.content
          | None -> mname_of_ident imports' id
        end
  in
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
              | None -> mname_of_ident imports x
            end
        in
        sprintf "%s_%s" prefix x.content
    | IdPrefixed (mname, x) -> Printf.sprintf "%s_%s" mname.content x.content
  in
  PrintCommon.ident_of_string x'

let transl_field_name (f : ident) : Syntax.ident =
  PrintCommon.ident_of_string f.content

let rec transl_btyp (ty : btyp) : Types.btyp =
  match ty with
  | BBool -> Types.BBool
  | BInt32 s -> Types.BInt32 s
  | BInt64 s -> Types.BInt64 s
  | BArray ta -> Types.BArray (transl_btyp ta)
  | BStruct (mname, sid) ->
      let sid' = PrintCommon.ident_of_string (sprintf "%s_%s" mname sid) in
      Types.BStruct sid'
  | BAbs (mname, cid) ->
      let cid' = PrintCommon.ident_of_string (sprintf "%s_%s" mname cid) in
      Types.BAbs cid'
  | BFun (tparams, tret) ->
      let tparams' = List.map transl_btyp tparams in
      let tret' = transl_btyp tret in
      Types.BFun (tparams', tret')

let arr_index_btyp : btyp =
  if Archi.ptr64 then BInt64 Types.Unsigned else BInt32 Types.Unsigned

let rec typecheck_raw_expr (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (e : raw_expr) : Barocq.expr * btyp =
  match e with
  | ETrue -> (Barocq.ETrue, BBool)
  | EFalse -> (Barocq.EFalse, BBool)
  | EInt32 (i, s) -> (Barocq.EInt32 (i, s), BInt32 s)
  | EInt64 (i, s) -> (Barocq.EInt64 (i, s), BInt64 s)
  | EVar x ->
      let ty = typof_var imports gx lx x in
      let x' = transl_var_name imports gx lx x in
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
        | BopEq | BopNeq -> Expect_int_or_bool
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
          (Expect_typ arr_index_btyp)
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
          (Expect_typ arr_index_btyp)
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
  | EStructProj (e1, f) ->
      let e1', t1 =
        typecheck_expr_expecting imports gte gx lx e1 Expect_struct
      in
      begin
        match t1 with
        | BStruct (mname, sid) ->
            let f' = transl_field_name f in
            let t = typecheck_struct_proj gte mname sid f in
            (Barocq.EStructProj (e1', f'), t)
        | _ -> assert false
      end
  | EStructUpdate (e1, f, e2) ->
      let e1', t1 =
        typecheck_expr_expecting imports gte gx lx e1 Expect_struct
      in
      begin
        match t1 with
        | BStruct (mname, sid) ->
            let f' = transl_field_name f in
            let tf = typecheck_struct_proj gte mname sid f in
            let e2', _ =
              typecheck_expr_expecting imports gte gx lx e2 (Expect_typ tf)
            in
            (Barocq.EStructUpdate (e1', f', e2'), t1)
        | _ -> assert false
      end
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
  | ELetIn (x, e1, e2) ->
      let x' = PrintCommon.ident_of_string ("u_" ^ x.content) in
      let e1', t1 = typecheck_expr imports gte gx lx e1 in
      let lx' = lcontext_update lx x t1 in
      let e2', t2 = typecheck_expr imports gte gx lx' e2 in
      (Barocq.ELetIn (x', e1', e2'), t2)

and typecheck_expr (imports : ident list) (gte : gtenv) (gx : gcontext)
    (lx : lcontext) (e : expr) : Barocq.expr * btyp =
  try typecheck_raw_expr imports gte gx lx e.content
  with Error (cause, loc) -> update_error_loc cause loc e

and typecheck_expr_expecting (imports : ident list) (gte : gtenv)
    (gx : gcontext) (lx : lcontext) (e : expr) (texp : expected_typ) :
    Barocq.expr * btyp =
  try
    let ((e', ty) as r) = typecheck_raw_expr imports gte gx lx e.content in
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
    | Expect_array -> begin
        match ty with
        | BArray _ -> r
        | _ -> error (Type_mismatch (texp, Current_typ ty))
      end
    | Expect_struct -> begin
        match ty with
        | BStruct _ -> r
        | _ -> error (Type_mismatch (texp, Current_typ ty))
      end
    | Expect_function -> begin
        match ty with
        | BFun _ -> r
        | _ -> error (Type_mismatch (texp, Current_typ ty))
      end
  with Error (cause, loc) -> update_error_loc cause loc e

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

let rec typecheck_literal (gte : gtenv) (ty : btyp) (l : literal) :
    Syntax.literal =
  try
    match (l.content, ty) with
    | LTrue, BBool -> Syntax.LTrue
    | LFalse, BBool -> Syntax.LFalse
    | LInt32 (i, sl), BInt32 st ->
        if sl = st then Syntax.LInt32 (i, sl)
        else
          error
            (Type_mismatch (Expect_typ (BInt32 st), Current_typ (BInt32 sl)))
    | LInt64 (i, sl), BInt64 st ->
        if sl = st then Syntax.LInt64 (i, sl)
        else
          error
            (Type_mismatch (Expect_typ (BInt64 st), Current_typ (BInt64 sl)))
    | LArray a, BArray ta ->
        let a' = List.map (typecheck_literal gte ta) a in
        Syntax.LArray a'
    | LStruct st, BStruct (mname, sid) ->
        let fields, sid' =
          let te, sid' =
            if mname <> !curr_mname then
              match IdentMap.find_opt mname gte.gtenv_extern with
              | Some te -> (te, compose_idents mname sid)
              | None -> assert false (* Ill-typed environment *)
            else (gte.gtenv_local, sid)
          in
          let fields =
            match IdentMap.find_opt sid te.tenv_structs with
            | Some fields -> fields
            | None -> assert false (* Ill-typed environment *)
          in
          (fields, sid')
        in
        let st' = typecheck_struct_lit gte sid' st fields in
        let sid =
          match transl_btyp ty with
          | Types.BStruct sid -> sid
          | _ -> assert false
        in
        Syntax.LStruct (st', sid)
    | (LTrue | LFalse), _ ->
        error (Type_mismatch (Expect_typ ty, Current_typ BBool))
    | LInt32 (_, s), _ ->
        error (Type_mismatch (Expect_typ ty, Current_typ (BInt32 s)))
    | LInt64 (_, s), _ ->
        error (Type_mismatch (Expect_typ ty, Current_typ (BInt64 s)))
    | LArray _, _ -> error (Type_mismatch (Expect_typ ty, Current_array))
    | LStruct _, _ -> error (Type_mismatch (Expect_typ ty, Current_struct))
  with Error (cause, loc) -> update_error_loc cause loc l

and typecheck_struct_lit (gte : gtenv) (sid : string)
    (st : (ident * literal) list) (fields : (string * btyp) list) :
    (Syntax.ident * Syntax.literal) list =
  match st with
  | [] ->
      if List.length fields = 0 then []
      else error (Missing_struct_fields (List.map fst fields))
  | (fname, lit) :: st' -> begin
      match List.assoc_opt fname.content fields with
      | Some ftyp ->
          let lit' = typecheck_literal gte ftyp lit in
          let r =
            typecheck_struct_lit
              gte
              sid
              st'
              (List.remove_assoc fname.content fields)
          in
          let fname' = transl_field_name fname in
          (fname', lit') :: r
      | None -> error (Unknown_field (fname.content, sid)) ~loc:(Some fname)
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
  | Some p -> error (Duplicated_param (p.content, x.content)) ~loc:(Some p)
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
            let pid' = PrintCommon.ident_of_string ("p_" ^ pid) in
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
  PrintCommon.ident_of_string (sprintf "%s_%s" mname x.content)

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

let typecheck_globdef (imports : ident list) (gte : gtenv) (gx : gcontext)
    (def : globdef) : Barocq.globdef option * gtenv * gcontext =
  match def with
  | DefAlias (alias, sty) ->
      let ty = styp_to_btyp imports gte sty in
      let ty = styp_to_btyp imports gte sty in
      (None, gtenv_update_local_aliases gte alias ty, gx)
  | DefType (sid, fields) -> begin
      match find_duplicate_ident (List.map fst fields) with
      | Some fname ->
          error
            (Duplicated_struct_field (fname.content, sid.content))
            ~loc:(Some fname)
      | None ->
          let fields' =
            List.map
              (fun ((fname, ftyp) : ident * styp) ->
                (fname.content, styp_to_btyp imports gte ftyp))
              fields
          in
          let bsid = transl_globdef_name !curr_mname sid in
          let bfields =
            List.map
              (fun (fname, ftyp) ->
                let fname' = PrintCommon.ident_of_string fname in
                let ftyp' = transl_btyp ftyp in
                (fname', ftyp'))
              fields'
          in
          let gte' = gtenv_update_local_structs gte sid fields' in
          (Some (Barocq.DefType (bsid, bfields)), gte', gx)
    end
  | DefConst (id, l, sty) ->
      let ty = styp_to_btyp imports gte sty in
      let ty = styp_to_btyp imports gte sty in
      let l' = typecheck_literal gte ty l in
      let gx' = gcontext_update_local gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      let bty = transl_btyp ty in
      let bty = transl_btyp ty in
      (Some (Barocq.DefConst (bid, l', bty)), gte, gx')
  | DefFun (id, f) ->
      let bf, ty = typecheck_function imports gte gx id f in
      let gx' = gcontext_update_local gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      (Some (Barocq.DefFun (bid, bf)), gte, gx')
  | DeclType (tid, tk) ->
      let gte' = gtenv_update_local_abstracts gte tid in
      let bid = transl_globdef_name !curr_mname tid in
      (Some (Barocq.DeclType (bid, tk)), gte', gx)
  | DeclConst (id, sty) ->
      let ty = styp_to_btyp imports gte sty in
      let gx' = gcontext_update_local gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      let bty = transl_btyp ty in
      (Some (Barocq.DeclConst (bid, bty)), gte, gx')
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
      let gx' = gcontext_update_local gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      let btparams =
        List.map
          (fun (attr, bty) ->
            let bty' = transl_btyp bty in
            (attr, bty'))
          tparams'
      in
      let btret = transl_btyp tret' in
      (Some (Barocq.DeclFun (bid, btparams, btret)), gte, gx')

let rec typecheck_imports (imports : ident list) (gx : gcontext) : unit =
  match imports with
  | [] -> ()
  | m1 :: imports' -> begin
      match IdentMap.find_opt m1.content gx.gx_extern with
      | Some _ -> typecheck_imports imports' gx
      | None -> error (Module_not_found m1.content) ~loc:(Some m1)
    end

let typecheck_modul (gte : gtenv) (gx : gcontext) (md : modul) :
    Barocq.program * gtenv * gcontext =
  let mname = md.md_name in
  match IdentMap.find_opt mname.content gx.gx_extern with
  | Some _ -> error (Duplicated_module mname.content) ~loc:(Some mname)
  | _ ->
      curr_mname := md.md_name.content;
      (* Initialization of gte and gtx *)
      let gte = { gte with gtenv_local = tenv_empty } in
      let gx = { gx with gx_local = IdentMap.empty } in
      (* Type checking *)
      typecheck_imports md.md_imports gx;
      let defs, gte, gx =
        List.fold_left
          (fun (acc_defs, acc_gte, acc_gx) def ->
            let d, gte, gx =
              typecheck_globdef md.md_imports acc_gte acc_gx def
            in
            let acc_defs' =
              match d with
              | Some d -> d :: acc_defs
              | None -> acc_defs
            in
            (acc_defs', gte, gx))
          ([], gte, gx)
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
      let gx' =
        {
          gx_local = IdentMap.empty;
          gx_extern = IdentMap.add md.md_name.content gx.gx_local gx.gx_extern;
        }
      in
      let bprog = List.rev defs in
      (bprog, gte', gx')

let typecheck_program (prog : program) : Barocq.program =
  let bprog, _, _ =
    List.fold_left
      (fun (acc_prog, acc_gte, acc_gx) md ->
        let bprog, gte, gx = typecheck_modul acc_gte acc_gx md in
        let bprog' = List.append acc_prog bprog in
        (bprog', gte, gx))
      ([], gtenv_empty, gcontext_empty)
      prog
  in
  bprog

let typecheck_command (imports : ident list) (gte : gtenv) (gx : gcontext)
    (cmd : command) : Barocq.command option * gtenv * gcontext =
  match cmd with
  | CmdDef d ->
      let bd, gte', gx' = typecheck_globdef imports gte gx d in
      begin
        match bd with
        | Some bd -> (Some (Barocq.CmdDef bd), gte', gx')
        | None -> (None, gte', gx')
      end
  | CmdExpr e ->
      let be, _ = typecheck_expr imports gte gx lcontext_empty e in
      (Some (Barocq.CmdExpr be), gte, gx)

let typecheck_imodul (gte : gtenv) (gx : gcontext) (imd : imodul) :
    Barocq.iprogram * gtenv * gcontext =
  let mname = imd.imd_name in
  match IdentMap.find_opt mname.content gx.gx_extern with
  | Some _ -> error (Duplicated_module mname.content) ~loc:(Some mname)
  | _ ->
      curr_mname := imd.imd_name.content;
      (* Initialization of gte and gtx *)
      let gte = { gte with gtenv_local = tenv_empty } in
      let gx = { gx with gx_local = IdentMap.empty } in
      typecheck_imports imd.imd_imports gx;
      (* Type checking *)
      let cmds, gte, gx =
        List.fold_left
          (fun (acc_cmds, acc_gte, acc_gx) cmd ->
            let cmd, gte, gx =
              typecheck_command imd.imd_imports acc_gte acc_gx cmd
            in
            let acc_defs' =
              match cmd with
              | Some cmd -> cmd :: acc_cmds
              | None -> acc_cmds
            in
            (acc_defs', gte, gx))
          ([], gte, gx)
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
      let gx' =
        {
          gx_local = IdentMap.empty;
          gx_extern = IdentMap.add imd.imd_name.content gx.gx_local gx.gx_extern;
        }
      in
      let bprog = List.rev cmds in
      (bprog, gte', gx')

let typecheck_iprogram (iprog : iprogram) : Barocq.iprogram =
  let biprog, _, _ =
    List.fold_left
      (fun (acc_iprog, acc_gte, acc_gx) md ->
        let biprog, gte, gx = typecheck_imodul acc_gte acc_gx md in
        let biprog' = List.append acc_iprog biprog in
        (biprog', gte, gx))
      ([], gtenv_empty, gcontext_empty)
      iprog
  in
  biprog
