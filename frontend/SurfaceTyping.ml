open Printf
open Syntax
open Location
open SurfaceAST

(** Name of the module being analyzed. *)
let curr_mname : string ref = ref ""

type ctyp =
  | CBool
  | CInt32 of Types.signedness
  | CInt64 of Types.signedness
  | CArray of ctyp
  | CStruct of string * string
  | CFun of ctyp list * ctyp

type expected_typ =
  | Expect_typ of ctyp
  | Expect_int
  | Expect_int_or_bool
  | Expect_array
  | Expect_struct
  | Expect_function

type current_typ =
  | Current_typ of ctyp
  | Current_array
  | Current_struct

type error_cause =
  | Type_mismatch of expected_typ * current_typ
  | Forbidden_cast of ctyp * ctyp
  | Undefined_ident of string
  | Undefined_type of string
  | Unknown_field of string * string
  | Module_not_found of string
  | Wrong_argument_number of int * int
  | Variable_shadowing_diff_type of string * ctyp
  | Already_defined_type of string
  | Already_defined_glob of string
  | Duplicated_struct_field of string * string
  | Duplicated_param of string * string
  | Duplicated_module of string
  | Missing_struct_fields of string list

exception Error of error_cause * unit Location.t option

let rec ctyp_to_string (ty : ctyp) : string =
  match ty with
  | CBool -> "bool"
  | CInt32 Types.Signed -> "i32"
  | CInt32 Types.Unsigned -> "u32"
  | CInt64 Types.Signed -> "i64"
  | CInt64 Types.Unsigned -> "u64"
  | CArray (CArray t) -> sprintf "array (%s)" (ctyp_to_string t)
  | CArray t -> sprintf "array %s" (ctyp_to_string t)
  | CStruct (mname, sid) ->
      if mname = !curr_mname then sid else sprintf "%s::%s" mname sid
  | CFun (tparams, tret) ->
      PrintTypes.funtyp_to_string ctyp_to_string tparams tret

let msg_from_failure (cause : error_cause) : string =
  match cause with
  | Undefined_ident x -> sprintf "undefined identifier %s" x
  | Type_mismatch (ety, cty) ->
      let prefix =
        match cty with
        | Current_typ ty ->
            sprintf "this expression has type %s" (ctyp_to_string ty)
        | Current_array -> sprintf "this expression is an array"
        | Current_struct -> sprintf "this expression is a struct"
      in
      let suffix =
        match ety with
        | Expect_typ cty ->
            sprintf
              "but an expression was expected of type %s"
              (ctyp_to_string cty)
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
        (ctyp_to_string ty)
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
        (ctyp_to_string t1)
        (ctyp_to_string t2)
  | Module_not_found mname -> sprintf "module %s not found" mname
  | Duplicated_module mname ->
      sprintf "a module with name %s already exists" mname
  | Missing_struct_fields mfields ->
      sprintf
        "the following struct fields are missing: %s"
        (PrintCommon.list_to_string "" "" ", " (fun x -> x) mfields)

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

type senv = (string * ctyp) list IdentMap.t

type tenv = {
  tenv_aliases : ctyp IdentMap.t;
  tenv_structs : senv;
}

let tenv_empty =
  { tenv_aliases = IdentMap.empty; tenv_structs = IdentMap.empty }

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

let tenv_get (mname : string) (te : tenv) (tid : ident) : ctyp =
  match IdentMap.find_opt tid.content te.tenv_aliases with
  | Some ty -> ty
  | None -> begin
      match IdentMap.find_opt tid.content te.tenv_structs with
      | Some _ -> CStruct (mname, tid.content)
      | None -> error (Undefined_type tid.content) ~loc:(Some tid)
    end

let gtenv_get (gte : gtenv) (cid : cident) : ctyp =
  match cid with
  | IdLocal tid -> tenv_get !curr_mname gte.gtenv_local tid
  | IdExtern (mname, tid) -> begin
      match IdentMap.find_opt mname.content gte.gtenv_extern with
      | Some te -> begin
          try tenv_get mname.content te tid
          with Error (Undefined_type _, loc) ->
            let tid' = compose_loc_idents mname tid in
            error (Undefined_type tid'.content) ~loc:(Some tid)
        end
      | None -> error (Module_not_found mname.content) ~loc:(Some mname)
    end

let gtenv_get_fields (gte : gtenv) (cid : cident) : (string * ctyp) list =
  let ty = gtenv_get gte cid in
  match ty with
  | CStruct (mname, sid) ->
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

let tenv_update_aliases (te : tenv) (alias : ident) (ty : ctyp) : tenv =
  if is_local_type_defined te alias.content then
    error (Already_defined_type alias.content) ~loc:(Some alias)
  else { te with tenv_aliases = IdentMap.add alias.content ty te.tenv_aliases }

let tenv_update_structs (te : tenv) (sid : ident)
    (fields : (string * ctyp) list) : tenv =
  if is_local_type_defined te sid.content then
    error (Already_defined_type sid.content) ~loc:(Some sid)
  else
    { te with tenv_structs = IdentMap.add sid.content fields te.tenv_structs }

let gtenv_update_local_aliases (gte : gtenv) (alias : ident) (ty : ctyp) : gtenv
    =
  { gte with gtenv_local = tenv_update_aliases gte.gtenv_local alias ty }

let gtenv_update_local_structs (gte : gtenv) (sid : ident)
    (fields : (string * ctyp) list) : gtenv =
  { gte with gtenv_local = tenv_update_structs gte.gtenv_local sid fields }

type gcontext = {
  gx_local : ctyp IdentMap.t;
  gx_extern : ctyp IdentMap.t IdentMap.t;
}

let gcontext_empty = { gx_local = IdentMap.empty; gx_extern = IdentMap.empty }

type var_kind =
  | VarLocal
  | VarParam

type lcontext = (ctyp * var_kind) IdentMap.t

let lcontext_empty = IdentMap.empty

let gcontext_get (gx : gcontext) (cid : cident) : ctyp =
  match cid with
  | IdLocal id -> begin
      match IdentMap.find_opt id.content gx.gx_local with
      | Some ty -> ty
      | None -> error (Undefined_ident id.content) ~loc:(Some id)
    end
  | IdExtern (mname, id) -> begin
      match IdentMap.find_opt mname.content gx.gx_extern with
      | Some mx -> begin
          match IdentMap.find_opt id.content mx with
          | Some ty -> ty
          | None ->
              let id' = compose_loc_idents mname id in
              error (Undefined_ident id'.content) ~loc:(Some id')
        end
      | None -> error (Module_not_found mname.content) ~loc:(Some mname)
    end

let gcontext_update_local (gx : gcontext) (x : ident) (ty : ctyp) : gcontext =
  match IdentMap.find_opt x.content gx.gx_local with
  | Some _ -> error (Already_defined_glob x.content) ~loc:(Some x)
  | None -> { gx with gx_local = IdentMap.add x.content ty gx.gx_local }

let lcontext_update (lx : lcontext) (x : ident) (ty : ctyp) : lcontext =
  match IdentMap.find_opt x.content lx with
  | Some (ty1, _) ->
      if ty1 = ty then IdentMap.add x.content (ty, VarLocal) lx
      else error (Variable_shadowing_diff_type (x.content, ty)) ~loc:(Some x)
  | None -> IdentMap.add x.content (ty, VarLocal) lx

let typof_var (gx : gcontext) (lx : lcontext) (x : cident) : ctyp =
  match x with
  | IdLocal x' -> begin
      match IdentMap.find_opt x'.content lx with
      | Some (ty, _) -> ty
      | None -> gcontext_get gx x
    end
  | IdExtern _ -> gcontext_get gx x

let typecheck_unary_op (op : unary_op) (ty : ctyp) : ctyp =
  match (op, ty) with
  | UopNotbool, CBool
  | UopNotint, CInt32 _
  | UopNotint, CInt64 _
  | UopNeg, (CInt32 _ | CInt64 _)
  | UopPlus, (CInt32 _ | CInt64 _) -> ty
  | _, _ -> assert false

let typecheck_binary_op (op : binary_op) (ty1 : ctyp) (ty2 : ctyp) : ctyp =
  match op with
  | BopAndbool | BopOrbool | BopXorbool -> begin
      match (ty1, ty2) with
      | CBool, CBool -> CBool
      | _, _ -> assert false
    end
  | BopEq | BopNeq -> begin
      match (ty1, ty2) with
      | CBool, CBool -> CBool
      | CInt32 s1, CInt32 s2 | CInt64 s1, CInt64 s2 ->
          if s1 = s2 then CBool else assert false
      | _, _ -> assert false
    end
  | BopLt | BopLe | BopGt | BopGe -> begin
      match (ty1, ty2) with
      | CInt32 s1, CInt32 s2 | CInt64 s1, CInt64 s2 ->
          if s1 = s2 then CBool else assert false
      | _, _ -> assert false
    end
  | _ -> begin
      match (ty1, ty2) with
      | CInt32 s1, CInt32 s2 | CInt64 s1, CInt64 s2 ->
          if s1 = s2 then ty1 else assert false
      | _, _ -> assert false
    end

let typecheck_cast (from_ty : ctyp) (to_ty : ctyp) : ctyp =
  match from_ty with
  | CBool | CInt32 _ | CInt64 _ -> begin
      match to_ty with
      | CBool | CInt32 _ | CInt64 _ -> to_ty
      | _ -> error (Forbidden_cast (from_ty, to_ty))
    end
  | _ -> error (Forbidden_cast (from_ty, to_ty))

let typecheck_struct_proj (gte : gtenv) (mname : string) (sid : string)
    (f : ident) : ctyp =
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

let rec styp_to_ctyp (gte : gtenv) (sty : styp) : ctyp =
  match sty with
  | SBool -> CBool
  | SInt32 s -> CInt32 s
  | SInt64 s -> CInt64 s
  | SArray sta -> CArray (styp_to_ctyp gte sta)
  | SStructOrAlias stid -> gtenv_get gte stid
  | SFun (stparams, stret) ->
      let tparams = List.map (styp_to_ctyp gte) stparams in
      let tret = styp_to_ctyp gte stret in
      CFun (tparams, tret)

let transl_var_name (mname : string) (lx : lcontext) (x : cident) : Syntax.ident
    =
  let x' =
    match x with
    | IdLocal x ->
        let prefix =
          match IdentMap.find_opt x.content lx with
          | Some (_, VarLocal) -> "u_"
          | Some (_, VarParam) -> "p_"
          | None -> mname ^ "_"
        in
        prefix ^ x.content
    | IdExtern (mname', x) -> Printf.sprintf "%s_%s" mname'.content x.content
  in
  PrintCommon.ident_of_string x'

let transl_field_name (f : ident) : Syntax.ident =
  PrintCommon.ident_of_string f.content

let rec transl_ctyp (ty : ctyp) : Types.ctyp =
  match ty with
  | CBool -> Types.CBool
  | CInt32 s -> Types.CInt32 s
  | CInt64 s -> Types.CInt64 s
  | CArray ta -> Types.CArray (transl_ctyp ta)
  | CStruct (mname, sid) ->
      let sid' = PrintCommon.ident_of_string (sprintf "%s_%s" mname sid) in
      Types.CStruct sid'
  | CFun (tparams, tret) ->
      let tparams' = List.map transl_ctyp tparams in
      let tret' = transl_ctyp tret in
      Types.CFun (tparams', tret')

let rec typecheck_raw_expr (gte : gtenv) (gx : gcontext) (lx : lcontext)
    (e : raw_expr) : Barocq.expr * ctyp =
  match e with
  | ETrue -> (Barocq.ETrue, CBool)
  | EFalse -> (Barocq.EFalse, CBool)
  | EInt32 (i, s) -> (Barocq.EInt32 (i, s), CInt32 s)
  | EInt64 (i, s) -> (Barocq.EInt64 (i, s), CInt64 s)
  | EVar x ->
      let x' = transl_var_name !curr_mname lx x in
      (Barocq.EVar x', typof_var gx lx x)
  | ECast (e1, sty) ->
      let ty = styp_to_ctyp gte sty in
      let e1', t1 = typecheck_expr gte gx lx e1 in
      (Barocq.ECast (e1', transl_ctyp ty), typecheck_cast t1 ty)
  | EUnaryOp (op, e1) ->
      let texp =
        match op with
        | UopNeg | UopNotint | UopPlus -> Expect_int
        | UopNotbool -> Expect_typ CBool
      in
      let e1', t1 = typecheck_expr_expecting gte gx lx e1 texp in
      let t = typecheck_unary_op op t1 in
      (Barocq.EUnaryOp (op, e1'), t)
  | EBinaryOp (op, e1, e2) ->
      let texp =
        match op with
        | BopAndbool | BopOrbool | BopXorbool -> Expect_typ CBool
        | BopEq | BopNeq -> Expect_int_or_bool
        | _ -> Expect_int
      in
      let e1', t1 = typecheck_expr_expecting gte gx lx e1 texp in
      let e2', t2 = typecheck_expr_expecting gte gx lx e2 (Expect_typ t1) in
      let t = typecheck_binary_op op t1 t2 in
      (Barocq.EBinaryOp (op, e1', e2'), t)
  | EArrayGet (e1, e2) ->
      let e1', t1 = typecheck_expr_expecting gte gx lx e1 Expect_array in
      let e2', _ =
        typecheck_expr_expecting
          gte
          gx
          lx
          e2
          (Expect_typ (CInt32 Types.Unsigned))
      in
      begin
        match t1 with
        | CArray ta -> (Barocq.EArrayGet (e1', e2'), ta)
        | _ -> assert false
      end
  | EArraySet (e1, e2, e3) ->
      let e1', t1 = typecheck_expr_expecting gte gx lx e1 Expect_array in
      let e2', _ =
        typecheck_expr_expecting
          gte
          gx
          lx
          e2
          (Expect_typ (CInt32 Types.Unsigned))
      in
      begin
        match t1 with
        | CArray ta ->
            let e3', _ =
              typecheck_expr_expecting gte gx lx e3 (Expect_typ ta)
            in
            (Barocq.EArraySet (e1', e2', e3'), t1)
        | _ -> assert false
      end
  | EStructProj (e1, f) ->
      let e1', t1 = typecheck_expr_expecting gte gx lx e1 Expect_struct in
      begin
        match t1 with
        | CStruct (mname, sid) ->
            let f' = transl_field_name f in
            let t = typecheck_struct_proj gte mname sid f in
            (Barocq.EStructProj (e1', f'), t)
        | _ -> assert false
      end
  | EStructUpdate (e1, f, e2) ->
      let e1', t1 = typecheck_expr_expecting gte gx lx e1 Expect_struct in
      begin
        match t1 with
        | CStruct (mname, sid) ->
            let f' = transl_field_name f in
            let tf = typecheck_struct_proj gte mname sid f in
            let e2', _ =
              typecheck_expr_expecting gte gx lx e2 (Expect_typ tf)
            in
            (Barocq.EStructUpdate (e1', f', e2'), t1)
        | _ -> assert false
      end
  | EApp (e1, args) ->
      let e1', t1 = typecheck_expr_expecting gte gx lx e1 Expect_function in
      begin
        match t1 with
        | CFun (tparams, tret) ->
            let args', t = typecheck_app gte gx lx tparams tret args in
            (Barocq.EApp (e1', args'), t)
        | _ -> assert false
      end
  | EIfThenElse (e1, e2, e3) ->
      let e1', _ = typecheck_expr_expecting gte gx lx e1 (Expect_typ CBool) in
      let e2', t2 = typecheck_expr gte gx lx e2 in
      let e3', _ = typecheck_expr_expecting gte gx lx e3 (Expect_typ t2) in
      (Barocq.EIfThenElse (e1', e2', e3'), t2)
  | ELetIn (x, e1, e2) ->
      let x' = PrintCommon.ident_of_string ("u_" ^ x.content) in
      let e1', t1 = typecheck_expr gte gx lx e1 in
      let lx' = lcontext_update lx x t1 in
      let e2', t2 = typecheck_expr gte gx lx' e2 in
      (Barocq.ELetIn (x', e1', e2'), t2)

and typecheck_expr (gte : gtenv) (gx : gcontext) (lx : lcontext) (e : expr) :
    Barocq.expr * ctyp =
  try typecheck_raw_expr gte gx lx e.content
  with Error (cause, loc) -> update_error_loc cause loc e

and typecheck_expr_expecting (gte : gtenv) (gx : gcontext) (lx : lcontext)
    (e : expr) (texp : expected_typ) : Barocq.expr * ctyp =
  try
    let ((e', ty) as r) = typecheck_raw_expr gte gx lx e.content in
    match texp with
    | Expect_typ t ->
        if t = ty then r else error (Type_mismatch (texp, Current_typ ty))
    | Expect_int -> begin
        match ty with
        | CInt32 _ | CInt64 _ -> r
        | _ -> error (Type_mismatch (texp, Current_typ ty))
      end
    | Expect_int_or_bool -> begin
        match ty with
        | CBool | CInt32 _ | CInt64 _ -> r
        | _ -> error (Type_mismatch (texp, Current_typ ty))
      end
    | Expect_array -> begin
        match ty with
        | CArray _ -> r
        | _ -> error (Type_mismatch (texp, Current_typ ty))
      end
    | Expect_struct -> begin
        match ty with
        | CStruct _ -> r
        | _ -> error (Type_mismatch (texp, Current_typ ty))
      end
    | Expect_function -> begin
        match ty with
        | CFun _ -> r
        | _ -> error (Type_mismatch (texp, Current_typ ty))
      end
  with Error (cause, loc) -> update_error_loc cause loc e

and typecheck_app (gte : gtenv) (gx : gcontext) (lx : lcontext)
    (tparams : ctyp list) (tret : ctyp) (args : expr list) :
    Barocq.expr list * ctyp =
  let arity = List.length tparams in
  let nbargs = List.length args in
  let rec aux tparams args =
    match (tparams, args) with
    | [], [] -> ([], tret)
    | tp :: tparams', a :: args' ->
        let a', _ = typecheck_expr_expecting gte gx lx a (Expect_typ tp) in
        let bargs, t = aux tparams' args' in
        (a' :: bargs, t)
    | _, _ -> error (Wrong_argument_number (arity, nbargs))
  in
  aux tparams args

let rec typecheck_literal (gte : gtenv) (ty : ctyp) (l : literal) :
    Syntax.literal =
  try
    match (l.content, ty) with
    | LTrue, CBool -> Syntax.LTrue
    | LFalse, CBool -> Syntax.LFalse
    | LInt32 (i, sl), CInt32 st ->
        if sl = st then Syntax.LInt32 (i, sl)
        else
          error
            (Type_mismatch (Expect_typ (CInt32 st), Current_typ (CInt32 sl)))
    | LInt64 (i, sl), CInt64 st ->
        if sl = st then Syntax.LInt64 (i, sl)
        else
          error
            (Type_mismatch (Expect_typ (CInt64 st), Current_typ (CInt64 sl)))
    | LArray a, CArray ta ->
        let a' = List.map (typecheck_literal gte ta) a in
        Syntax.LArray a'
    | LStruct st, CStruct (mname, sid) ->
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
          match transl_ctyp ty with
          | Types.CStruct sid -> sid
          | _ -> assert false
        in
        Syntax.LStruct (st', sid)
    | (LTrue | LFalse), _ ->
        error (Type_mismatch (Expect_typ ty, Current_typ CBool))
    | LInt32 (_, s), _ ->
        error (Type_mismatch (Expect_typ ty, Current_typ (CInt32 s)))
    | LInt64 (_, s), _ ->
        error (Type_mismatch (Expect_typ ty, Current_typ (CInt64 s)))
    | LArray _, _ -> error (Type_mismatch (Expect_typ ty, Current_array))
    | LStruct _, _ -> error (Type_mismatch (Expect_typ ty, Current_struct))
  with Error (cause, loc) -> update_error_loc cause loc l

and typecheck_struct_lit (gte : gtenv) (sid : string)
    (st : (ident * literal) list) (fields : (string * ctyp) list) :
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

let typecheck_function (gte : gtenv) (gx : gcontext) (x : ident) (f : func) :
    Barocq.coq_function * ctyp =
  match find_duplicate_ident (List.map fst f.fn_params) with
  | Some p -> error (Duplicated_param (p.content, x.content)) ~loc:(Some p)
  | None ->
      let tret = styp_to_ctyp gte f.fn_return in
      let params =
        List.map
          (fun ((pid, ptyp) : ident * styp) ->
            (pid.content, styp_to_ctyp gte ptyp))
          f.fn_params
      in
      let ty = CFun (List.map snd params, tret) in
      let lx =
        List.fold_left
          (fun acc (pid, ptyp) -> IdentMap.add pid (ptyp, VarParam) acc)
          lcontext_empty
          params
      in
      let body, tb =
        typecheck_expr_expecting gte gx lx f.fn_body (Expect_typ tret)
      in
      let bparams =
        List.map
          (fun (pid, ptyp) ->
            let pid' = PrintCommon.ident_of_string ("p_" ^ pid) in
            let ptyp' = transl_ctyp ptyp in
            (pid', ptyp'))
          params
      in
      let bf =
        {
          Syntax.fn_return = transl_ctyp tret;
          Syntax.fn_params = bparams;
          Syntax.fn_body = body;
        }
      in
      (bf, ty)

let transl_globdef_name (mname : string) (x : ident) : Syntax.ident =
  PrintCommon.ident_of_string (sprintf "%s_%s" mname x.content)

let typecheck_globdef (gte : gtenv) (gx : gcontext) (def : globdef) :
    Barocq.globdef option * gtenv * gcontext =
  match def with
  | DefAlias (alias, sty) ->
      let ty = styp_to_ctyp gte sty in
      (None, gtenv_update_local_aliases gte alias ty, gx)
  | DefStruct (sid, fields) -> begin
      match find_duplicate_ident (List.map fst fields) with
      | Some fname ->
          error
            (Duplicated_struct_field (fname.content, sid.content))
            ~loc:(Some fname)
      | None ->
          let fields' =
            List.map
              (fun ((fname, ftyp) : ident * styp) ->
                (fname.content, styp_to_ctyp gte ftyp))
              fields
          in
          let bsid = transl_globdef_name !curr_mname sid in
          let bfields =
            List.map
              (fun (fname, ftyp) ->
                let fname' = PrintCommon.ident_of_string fname in
                let ftyp' = transl_ctyp ftyp in
                (fname', ftyp'))
              fields'
          in
          let gte' = gtenv_update_local_structs gte sid fields' in
          (Some (Barocq.DefStruct (bsid, bfields)), gte', gx)
    end
  | DefConst (id, l, sty) ->
      let ty = styp_to_ctyp gte sty in
      let l' = typecheck_literal gte ty l in
      let gx' = gcontext_update_local gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      let bty = transl_ctyp ty in
      (Some (Barocq.DefConst (bid, l', bty)), gte, gx')
  | DefFun (id, f) ->
      let bf, ty = typecheck_function gte gx id f in
      let gx' = gcontext_update_local gx id ty in
      let bid = transl_globdef_name !curr_mname id in
      (Some (Barocq.DefFun (bid, bf)), gte, gx')

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
      let defs, gte, gx =
        List.fold_left
          (fun (acc_defs, acc_gte, acc_gx) def ->
            let d, gte, gx = typecheck_globdef acc_gte acc_gx def in
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

let typecheck_command (gte : gtenv) (gx : gcontext) (cmd : command) :
    Barocq.command option * gtenv * gcontext =
  match cmd with
  | CmdDef d ->
      let bd, gte', gx' = typecheck_globdef gte gx d in
      begin
        match bd with
        | Some bd -> (Some (Barocq.CmdDef bd), gte', gx')
        | None -> (None, gte', gx')
      end
  | CmdExpr e ->
      let be, _ = typecheck_expr gte gx lcontext_empty e in
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
      (* Type checking *)
      let cmds, gte, gx =
        List.fold_left
          (fun (acc_cmds, acc_gte, acc_gx) cmd ->
            let cmd, gte, gx = typecheck_command acc_gte acc_gx cmd in
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
