open Printf
open Maps
open Types
open Syntax
open Utils
open Location
open SurfaceAST

(* exception Error of string

let error msg = raise (Error msg) *)

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
  | Undefined_ident of Syntax.ident
  | Type_mismatch of expected_typ * current_typ
  | Unknown_field of Syntax.ident * Syntax.ident
  | Wrong_argument_number of int * int
  | Variable_shadowing_diff_type of Syntax.ident * ctyp
  | Already_defined_type of Syntax.ident
  | Already_defined_glob of Syntax.ident
  | Unknown_type of Syntax.ident
  | Duplicated_struct_field of Syntax.ident * Syntax.ident
  | Duplicated_param of Syntax.ident * Syntax.ident
  | Forbidden_cast of ctyp * ctyp

let funtyp_to_string (f : 'typ -> string) (tparams : 'typ list) (tret : 'typ) :
    string =
  let p =
    match tparams with
    | [t] -> f t
    | _ -> PrintCommon.list_to_string_paren f tparams
  in
  sprintf "%s -> %s" p (f tret)

let msg_from_failure (cause : error_cause) : string =
  match cause with
  | Undefined_ident x ->
      sprintf "undefined identifier %s" (PrintCommon.ident_to_string x)
  | Type_mismatch (ety, cty) ->
      let prefix =
        match cty with
        | Current_typ ty ->
            sprintf "this expression has type %s" (PrintTypes.ctyp_to_string ty)
        | Current_array -> sprintf "this expression is an array"
        | Current_struct -> sprintf "this expression is a struct"
      in
      let suffix =
        match ety with
        | Expect_typ cty ->
            sprintf
              "but an expression was expected of type %s"
              (PrintTypes.ctyp_to_string cty)
        | Expect_int -> sprintf "but an integer expression was expected"
        | Expect_int_or_bool ->
            sprintf "but a boolean or integer expression was expected"
        | Expect_array -> sprintf "but an array was expected"
        | Expect_struct -> sprintf "but a struct was expected"
        | Expect_function -> sprintf "but a function was expected"
      in
      sprintf "%s %s" prefix suffix
  | Unknown_field (f, st) ->
      sprintf
        "field %s is not defined for struct type %s"
        (PrintCommon.ident_to_string f)
        (PrintCommon.ident_to_string st)
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
        (PrintCommon.ident_to_string id)
        (PrintTypes.ctyp_to_string ty)
  | Already_defined_type tid ->
      sprintf "type %s is already defined" (PrintCommon.ident_to_string tid)
  | Already_defined_glob gid ->
      sprintf
        "global identifier %s cannot be redefined"
        (PrintCommon.ident_to_string gid)
  | Unknown_type tid ->
      sprintf "type %s is not defined" (PrintCommon.ident_to_string tid)
  | Duplicated_struct_field (fname, sid) ->
      sprintf
        "field %s is duplicated in struct type %s"
        (PrintCommon.ident_to_string fname)
        (PrintCommon.ident_to_string sid)
  | Duplicated_param (p, f) ->
      sprintf
        "parameter %s is duplicated in the definition of function %s"
        (PrintCommon.ident_to_string p)
        (PrintCommon.ident_to_string f)
  | Forbidden_cast (t1, t2) ->
      sprintf
        "cannot cast a value of type %s to a value of type %s"
        (PrintTypes.ctyp_to_string t1)
        (PrintTypes.ctyp_to_string t2)

exception Error of error_cause * unit Location.t option

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

type tenv = {
  tenv_aliases : ctyp PTree.t;
  tenv_structs : types;
}

let tenv_get (te : tenv) (tid : ident) : ctyp =
  match tget te.tenv_aliases tid.content with
  | Some ty -> ty
  | None -> begin
      match types_get te.tenv_structs tid.content with
      | Errors.OK _ -> CStruct tid.content
      | Errors.Error _ -> error (Unknown_type tid.content) ~loc:(Some tid)
    end

let is_type_defined (te : tenv) (tid : Syntax.ident) : bool =
  match tget te.tenv_aliases tid with
  | Some _ -> true
  | None -> begin
      match types_get te.tenv_structs tid with
      | Errors.OK _ -> true
      | Errors.Error _ -> false
    end

let tenv_update_alias (te : tenv) (alias : ident) (ty : ctyp) : tenv =
  if is_type_defined te alias.content then
    error (Already_defined_type alias.content) ~loc:(Some alias)
  else { te with tenv_aliases = tset te.tenv_aliases alias.content ty }

let tenv_update_structs (te : tenv) (sid : ident)
    (fields : (Syntax.ident * ctyp) list) : tenv =
  if is_type_defined te sid.content then
    error (Already_defined_type sid.content) ~loc:(Some sid)
  else { te with tenv_structs = tset te.tenv_structs sid.content fields }

let tenv_empty = { tenv_aliases = PTree.empty; tenv_structs = PTree.empty }

type gcontext = Typing.gcontext

type lcontext = Typing.lcontext

let gcontext_update (gx : gcontext) (x : ident) (ty : ctyp) : gcontext =
  match Typing.gcontext_update gx x.content ty with
  | Errors.OK gx' -> gx'
  | Errors.Error _ -> error (Already_defined_glob x.content) ~loc:(Some x)

let typof_var (gx : gcontext) (lx : lcontext) (x : ident) : ctyp =
  match Typing.typof_var gx lx x.content with
  | Errors.OK ty -> ty
  | Errors.Error _ -> error (Undefined_ident x.content) ~loc:(Some x)

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

let typecheck_struct_proj (ts : types) (st : Syntax.ident) (f : ident) : ctyp =
  match types_get ts st with
  | Errors.OK fields -> begin
      match List.assoc_opt f.content fields with
      | Some tf -> tf
      | None -> error (Unknown_field (f.content, st))
    end
  | Errors.Error _ -> assert false

let rec styp_to_ctyp (te : tenv) (sty : styp) : ctyp =
  match sty with
  | SBool -> CBool
  | SInt32 s -> CInt32 s
  | SInt64 s -> CInt64 s
  | SArray sta -> CArray (styp_to_ctyp te sta)
  | SStructOrAlias stid -> tenv_get te stid
  | SFun (stparams, stret) ->
      let tparams = List.map (styp_to_ctyp te) stparams in
      let tret = styp_to_ctyp te stret in
      CFun (tparams, tret)

let rec typecheck_raw_expr (te : tenv) (gx : gcontext) (lx : lcontext)
    (e : raw_expr) : Barocq.expr * ctyp =
  match e with
  | ETrue -> (Barocq.ETrue, CBool)
  | EFalse -> (Barocq.EFalse, CBool)
  | EInt32 (i, s) -> (Barocq.EInt32 (i, s), CInt32 s)
  | EInt64 (i, s) -> (Barocq.EInt64 (i, s), CInt64 s)
  | EVar x -> (Barocq.EVar x.content, typof_var gx lx x)
  | ECast (e1, sty) ->
      let ty = styp_to_ctyp te sty in
      let e1', t1 = typecheck_expr te gx lx e1 in
      begin
        match Typing.typecheck_cast t1 ty with
        | Errors.OK t -> (Barocq.ECast (e1', t), t)
        | Errors.Error _ -> error (Forbidden_cast (t1, ty))
      end
  | EUnaryOp (op, e1) ->
      let texp =
        match op with
        | UopNeg | UopNotint | UopPlus -> Expect_int
        | UopNotbool -> Expect_typ CBool
      in
      let e1', t1 = typecheck_expr_expecting te gx lx e1 texp in
      let t = typecheck_unary_op op t1 in
      (Barocq.EUnaryOp (op, e1'), t)
  | EBinaryOp (op, e1, e2) ->
      let texp =
        match op with
        | BopAndbool | BopOrbool | BopXorbool -> Expect_typ CBool
        | BopEq | BopNeq -> Expect_int_or_bool
        | _ -> Expect_int
      in
      let e1', t1 = typecheck_expr_expecting te gx lx e1 texp in
      let e2', t2 = typecheck_expr_expecting te gx lx e2 (Expect_typ t1) in
      let t = typecheck_binary_op op t1 t2 in
      (Barocq.EBinaryOp (op, e1', e2'), t)
  | EArrayGet (e1, e2) ->
      let e1', t1 = typecheck_expr_expecting te gx lx e1 Expect_array in
      let e2', _ =
        typecheck_expr_expecting te gx lx e2 (Expect_typ (CInt32 Unsigned))
      in
      begin
        match t1 with
        | CArray ta -> (Barocq.EArrayGet (e1', e2'), ta)
        | _ -> assert false
      end
  | EArraySet (e1, e2, e3) ->
      let e1', t1 = typecheck_expr_expecting te gx lx e1 Expect_array in
      let e2', _ =
        typecheck_expr_expecting te gx lx e2 (Expect_typ (CInt32 Unsigned))
      in
      begin
        match t1 with
        | CArray ta ->
            let e3', _ = typecheck_expr_expecting te gx lx e3 (Expect_typ ta) in
            (Barocq.EArraySet (e1', e2', e3'), t1)
        | _ -> assert false
      end
  | EStructProj (e1, f) ->
      let e1', t1 = typecheck_expr_expecting te gx lx e1 Expect_struct in
      begin
        match t1 with
        | CStruct st ->
            let tf = typecheck_struct_proj te.tenv_structs st f in
            (Barocq.EStructProj (e1', f.content), tf)
        | _ -> assert false
      end
  | EStructUpdate (e1, f, e2) ->
      let e1', t1 = typecheck_expr_expecting te gx lx e1 Expect_struct in
      begin
        match t1 with
        | CStruct st ->
            let tf = typecheck_struct_proj te.tenv_structs st f in
            let e2', _ = typecheck_expr_expecting te gx lx e2 (Expect_typ tf) in
            (Barocq.EStructUpdate (e1', f.content, e2'), t1)
        | _ -> assert false
      end
  | EApp (e1, args) ->
      let e1', t1 = typecheck_expr_expecting te gx lx e1 Expect_function in
      begin
        match t1 with
        | CFun (tparams, tret) ->
            let args', tapp =
              typecheck_app
                te
                gx
                lx
                tparams
                tret
                args
                (List.length tparams)
                (List.length args)
            in
            (Barocq.EApp (e1', args'), tapp)
        | _ -> assert false
      end
  | EIfThenElse (e1, e2, e3) ->
      let e1', _ = typecheck_expr_expecting te gx lx e1 (Expect_typ CBool) in
      let e2', t2 = typecheck_expr te gx lx e2 in
      let e3', _ = typecheck_expr_expecting te gx lx e3 (Expect_typ t2) in
      (Barocq.EIfThenElse (e1', e2', e3'), t2)
  | ELetIn (x, e1, e2) ->
      let e1', t1 = typecheck_expr te gx lx e1 in
      let lx' =
        match Typing.lcontext_update lx x.content t1 with
        | Errors.OK lx' -> lx'
        | Errors.Error _ -> error (Variable_shadowing_diff_type (x.content, t1))
      in
      let e2', t2 = typecheck_expr te gx lx' e2 in
      (Barocq.ELetIn (x.content, e1', e2'), t2)

and typecheck_expr (te : tenv) (gx : gcontext) (lx : lcontext) (e : expr) :
    Barocq.expr * ctyp =
  try typecheck_raw_expr te gx lx e.content
  with Error (cause, loc) -> update_error_loc cause loc e

and typecheck_expr_expecting (te : tenv) (gx : gcontext) (lx : lcontext)
    (e : expr) (texp : expected_typ) : Barocq.expr * ctyp =
  try
    let ((e', ty) as r) = typecheck_raw_expr te gx lx e.content in
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

and typecheck_app (te : tenv) (gx : gcontext) (lx : lcontext)
    (tparams : ctyp list) (tret : ctyp) (args : expr list) (arity : int)
    (nbargs : int) : Barocq.expr list * ctyp =
  match (tparams, args) with
  | [], [] -> ([], tret)
  | tp :: tparams', a :: args' ->
      let a', _ = typecheck_expr_expecting te gx lx a (Expect_typ tp) in
      let r, t = typecheck_app te gx lx tparams' tret args' arity nbargs in
      (a' :: r, t)
  | _, _ -> error (Wrong_argument_number (arity, nbargs))

let rec typecheck_literal (te : tenv) (ty : ctyp) (l : literal) : Syntax.literal
    =
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
        let a' = List.map (typecheck_literal te ta) a in
        Syntax.LArray a'
    | LStruct (st, sid1), CStruct sid2 -> begin
        match types_get te.tenv_structs sid1.content with
        | Errors.OK fields ->
            let st' = typecheck_struct_lit te sid1.content st fields in
            if sid1.content <> sid2 then
              error
                (Type_mismatch
                   (Expect_typ ty, Current_typ (CStruct sid1.content)))
            else Syntax.LStruct (st', sid1.content)
        | Errors.Error _ -> error (Unknown_type sid1.content) ~loc:(Some sid1)
      end
    | (LTrue | LFalse), _ ->
        error (Type_mismatch (Expect_typ ty, Current_typ CBool))
    | LInt32 (_, s), _ ->
        error (Type_mismatch (Expect_typ ty, Current_typ (CInt32 s)))
    | LInt64 (_, s), _ ->
        error (Type_mismatch (Expect_typ ty, Current_typ (CInt32 s)))
    | LArray _, _ -> error (Type_mismatch (Expect_typ ty, Current_array))
    | LStruct _, _ -> error (Type_mismatch (Expect_typ ty, Current_struct))
  with Error (cause, loc) -> update_error_loc cause loc l

and typecheck_struct_lit (te : tenv) (sid : Syntax.ident)
    (st : (ident * literal) list) (fields : (Syntax.ident * ctyp) list) :
    (Syntax.ident * Syntax.literal) list =
  match st with
  | [] -> []
  | (fname, lit) :: st' -> begin
      match List.assoc_opt fname.content fields with
      | Some ftyp ->
          let lit' = typecheck_literal te ftyp lit in
          let r = typecheck_struct_lit te sid st' fields in
          (fname.content, lit') :: r
      | None -> error (Unknown_field (fname.content, sid)) ~loc:(Some fname)
    end

let find_duplicate_ident (l : ident list) : ident option =
  let rec aux l =
    match l with
    | [] -> None
    | id :: l' ->
        if List.exists (fun x -> x.content = id.content) l' then Some id
        else aux l'
  in
  aux (List.rev l)

let typecheck_function (te : tenv) (gx : gcontext) (x : ident) (f : func) :
    Barocq.coq_function * ctyp =
  match find_duplicate_ident (List.map fst f.fn_params) with
  | Some p -> error (Duplicated_param (p.content, x.content)) ~loc:(Some p)
  | None ->
      let tret = styp_to_ctyp te f.fn_return in
      let params =
        List.map
          (fun (pid, styp) -> (pid.content, styp_to_ctyp te styp))
          f.fn_params
      in
      let ty =
        let tparams = List.map snd params in
        CFun (tparams, tret)
      in
      let lx =
        List.fold_left
          (fun acc (pid, ptyp) ->
            match Typing.lcontext_update acc pid ptyp with
            | Errors.OK acc' -> acc'
            | Errors.Error _ -> assert false)
          PTree.empty
          params
      in
      let body, _ =
        typecheck_expr_expecting te gx lx f.fn_body (Expect_typ tret)
      in
      let f' =
        {
          Syntax.fn_return = tret;
          Syntax.fn_params = params;
          Syntax.fn_body = body;
        }
      in
      (f', ty)

let typecheck_globdef (te : tenv) (gx : gcontext) (def : globdef) :
    Barocq.globdef option * tenv * gcontext =
  match def with
  | DefAlias (alias, sty) ->
      let ty = styp_to_ctyp te sty in
      (None, tenv_update_alias te alias ty, gx)
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
                (fname.content, styp_to_ctyp te ftyp))
              fields
          in
          let def' = Barocq.DefStruct (sid.content, fields') in
          (Some def', tenv_update_structs te sid fields', gx)
    end
  | DefConst (cid, l, sty) ->
      let ty = styp_to_ctyp te sty in
      let l' = typecheck_literal te ty l in
      let def' = Barocq.DefConst (cid.content, l', ty) in
      (Some def', te, gcontext_update gx cid ty)
  | DefFun (x, f) ->
      let f', ty = typecheck_function te gx x f in
      let def' = Barocq.DefFun (x.content, f') in
      (Some def', te, gcontext_update gx x ty)

let typecheck_program (prog : program) : Barocq.program =
  let prog, _, _ =
    List.fold_left
      (fun (prog, te, gx) def ->
        let def', te', gx' = typecheck_globdef te gx def in
        match def' with
        | Some def' -> (def' :: prog, te', gx')
        | None -> (prog, te', gx'))
      ([], tenv_empty, PTree.empty)
      prog
  in
  List.rev prog

let typecheck_command (te : tenv) (gx : gcontext) (cmd : command) :
    Barocq.command option * tenv * gcontext =
  match cmd with
  | CmdDef d ->
      let d', te', gx' = typecheck_globdef te gx d in
      begin
        match d' with
        | Some d' -> (Some (Barocq.CmdDef d'), te', gx')
        | None -> (None, te', gx')
      end
  | CmdExpr e ->
      let e', _ = typecheck_expr te gx PTree.empty e in
      (Some (Barocq.CmdExpr e'), te, gx)

let typecheck_xprogram (xprog : xprogram) : Barocq.xprogram =
  let prog, _, _ =
    List.fold_left
      (fun (xprog, te, gx) def ->
        let cmd', te', gx' = typecheck_command te gx def in
        match cmd' with
        | Some cmd' -> (cmd' :: xprog, te', gx')
        | None -> (xprog, te', gx'))
      ([], tenv_empty, PTree.empty)
      xprog
  in
  List.rev prog
