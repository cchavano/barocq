open Printf
open PrintCommon
open Types
open Syntax
open BarocqShallow.Monadic

let int_to_rocq (i : Integers.Int.int) (ty : mtyp) : string =
  let si =
    match ty with
    | MInt32 Signed -> i32_to_string i
    | MInt32 Unsigned -> u32_to_string i
    | _ -> assert false
  in
  sprintf "Int.repr %s%%Z" si

let int64_to_rocq (i : Integers.Int64.int) (ty : mtyp) : string =
  let si =
    match ty with
    | MInt64 Signed -> i64_to_string i
    | MInt64 Unsigned -> u64_to_string i
    | _ -> assert false
  in
  sprintf "Int.repr %s%%Z" si

let unary_op_to_rocq (op : unary_op) : string =
  match op with
  | UopNotbool -> "negb"
  | UopNotint -> "Int.not"
  | UopNeg -> "Int.neg"

let binary_op_to_rocq (ty : mtyp) (op : binary_op) : string =
  let intmod, suffix =
    match ty with
    | MInt32 Signed -> ("Int", "s")
    | MInt32 Unsigned -> ("Int", "u")
    | MInt64 Signed -> ("Int", "s")
    | MInt64 Unsigned -> ("Int64", "u")
    | _ -> ("", "")
  in
  let intop (o : string) =
    let suffix =
      match o with
      | "add" | "sub" | "mul" | "and" | "or" | "xor" | "shl" -> ""
      | "shr" | "cmp" | "lt" -> if suffix = "s" then "" else suffix
      | _ -> suffix
    in
    sprintf "%s.%s%s" intmod o suffix
  in
  match op with
  | BopAndbool -> "andb"
  | BopOrbool -> "orb"
  | BopXorbool -> "xorb"
  | BopAdd -> intop "add"
  | BopSub -> intop "sub"
  | BopMul -> intop "mul"
  | BopDiv -> intop "div"
  | BopMod -> intop "mod"
  | BopAndint -> intop "and"
  | BopOrint -> intop "or"
  | BopXorint -> intop "xor"
  | BopShl -> intop "shl"
  | BopShr -> intop "shr"
  | BopEq -> (
      match ty with
      | MBool -> "eqb"
      | _ -> intop "eq")
  | BopNeq -> (
      match ty with
      | MBool -> "neqb"
      | _ -> sprintf "%s %s" (intop "cmp") "Cne")
  | BopLt -> intop "lt"
  | BopGt -> sprintf "%s %s" (intop "cmp") "Cgt"
  | BopLe -> sprintf "%s %s" (intop "cmp") "Cle"
  | BopGe -> sprintf "%s %s" (intop "cmp") "Cge"

let is_simpl_atom (a : atom) : bool =
  match a with
  | ATrue _ | AFalse _ | AVar _ -> true
  | _ -> false

let rec atom_to_rocq (a : atom) : string =
  match a with
  | ATrue _ -> "true"
  | AFalse _ -> "false"
  | AInt32 (i, ty) -> int_to_rocq i ty
  | AInt64 (i, ty) -> int64_to_rocq i ty
  | AVar (x, _) -> ident_to_string x
  | AUnaryOp (op, a, _) -> sprintf "%s %s" (unary_op_to_rocq op) (opt_parens a)
  | ABinaryOp (op, a1, a2, ty) ->
      sprintf
        "%s %s %s"
        (binary_op_to_rocq ty op)
        (opt_parens a1)
        (opt_parens a2)
  | AStructProj (a1, x, _) ->
      sprintf "%s %s" (ident_to_string x) (opt_parens a1)
  | AStructUpdate (a1, x, a2, ty) ->
      let stid =
        match ty with
        | MStruct st -> st
        | _ -> assert false
      in
      sprintf
        "set_%s_%s %s %s"
        (ident_to_string stid)
        (ident_to_string x)
        (opt_parens a1)
        (opt_parens a2)
  | ALambda (params, a1, _) ->
      sprintf
        "fun %s => %s"
        (list_to_string "" "" " " ident_to_string params)
        (opt_parens a1)
  | ALambdaRet (params, a1, _) ->
      sprintf
        "fun %s => ret %s"
        (list_to_string "" "" " " ident_to_string params)
        (opt_parens a1)
  | AApp (f, args, _) ->
      sprintf
        "%s %s"
        (ident_to_string f)
        (list_to_string "" "" " " ident_to_string args)

and opt_parens (a : atom) : string =
  PrintCommon.opt_parens is_simpl_atom atom_to_rocq a

let rec expr_to_rocq_rec (prefix : string) (e : expr) : string =
  let prefix' = prefix ^ indent in
  let str =
    match e with
    | EAtom (a, _) -> atom_to_rocq a
    | EArrayGet (a1, a2, _) ->
        sprintf "Array.get %s %s" (opt_parens a1) (opt_parens a2)
    | EArraySet (a1, a2, a3, _) ->
        sprintf
          "Array.set %s %s %s"
          (opt_parens a1)
          (opt_parens a2)
          (opt_parens a3)
    | EApp (a1, args, _) ->
        let sargs =
          match args with
          | [] -> "tt"
          | _ -> list_to_string "" "" " " opt_parens args
        in
        sprintf "%s %s" (opt_parens a1) sargs
    | EIfThenElse (a1, e2, e3, _) ->
        sprintf
          "if %s then\n%s\n%selse\n%s"
          (opt_parens a1)
          (expr_to_rocq_rec prefix' e2)
          prefix
          (expr_to_rocq_rec prefix' e3)
    | ELetIn (x, e1, e2, _) -> (
        match e1 with
        | ELetIn _ | ELetMon _ | EIfThenElse _ ->
            sprintf
              "let %s :=\n%s\n%sin\n%s"
              (ident_to_string x)
              (expr_to_rocq_rec prefix' e1)
              prefix
              (expr_to_rocq_rec prefix e2)
        | _ ->
            sprintf
              "let %s := %s in\n%s"
              (ident_to_string x)
              (expr_to_rocq_rec "" e1)
              (expr_to_rocq_rec prefix e2))
    | ELetMon (x, e1, e2, _) -> (
        match e1 with
        | ELetIn _ | ELetMon _ | EIfThenElse _ ->
            sprintf
              "let* %s :=\n%s\n%sin\n%s"
              (ident_to_string x)
              (expr_to_rocq_rec prefix' e1)
              prefix
              (expr_to_rocq_rec prefix e2)
        | _ ->
            sprintf
              "let* %s := %s in\n%s"
              (ident_to_string x)
              (expr_to_rocq_rec "" e1)
              (expr_to_rocq_rec prefix e2))
    | ERet (a1, _) -> sprintf "ret %s" (opt_parens a1)
  in
  prefix ^ str

let expr_to_rocq (e : expr) : string = expr_to_rocq_rec PrintCommon.indent e

let rec is_simpl_mtyp (ty : mtyp) : bool =
  match ty with
  | MBool | MInt32 _ | MInt64 _ | MStruct _ -> true
  | MRes ty' -> is_simpl_mtyp ty'
  | _ -> false

let rec mtyp_to_rocq (ty : mtyp) : string =
  match ty with
  | MBool -> "bool"
  | MInt32 _ -> "int"
  | MInt64 _ -> "int64"
  | MArray ta -> sprintf "array %s" (opt_parens ta)
  | MStruct ts -> ident_to_string ts
  | MFun (tparams, tret) -> (
      match tparams with
      | [] -> sprintf "unit -> %s" (opt_parens tret)
      | _ ->
          List.fold_right
            (fun t acc -> sprintf "%s -> %s" (opt_parens t) acc)
            tparams
            (opt_parens tret))
  | MRes ty' -> sprintf "res %s" (opt_parens ty')

and opt_parens (ty : mtyp) : string =
  PrintCommon.opt_parens is_simpl_mtyp mtyp_to_rocq ty

let param_to_rocq (param : ident * mtyp) : string =
  sprintf "(%s: %s)" (ident_to_string (fst param)) (mtyp_to_rocq (snd param))

let param_list_to_rocq (params : (ident * mtyp) list) : string =
  match params with
  | [] -> "(_: unit)"
  | _ -> list_to_string "" "" " " param_to_rocq params

let function_to_rocq (f : coq_function) : string =
  sprintf
    "%s : %s :=\n%s"
    (param_list_to_rocq f.fn_params)
    (mtyp_to_rocq f.fn_return)
    (expr_to_rocq f.fn_body)

let is_simpl_lit (l : literal) : bool =
  match l with
  | LTrue | LFalse -> true
  | _ -> false

let rec literal_to_rocq (l : literal) : string =
  match l with
  | LTrue -> "true"
  | LFalse -> "false"
  | LInt32 (i, s) -> int_to_rocq i (MInt32 s) (* Check for signedness ? *)
  | LInt64 (i, s) -> int64_to_rocq i (MInt64 s) (* Check for signedness ? *)
  | LArray la -> list_to_string_bracket literal_to_rocq la
  | LStruct (st, _) -> struct_lit_to_rocq st

and field_lit_to_rocq (fl : ident * literal) : string =
  sprintf "%s := %s" (ident_to_string (fst fl)) (opt_parens (snd fl))

and struct_lit_to_rocq (st : (ident * literal) list) : string =
  list_to_string "{| " " |}" "; " field_lit_to_rocq st

and opt_parens (l : literal) : string =
  PrintCommon.opt_parens is_simpl_lit literal_to_rocq l

let field_typ_to_rocq ((fname, ftyp) : ident * mtyp) : string =
  sprintf "%s%s: %s" indent (ident_to_string fname) (mtyp_to_rocq ftyp)

let structtyp_to_rocq (id : ident) (fields : (ident * mtyp) list) : string =
  sprintf
    "Record %s := {\n%s\n}."
    (ident_to_string id)
    (list_to_string "" "" ";\n" field_typ_to_rocq fields)

let globdef_to_rocq (def : globdef) : string =
  match def with
  | DefConst (x, l, ty) ->
      sprintf
        "Definition %s : %s := %s."
        (ident_to_string x)
        (mtyp_to_rocq ty)
        (literal_to_rocq l)
  | DefFun (x, f) ->
      sprintf "Definition %s %s." (ident_to_string x) (function_to_rocq f)

let gen_field_setter (id : ident) ((fname, ftyp) : ident * mtyp) (args : string)
    : string =
  let id_str = ident_to_string id in
  let fname_str = ident_to_string fname in
  sprintf
    "Definition set_%s_%s (s: %s) (v: %s) : %s :=\n%sBuild_%s %s."
    id_str
    fname_str
    id_str
    (mtyp_to_rocq ftyp)
    id_str
    indent
    id_str
    args

let gen_field_setter_arg (id : ident) (x : ident) ((fname, ftyp) : ident * mtyp)
    : string =
  if Utils.ident_eq_dec x fname then "v"
  else sprintf "(%s s)" (ident_to_string fname)

let gen_field_setter_args (id : ident) (fields : (ident * mtyp) list)
    (x : ident) : string =
  list_to_string "" "" " " (fun field -> gen_field_setter_arg id x field) fields

let print_struct_setters (out : out_channel) (id : ident)
    (fields : (ident * mtyp) list) : unit =
  List.iter
    (fun field ->
      let args = gen_field_setter_args id fields (fst field) in
      fprintf out "%s\n\n" (gen_field_setter id field args))
    fields

let headers : string =
  "From Coq Require Import List BinIntDef.\n\
   From compcert Require Import Integers.\n\
   From BarocqComp Require Import Error Array.\n\
   Import ListNotations.\n\n\
   Open Scope error_monad_scope.\n\n"

let print_program (out : out_channel) (prog : program) : unit =
  let types = prog.prog_types in
  let defs = prog.prog_defs in
  let s, e =
    match (types, defs) with
    | [], [] -> ("", "")
    | _ :: _, [] -> ("\n", "")
    | _ :: _, _ :: _ -> ("\n\n", "\n")
    | [], _ :: _ -> ("", "\n")
  in
  fprintf out "%s" headers;
  print_list out "" s "\n\n" (fun (x, tx) -> structtyp_to_rocq x tx) types;
  List.iter (fun (id, fields) -> print_struct_setters out id fields) types;
  print_list out "" e "\n\n" globdef_to_rocq defs
