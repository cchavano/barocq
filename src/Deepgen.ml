open Printf
open Types
open Syntax
open Barocq
open PrintCommon

let ident_to_deep (id : ident) : string = sprintf "$\"%s\"" (ident_to_string id)

let int_to_deep (i : Integers.Int.int) (s : signedness) : string =
  let si =
    match s with
    | Signed -> i32_to_string i
    | Unsigned -> u32_to_string i
  in
  sprintf "Int.repr %s%%Z" si

let int64_to_deep (i : Integers.Int64.int) (s : signedness) : string =
  let si =
    match s with
    | Signed -> i64_to_string i
    | Unsigned -> u64_to_string i
  in
  sprintf "Int.repr %s%%Z" si

let unary_op_to_deep (op : unary_op) : string =
  match op with
  | UopNotbool -> "UopNotBool"
  | UopNotint -> "UopNotInt"
  | UopNeg -> "UopNeg"

let binary_op_to_deep (op : binary_op) : string =
  match op with
  | BopAndbool -> "BopAndBool"
  | BopOrbool -> "BopOrBool"
  | BopXorbool -> "BopXorBool"
  | BopAdd -> "BopAdd"
  | BopSub -> "BopSub"
  | BopMul -> "BopMul"
  | BopDiv -> "BopDiv"
  | BopMod -> "BopMod"
  | BopAndint -> "BopAndint"
  | BopOrint -> "BopOrint"
  | BopXorint -> "BopXorint"
  | BopShl -> "BopShl"
  | BopShr -> "BopShr"
  | BopEq -> "BopEq"
  | BopNeq -> "BopNeq"
  | BopLt -> "BopLt"
  | BopGt -> "BopGt"
  | BopLe -> "BopLe"
  | BopGe -> "BopGe"

let signedness_to_deep (s : signedness) : string =
  match s with
  | Signed -> "Signed"
  | Unsigned -> "Unsigned"

let rec expr_to_deep (prefix : string) (e : expr) : string =
  let prefix' = prefix ^ indent in
  match e with
  | ETrue -> "ETrue"
  | EFalse -> "EFalse"
  | EInt32 (i, s) ->
      sprintf "EInt32 (%s) %s" (int_to_deep i s) (signedness_to_deep s)
  | EInt64 (i, s) ->
      sprintf "EInt64 (%s) %s" (int_to_deep i s) (signedness_to_deep s)
  | EVar x -> sprintf "EVar %s" (ident_to_deep x)
  | EUnaryOp (op, e1) ->
      sprintf "EUnaryOp %s (%s)" (unary_op_to_deep op) (expr_to_deep "" e1)
  | EBinaryOp (op, e1, e2) ->
      sprintf
        "EBinaryOp %s (%s) (%s)"
        (binary_op_to_deep op)
        (expr_to_deep "" e1)
        (expr_to_deep "" e2)
  | EArrayGet (e1, e2) ->
      sprintf "EArrayGet (%s) (%s)" (expr_to_deep "" e1) (expr_to_deep "" e2)
  | EArraySet (e1, e2, e3) ->
      sprintf
        "EArraySet (%s) (%s) (%s)"
        (expr_to_deep "" e1)
        (expr_to_deep "" e2)
        (expr_to_deep "" e3)
  | EStructProj (e1, x) ->
      sprintf "EStructProj (%s) %s" (expr_to_deep "" e1) (ident_to_deep x)
  | EStructUpdate (e1, x, e2) ->
      sprintf
        "EStructUpdate (%s) %s (%s)"
        (expr_to_deep "" e1)
        (ident_to_deep x)
        (expr_to_deep "" e2)
  | EDeepAccess (e1, acs) ->
      sprintf
        "EDeepAccess (%s) %s"
        (expr_to_deep prefix e1)
        (list_to_string_bracket access_to_deep acs)
  | EApp (e1, args) ->
      sprintf
        "EApp (%s) %s"
        (expr_to_deep "" e1)
        (list_to_string_bracket (expr_to_deep "") args)
  | EIfThenElse (e1, e2, e3) ->
      sprintf
        "EIfThenElse (%s)\n%s(%s)\n%s(%s)"
        (expr_to_deep "" e1)
        prefix'
        (expr_to_deep prefix' e2)
        prefix'
        (expr_to_deep prefix' e3)
  | ELetIn (x, e1, e2) ->
      sprintf
        "ELetIn %s (%s)\n%s(%s)"
        (ident_to_deep x)
        (expr_to_deep "" e1)
        prefix'
        (expr_to_deep prefix' e2)

and access_to_deep (ac : access) : string =
  match ac with
  | AcStructField f -> sprintf "AcStructField %s" (ident_to_string f)
  | AcArrayIndex e -> sprintf "AcArrayIndex (%s)" (expr_to_deep "" e)

let rec ctyp_to_deep (ty : ctyp) : string =
  match ty with
  | CBool -> "CBool"
  | CInt32 s -> sprintf "CInt32 %s" (signedness_to_deep s)
  | CInt64 s -> sprintf "CInt64 %s" (signedness_to_deep s)
  | CArray ta -> sprintf "CArray (%s)" (ctyp_to_deep ta)
  | CStruct ts -> sprintf "CStruct (%s)" (ident_to_deep ts)
  | CFun (tparams, tret) ->
      sprintf
        "CFun %s (%s)"
        (list_to_string_bracket ctyp_to_deep tparams)
        (ctyp_to_deep tret)

let params_to_deep (params : (ident * ctyp) list) : string =
  list_to_string_bracket
    (fun (id, ty) -> sprintf "(%s, %s)" (ident_to_deep id) (ctyp_to_deep ty))
    params

let function_to_deep (f : coq_function) : string =
  let prefix = String.make 4 ' ' in
  sprintf
    "{|\n%sfn_return := %s;\n%sfn_params := %s;\n%sfn_body :=\n%s%s\n|}"
    indent
    (ctyp_to_deep f.fn_return)
    indent
    (params_to_deep f.fn_params)
    indent
    prefix
    (expr_to_deep prefix f.fn_body)

let fields_to_deep (fields : (ident * ctyp) list) : string =
  params_to_deep fields

let rec literal_to_deep (l : literal) : string =
  match l with
  | LTrue -> "LTrue"
  | LFalse -> "LFalse"
  | LInt32 (i, s) ->
      sprintf "LInt32 (%s) %s" (int_to_deep i s) (signedness_to_deep s)
  | LInt64 (i, s) ->
      sprintf "LInt64 (%s) %s" (int64_to_deep i s) (signedness_to_deep s)
  | LArray la -> sprintf "LArray %s" (list_to_string_bracket literal_to_deep la)
  | LStruct (ls, id) ->
      sprintf "LStruct %s %s" (fields_lit_to_deep ls) (ident_to_deep id)

and fields_lit_to_deep (fields : (ident * literal) list) : string =
  list_to_string_bracket
    (fun (id, li) -> sprintf "(%s, %s)" (ident_to_deep id) (literal_to_deep li))
    fields

let globdef_to_coqdef (def : globdef) : string =
  let s1, s2, s3 =
    match def with
    | DefStruct (id, fields) ->
        ( sprintf "_struct_%s" (ident_to_string id),
          "list (ident * ctyp)",
          fields_to_deep fields )
    | DefConst (id, l, _) ->
        ( sprintf "_const_%s" (ident_to_string id),
          "Syntax.literal",
          literal_to_deep l )
    | DefFun (id, f) ->
        ( sprintf "_fun_%s" (ident_to_string id),
          "Barocq.function",
          function_to_deep f )
  in
  sprintf "Definition %s : %s := %s." s1 s2 s3

let rec print_globdefs (out : out_channel) (defs : globdef list) : unit =
  match defs with
  | [] -> ()
  | d :: defs' ->
      fprintf out "%s\n\n" (globdef_to_coqdef d);
      print_globdefs out defs'

let headers : string =
  "From Coq Require Import String List BinIntDef.\n\
   From compcert Require Import Integers Clightdefs.\n\
   From BarocqComp Require Import Types Syntax Barocq.\n\
   Import ClightNotations.\n\
   Import ListNotations.\n\n\
   Open Scope string_scope.\n\
   Open Scope clight_scope.\n\n"

let globdef_to_deep (def : globdef) : string =
  match def with
  | DefStruct (id, fields) ->
      sprintf "DefStruct %s _struct_%s" (ident_to_deep id) (ident_to_string id)
  | DefConst (id, l, ty) ->
      sprintf
        "DefConst %s _const_%s (%s)"
        (ident_to_deep id)
        (ident_to_string id)
        (ctyp_to_deep ty)
  | DefFun (id, f) ->
      sprintf "DefFun %s _fun_%s" (ident_to_deep id) (ident_to_string id)

let print_program (out : out_channel) (prog : program) : unit =
  fprintf out "%s" headers;
  let _ = print_globdefs out prog in
  print_list
    out
    "Definition prog : Barocq.program := [\n"
    "\n]."
    ";\n"
    (fun d -> sprintf "%s%s" indent (globdef_to_deep d))
    prog
