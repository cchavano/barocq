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
  let si =
    if Integers.Int.lt i Integers.Int.zero then sprintf "(%s)" si else si
  in
  sprintf "Int.repr %s%%Z" si

let int64_to_deep (i : Integers.Int64.int) (s : signedness) : string =
  let si =
    match s with
    | Signed -> i64_to_string i
    | Unsigned -> u64_to_string i
  in
  let si =
    if Integers.Int64.lt i Integers.Int64.zero then sprintf "(%s)" si else si
  in
  sprintf "Int64.repr %s%%Z" si

let unary_op_to_deep (op : unary_op) : string =
  match op with
  | UopNotbool -> "UopNotbool"
  | UopNotint -> "UopNotint"
  | UopNeg -> "UopNeg"
  | UopPlus -> "UopPlus"

let binary_op_to_deep (op : binary_op) : string =
  match op with
  | BopAndbool -> "BopAndbool"
  | BopOrbool -> "BopOrbool"
  | BopXorbool -> "BopXorbool"
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

let is_simpl_btyp (ty : btyp) : bool =
  match ty with
  | BBool | BInt32 _ | BInt64 _ -> true
  | _ -> false

let rec btyp_to_deep (ty : btyp) : string =
  match ty with
  | BBool -> "bool_t"
  | BInt32 Signed -> "int32_t"
  | BInt32 Unsigned -> "uint32_t"
  | BInt64 Signed -> "int64_t"
  | BInt64 Unsigned -> "uint64_t"
  | BArray ta -> sprintf "BArray %s" (opt_parens ta)
  | BRecord ts -> sprintf "BRecord %s" (ident_to_deep ts)
  | BAbs t -> sprintf "BAbs %s" (ident_to_deep t)
  | BFun (tparams, tret) ->
      sprintf
        "BFun %s %s"
        (list_to_string_bracket btyp_to_deep tparams)
        (opt_parens tret)

and opt_parens (ty : btyp) : string =
  PrintCommon.opt_parens is_simpl_btyp btyp_to_deep ty

let rec expr_to_deep (prefix : string) (e : expr) : string =
  let prefix' = prefix ^ indent in
  match e with
  | ETrue -> "ETrue"
  | EFalse -> "EFalse"
  | EInt32 (i, s) ->
      sprintf "EInt32 (%s) %s" (int_to_deep i s) (signedness_to_deep s)
  | EInt64 (i, s) ->
      sprintf "EInt64 (%s) %s" (int64_to_deep i s) (signedness_to_deep s)
  | EVar x -> sprintf "EVar %s" (ident_to_deep x)
  | ECast (e1, ty) ->
      sprintf "ECast (%s) (%s)" (expr_to_deep prefix e1) (btyp_to_deep ty)
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
  | ERecordProj (e1, x) ->
      sprintf "ERecordProj (%s) %s" (expr_to_deep "" e1) (ident_to_deep x)
  | ERecordUpdate (e1, x, e2) ->
      sprintf
        "ERecordUpdate (%s) %s (%s)"
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
  | ELetIn (x, e1, e2) -> begin
      match e1 with
      | EIfThenElse _ ->
          sprintf
            "ELetIn %s\n%s(%s)\n%s(%s)"
            (ident_to_deep x)
            prefix'
            (expr_to_deep prefix' e1)
            prefix'
            (expr_to_deep prefix' e2)
      | _ ->
          sprintf
            "ELetIn %s (%s)\n%s(%s)"
            (ident_to_deep x)
            (expr_to_deep "" e1)
            prefix'
            (expr_to_deep prefix' e2)
    end

and access_to_deep (ac : access) : string =
  match ac with
  | AcRecordField f -> sprintf "AcRecordField %s" (ident_to_string f)
  | AcArrayIndex e -> sprintf "AcArrayIndex (%s)" (expr_to_deep "" e)

let params_to_deep (params : (ident * btyp) list) : string =
  list_to_string_bracket
    (fun (id, ty) -> sprintf "(%s, %s)" (ident_to_deep id) (btyp_to_deep ty))
    params

let function_to_deep (f : coq_function) : string =
  let prefix = String.make 4 ' ' in
  sprintf
    "{|\n%sfn_return := %s;\n%sfn_params := %s;\n%sfn_body :=\n%s%s\n|}"
    indent
    (btyp_to_deep f.fn_return)
    indent
    (params_to_deep f.fn_params)
    indent
    prefix
    (expr_to_deep prefix f.fn_body)

let fields_to_deep (fields : (ident * btyp) list) : string =
  sprintf
    "[\n%s\n]"
    (list_to_string
       ~delim:("", "")
       ~sep:";\n"
       (fun (id, ty) ->
         sprintf "%s(%s, %s)" indent (ident_to_deep id) (btyp_to_deep ty))
       fields)

let rec literal_to_deep (l : literal) : string =
  match l with
  | LTrue -> "LTrue"
  | LFalse -> "LFalse"
  | LInt32 (i, s) ->
      sprintf "LInt32 (%s) %s" (int_to_deep i s) (signedness_to_deep s)
  | LInt64 (i, s) ->
      sprintf "LInt64 (%s) %s" (int64_to_deep i s) (signedness_to_deep s)
  | LArray la -> sprintf "LArray %s" (list_to_string_bracket literal_to_deep la)
  | LRecord (ls, id) ->
      sprintf "LRecord %s %s" (fields_lit_to_deep ls) (ident_to_deep id)

and fields_lit_to_deep (fields : (ident * literal) list) : string =
  list_to_string_bracket
    (fun (id, li) -> sprintf "(%s, %s)" (ident_to_deep id) (literal_to_deep li))
    fields

let globdef_to_coqdef (def : globdef) : string =
  let def_format = sprintf "Definition %s : %s := %s." in
  match def with
  | DefType (id, fields) ->
      def_format
        (sprintf "record_%s" (ident_to_string id))
        "list (ident * btyp)"
        (fields_to_deep fields)
  | DefConst (id, l, _) ->
      def_format
        (sprintf "const_%s" (ident_to_string id))
        "Syntax.literal"
        (literal_to_deep l)
  | DefFun (id, f) ->
      def_format
        (sprintf "fun_%s" (ident_to_string id))
        "Barocq.function"
        (function_to_deep f)
  | _ -> ""

let print_globdefs (out : out_channel) (defs : globdef list) : unit =
  let defs =
    List.filter
      (fun d ->
        match (d : Barocq.globdef) with
        | DefType _ | DefConst _ | DefFun _ -> true
        | _ -> false)
      defs
  in
  print_list out ~delim:("", "\n") ~sep:"\n\n" globdef_to_coqdef defs

let param_attr_to_deep (attr : param_attr) : string =
  match attr with
  | AttrNone -> "AttrNone"
  | AttrReadonly -> "AttrReadonly"
  | AttrWrite -> "AttrWrite"

let globdef_to_deep (def : globdef) : string =
  match def with
  | DefType (id, fields) ->
      sprintf "DefType %s record_%s" (ident_to_deep id) (ident_to_string id)
  | DefConst (id, l, ty) ->
      sprintf
        "DefConst %s const_%s (%s)"
        (ident_to_deep id)
        (ident_to_string id)
        (btyp_to_deep ty)
  | DefFun (id, f) ->
      sprintf "DefFun %s fun_%s" (ident_to_deep id) (ident_to_string id)
  | DeclType (id, tk) ->
      let st_or_un =
        match tk with
        | Ctypes.Struct -> "Struct"
        | Ctypes.Union -> "Union"
      in
      sprintf "DeclType %s %s" (ident_to_deep id) st_or_un
  | DeclConst (id, ty) ->
      sprintf "DeclConst %s (%s)" (ident_to_deep id) (btyp_to_deep ty)
  | DeclFun (id, tparams, tret) ->
      sprintf
        "DeclFun %s (%s) (%s)"
        (ident_to_deep id)
        (list_to_string_bracket
           (fun (attr, ty) ->
             sprintf "(%s, %s)" (param_attr_to_deep attr) (btyp_to_deep ty))
           tparams)
        (btyp_to_deep tret)

let prim_types : string =
  "Definition bool_t := BBool.\n\n\
   Definition int32_t := BInt32 Signed.\n\n\
   Definition uint32_t := BInt32 Unsigned.\n\n\
   Definition int64_t := BInt64 Signed.\n\n\
   Definition uint64_t := BInt64 Unsigned.\n"

let imports : string =
  "From Coq Require Import String List BinIntDef.\n\
   From compcert Require Import Integers Ctypes Clightdefs.\n\
   From BarocqComp Require Import Types Syntax Barocq.\n\
   Import ClightNotations.\n\
   Import ListNotations.\n\n\
   Open Scope string_scope.\n\
   Open Scope clight_scope.\n"

let print_program (out : out_channel) (prog : program) : unit =
  fprintf out "%s" imports;
  if prog <> [] then begin
    fprintf out "\n";
    fprintf out "%s" prim_types;
    fprintf out "\n";
    print_globdefs out prog;
    fprintf out "\n";
    print_list
      out
      ~delim:("Definition prog : Barocq.program := [\n", "\n].\n")
      ~sep:";\n"
      (fun d -> sprintf "%s%s" indent (globdef_to_deep d))
      prog
  end
