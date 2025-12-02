open Printf
open Types
open Syntax
open Barocq
open PrintUtils
open Typed

let ident_to_deep (id : ident) : string = sprintf "\"%s\"" (ident_to_string id)

let int_to_deep (i : Integers.Int.int) (s : signedness) : string =
  let si =
    match s with
    | Signed ->
        let si = i32_to_string i in
        if Integers.Int.lt i Integers.Int.zero then sprintf "(%s)" si else si
    | Unsigned -> u32_to_string i
  in
  sprintf "Int.repr %s" si

let int64_to_deep (i : Integers.Int64.int) (s : signedness) : string =
  let si =
    match s with
    | Signed ->
        let si = i64_to_string i in
        if Integers.Int64.lt i Integers.Int64.zero then sprintf "(%s)" si
        else si
    | Unsigned -> u64_to_string i
  in
  sprintf "Int64.repr %s" si

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

let layout_to_deep (ly : layout) : string =
  match ly with
  | LyPrim -> "LyPrim"
  | LyBoxed -> "LyBoxed"
  | LyUnboxed sz ->
      let suffix =
        match sz with
        | Some v -> sprintf "(Some %s)" (Camlcoq.Z.to_string v)
        | None -> "None"
      in
      sprintf "LyUnboxed %s" suffix

let opt_parens_layout (ly : layout) : string =
  PrintUtils.opt_parens
    (fun ly ->
      match ly with
      | LyPrim | LyBoxed -> true
      | _ -> false)
    layout_to_deep
    ly

let rec btyp_to_deep (ty : btyp) : string =
  match ty with
  | BBool -> "tbool"
  | BInt32 Signed -> "tint32"
  | BInt32 Unsigned -> "tuint32"
  | BInt64 Signed -> "tint64"
  | BInt64 Unsigned -> "tuint64"
  | BArray (ta, ly) ->
      sprintf "BArray %s %s" (opt_parens_btyp ta) (opt_parens_layout ly)
  | BEnum te -> sprintf "BEnum %s" (ident_to_deep te)
  | BRecord (tr, ub) ->
      sprintf
        "BRecord %s %s"
        (ident_to_deep tr)
        (list_to_string_bracket ident_to_deep ub)
  | BAbs t -> sprintf "BAbs %s" (ident_to_deep t)
  | BFun (tparams, tret) ->
      sprintf
        "BFun %s %s"
        (list_to_string_bracket btyp_to_deep tparams)
        (opt_parens_btyp tret)

and opt_parens_btyp (ty : btyp) : string =
  PrintUtils.opt_parens is_simpl_btyp btyp_to_deep ty

let rec expr_to_deep (prefix : string) (e : Typed.expr) : string =
  let prefix' = prefix ^ indent in
  Typed.(
    match e with
    | ETrue -> "ETrue"
    | EFalse -> "EFalse"
    | EInt32 (i, s) ->
        sprintf "EInt32 (%s) %s" (int_to_deep i s) (signedness_to_deep s)
    | EInt64 (i, s) ->
        sprintf "EInt64 (%s) %s" (int64_to_deep i s) (signedness_to_deep s)
    | EConstr (x, bt) ->
        sprintf "EConstr %s (%s)" (ident_to_deep x) (btyp_to_deep bt)
    | EVar (x, bt) -> sprintf "EVar %s (%s)" (ident_to_deep x) (btyp_to_deep bt)
    | ECast (e1, ty) ->
        sprintf "ECast (%s) (%s)" (expr_to_deep prefix e1) (btyp_to_deep ty)
    | EUnaryOp (op, e1, bt) ->
        sprintf
          "EUnaryOp %s (%s) (%s)"
          (unary_op_to_deep op)
          (expr_to_deep "" e1)
          (btyp_to_deep bt)
    | EBinaryOp (op, e1, e2, bt) ->
        sprintf
          "EBinaryOp %s (%s) (%s) (%s)"
          (binary_op_to_deep op)
          (expr_to_deep "" e1)
          (expr_to_deep "" e2)
          (btyp_to_deep bt)
    | EArrayGet (e1, e2, bt) ->
        sprintf
          "EArrayGet (%s) (%s) (%s)"
          (expr_to_deep "" e1)
          (expr_to_deep "" e2)
          (btyp_to_deep bt)
    | EArraySet (e1, e2, e3, bt) ->
        sprintf
          "EArraySet (%s) (%s) (%s) (%s)"
          (expr_to_deep "" e1)
          (expr_to_deep "" e2)
          (expr_to_deep "" e3)
          (btyp_to_deep bt)
    | ERecordProj (e1, x, bt) ->
        sprintf
          "ERecordProj (%s) %s (%s)"
          (expr_to_deep "" e1)
          (ident_to_deep x)
          (btyp_to_deep bt)
    | ERecordUpdate (e1, x, e2, bt) ->
        sprintf
          "ERecordUpdate (%s) %s (%s) (%s)"
          (expr_to_deep "" e1)
          (ident_to_deep x)
          (expr_to_deep "" e2)
          (btyp_to_deep bt)
    (* | EDeepAccess (e1, acs, bt) ->
        sprintf
          "EDeepAccess (%s) %s (%s)"
          (expr_to_deep prefix e1)
          (list_to_string_bracket access_to_deep acs)
          (btyp_to_deep bt) *)
    | EApp (e1, args, bt) ->
        sprintf
          "EApp (%s) %s (%s)"
          (expr_to_deep "" e1)
          (list_to_string_bracket (expr_to_deep "") args)
          (btyp_to_deep bt)
    | EIfThenElse (e1, e2, e3, bt) ->
        sprintf
          "EIfThenElse (%s)\n%s(%s)\n%s(%s) (%s)"
          (expr_to_deep "" e1)
          prefix'
          (expr_to_deep prefix' e2)
          prefix'
          (expr_to_deep prefix' e3)
          (btyp_to_deep bt)
    | EMatch (e1, cases, bt) ->
        sprintf
          "EMatch (%s) [\n%s\n%s] (%s)"
          (expr_to_deep "" e1)
          (list_to_string ~sep:";\n" (match_case_to_string prefix') cases)
          prefix
          (btyp_to_deep bt)
    | ELetIn (x, e1, e2, bt) -> begin
        match e1 with
        | EIfThenElse _ | EMatch _ ->
            sprintf
              "ELetIn %s\n%s(%s)\n%s(%s) (%s)"
              (ident_to_deep x)
              prefix'
              (expr_to_deep prefix' e1)
              prefix'
              (expr_to_deep prefix' e2)
              (btyp_to_deep bt)
        | _ ->
            sprintf
              "ELetIn %s (%s)\n%s(%s) (%s)"
              (ident_to_deep x)
              (expr_to_deep "" e1)
              prefix'
              (expr_to_deep prefix' e2)
              (btyp_to_deep bt)
      end)

and match_case_to_string (prefix : string)
    ((p, ep) : Benum.pattern * Typed.expr) : string =
  let prefix' = prefix ^ indent in
  let case =
    match p with
    | Benum.PIdent (i, z) ->
        sprintf "PIdent %s %s" (ident_to_deep i) (i32_to_string z)
    | Benum.PWildcard -> sprintf "PWildcard"
  in
  sprintf "%s(%s,\n%s%s)" prefix case prefix' (expr_to_deep prefix' ep)

and access_to_deep (ac : Typed.access) : string =
  match ac with
  | AcRecordField (f, bt) ->
      sprintf "AcRecordField %s (%s)" (ident_to_deep f) (btyp_to_deep bt)
  | AcArrayIndex (e, bt) ->
      sprintf "AcArrayIndex (%s) (%s)" (expr_to_deep "" e) (btyp_to_deep bt)

let params_to_deep (params : (ident * btyp) list) : string =
  list_to_string_bracket
    (fun (id, ty) -> sprintf "(%s, %s)" (ident_to_deep id) (btyp_to_deep ty))
    params

let function_to_deep (f : Typed.coq_function) : string =
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

let rec literal_to_deep (l : literal) : string =
  match l with
  | LTrue -> "LTrue"
  | LFalse -> "LFalse"
  | LInt32 (i, s) ->
      sprintf "LInt32 (%s) %s" (int_to_deep i s) (signedness_to_deep s)
  | LInt64 (i, s) ->
      sprintf "LInt64 (%s) %s" (int64_to_deep i s) (signedness_to_deep s)
  | LArray (la, ta, ly) ->
      sprintf
        "LArray %s %s %s"
        (list_to_string_bracket literal_to_deep la)
        (btyp_to_deep ta)
        (layout_to_deep ly)
  | LRecord (ls, ub, id) ->
      sprintf
        "LRecord %s %s %s"
        (fields_lit_to_deep ls)
        (list_to_string_bracket ident_to_string ub)
        (ident_to_deep id)

and fields_lit_to_deep (fields : (ident * literal) list) : string =
  list_to_string_bracket
    (fun (id, li) -> sprintf "(%s, %s)" (ident_to_deep id) (literal_to_deep li))
    fields

let fields_to_deep (fields : (ident * field_descr) list) : string =
  list_to_string
    ~sep:";\n"
    (fun (id, (ty, ly)) ->
      sprintf
        "%s(%s, (%s, %s))"
        indent2
        (ident_to_deep id)
        (btyp_to_deep ty)
        (layout_to_deep ly))
    fields

let elems_to_deep (elems : ident list) : string =
  list_to_string
    ~sep:";\n"
    (fun e -> sprintf "%s%s" indent2 (ident_to_deep e))
    elems

let globdef_to_coqdef (def : Typed.globdef) : string =
  let typ_format = sprintf "Definition %s : %s :=\n%s%s." in
  let def_format = sprintf "Definition %s : %s := %s." in
  match def with
  | DefType (id, td) -> begin
      match td with
      | TdEnum elems ->
          typ_format
            (sprintf "enum_%s" (ident_to_string id))
            "type_def field_descr"
            indent
            (sprintf "TdEnum [\n%s\n%s]" (elems_to_deep elems) indent)
      | TdRecord fields ->
          typ_format
            (sprintf "record_%s" (ident_to_string id))
            "type_def field_descr"
            indent
            (sprintf "TdRecord [\n%s\n%s]" (fields_to_deep fields) indent)
    end
  | DefConst (id, l, _) ->
      def_format
        (sprintf "const_%s" (ident_to_string id))
        "Syntax.literal"
        (literal_to_deep l)
  | DefFun (id, f) ->
      def_format
        (sprintf "fun_%s" (ident_to_string id))
        "Barocq.Typed.function"
        (function_to_deep f)
  | _ -> ""

let print_globdefs (out : out_channel) (defs : Typed.globdef list) : unit =
  let defs =
    List.filter
      (fun d ->
        match (d : Barocq.Typed.globdef) with
        | Typed.DefType _ | Typed.DefConst _ | Typed.DefFun _ -> true
        | _ -> false)
      defs
  in
  print_list out ~delim:("", "\n") ~sep:"\n\n" globdef_to_coqdef defs

let param_attr_to_deep (attr : param_attr) : string =
  match attr with
  | AttrNone -> "AttrNone"
  | AttrReadonly -> "AttrReadonly"
  | AttrWrite -> "AttrWrite"

let globdef_to_deep (def : Typed.globdef) : string =
  match def with
  | DefType (id, td) ->
      let kind =
        match td with
        | TdEnum _ -> "enum"
        | TdRecord _ -> "record"
      in
      sprintf "DefType %s %s_%s" (ident_to_deep id) kind (ident_to_string id)
  | DefConst (id, l, ty) ->
      sprintf
        "DefConst %s const_%s %s"
        (ident_to_deep id)
        (ident_to_string id)
        (opt_parens_btyp ty)
  | DefFun (id, f) ->
      sprintf "DefFun %s fun_%s" (ident_to_deep id) (ident_to_string id)
  | DeclType (id, su) ->
      let st_or_un =
        match su with
        | SU_struct -> "SU_struct"
        | SU_union -> "SU_union"
      in
      sprintf "DeclType %s %s" (ident_to_deep id) st_or_un
  | DeclConst (id, ty) ->
      sprintf "DeclConst %s %s" (ident_to_deep id) (opt_parens_btyp ty)
  | DeclFun (id, tparams, tret) ->
      sprintf
        "DeclFun %s %s %s"
        (ident_to_deep id)
        (list_to_string_bracket
           (fun (attr, ty) ->
             sprintf "(%s, %s)" (param_attr_to_deep attr) (btyp_to_deep ty))
           tparams)
        (opt_parens_btyp tret)

let print_decomp_remark (out : out_channel) : unit =
  fprintf
    out
    "Remark prog_decomp : (prog = prog_types ++ prog_decls ++ prog_defs)%%list.\n\
     Proof.\n\
     %sreflexivity.\n\
     Qed.\n"
    indent

let prim_types : string =
  "Definition tbool := BBool.\n\n\
   Definition tint32 := BInt32 Signed.\n\n\
   Definition tuint32 := BInt32 Unsigned.\n\n\
   Definition tint64 := BInt64 Signed.\n\n\
   Definition tuint64 := BInt64 Unsigned.\n"

let imports : string =
  "From Coq Require Import String List BinIntDef.\n\
   From compcert Require Import Integers.\n\
   From BarocqComp Require Import Ident Types Syntax Benum Barocq.\n\
   Import Typed.\n\
   Import ListNotations.\n\n\
   Open Scope Z_scope.\n\
   Open Scope string_scope.\n"

let print_program (out : out_channel) (prog : Typed.program) : unit =
  fprintf out "%s" imports;
  if prog <> [] then begin
    fprintf out "\n";
    fprintf out "%s" prim_types;
    fprintf out "\n";
    print_globdefs out prog;
    fprintf out "\n";
    print_list
      out
      ~delim:("Definition prog : Barocq.Typed.program := [\n", "\n].\n")
      ~sep:";\n"
      (fun d -> sprintf "%s%s" indent (globdef_to_deep d))
      prog;
    let types =
      List.filter
        (fun (d : Barocq.Typed.globdef) ->
          match d with
          | DefType _ | DeclType _ -> true
          | _ -> false)
        prog
    in
    let decls =
      List.filter
        (fun (d : Barocq.Typed.globdef) ->
          match d with
          | DeclConst _ | DeclFun _ -> true
          | _ -> false)
        prog
    in
    let defs =
      List.filter
        (fun (d : Barocq.Typed.globdef) ->
          match d with
          | DefConst _ | DefFun _ -> true
          | _ -> false)
        prog
    in
    fprintf out "\n";
    print_list
      out
      ~delim:("Definition prog_types : Barocq.Typed.program := [\n", "\n].\n")
      ~sep:";\n"
      (fun d -> sprintf "%s%s" indent (globdef_to_deep d))
      types;
    fprintf out "\n";
    print_list
      out
      ~delim:("Definition prog_decls : Barocq.Typed.program := [\n", "\n].\n")
      ~sep:";\n"
      (fun d -> sprintf "%s%s" indent (globdef_to_deep d))
      decls;
    fprintf out "\n";
    print_list
      out
      ~delim:("Definition prog_defs : Barocq.Typed.program := [\n", "\n].\n")
      ~sep:";\n"
      (fun d -> sprintf "%s%s" indent (globdef_to_deep d))
      defs;
    fprintf out "\n";
    print_decomp_remark out
  end
