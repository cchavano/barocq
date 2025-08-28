open Printf
open PrintUtils
open Types
open Syntax
open BarocqShallow.Monadic

let rec is_simpl_mtyp (ty : mtyp) : bool =
  match ty with
  | MBool | MInt32 _ | MInt64 _ | MEnum _ | MRecord _ | MAbs _ -> true
  | MRes ty' -> is_simpl_mtyp ty'
  | _ -> false

let rec mtyp_to_rocq (ty : mtyp) : string =
  match ty with
  | MBool -> "bool"
  | MInt32 _ -> "int"
  | MInt64 _ -> "int64"
  | MArray ta -> sprintf "array %s" (opt_parens ta)
  | MEnum te -> ident_to_string te
  | MRecord tr -> ident_to_string tr
  | MAbs t -> ident_to_string t
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
  PrintUtils.opt_parens is_simpl_mtyp mtyp_to_rocq ty

let int_to_rocq (i : Integers.Int.int) (ty : mtyp) : string =
  let si =
    match ty with
    | MInt32 Signed -> i32_to_string i
    | MInt32 Unsigned -> u32_to_string i
    | _ -> assert false
  in
  let si =
    if Integers.Int.lt i Integers.Int.zero then sprintf "(%s)" si else si
  in
  sprintf "Int.repr %s%%Z" si

let int64_to_rocq (i : Integers.Int64.int) (ty : mtyp) : string =
  let si =
    match ty with
    | MInt64 Signed -> i64_to_string i
    | MInt64 Unsigned -> u64_to_string i
    | _ -> assert false
  in
  let si =
    if Integers.Int64.lt i Integers.Int64.zero then sprintf "(%s)" si else si
  in
  sprintf "Int64.repr %s%%Z" si

let cast_to_rocq (src_ty : mtyp) (dst_ty : mtyp) : string =
  let modl ty =
    match ty with
    | MInt32 Signed -> "I32"
    | MInt32 Unsigned -> "U32"
    | MInt64 Signed -> "I64"
    | MInt64 Unsigned -> "U64"
    | _ -> ""
  in
  if dst_ty <> MBool then
    let op =
      match src_ty with
      | MInt32 Signed -> "of_i32"
      | MInt32 Unsigned -> "of_u32"
      | MInt64 Signed -> "of_i64"
      | MInt64 Unsigned -> "of_u64"
      | MBool -> "of_bool"
      | _ -> ""
    in
    sprintf "%s.%s" (modl dst_ty) op
  else sprintf "%s.to_bool" (modl src_ty)

let unary_op_to_rocq (ty : mtyp) (op : unary_op) : string =
  let intmod =
    match ty with
    | MInt32 _ -> "Int"
    | MInt64 _ -> "Int64"
    | _ -> ""
  in
  match op with
  | UopNotbool -> "negb "
  | UopNotint -> sprintf "%s.not " intmod
  | UopNeg -> sprintf "%s.neg " intmod
  | UopPlus -> ""

let binary_op_to_rocq (ty : mtyp) (op : binary_op) : string =
  let intmod, suffix =
    match ty with
    | MInt32 Signed ->
        let modl =
          match op with
          | BopDiv | BopMod -> "I32"
          | _ -> "Int"
        in
        (modl, "s")
    | MInt32 Unsigned ->
        let modl =
          match op with
          | BopDiv | BopMod -> "U32"
          | _ -> "Int"
        in
        (modl, "u")
    | MInt64 Signed ->
        let modl =
          match op with
          | BopDiv | BopMod -> "I64"
          | _ -> "Int64"
        in
        (modl, "s")
    | MInt64 Unsigned ->
        let modl =
          match op with
          | BopDiv | BopMod -> "U64"
          | _ -> "Int64"
        in
        (modl, "u")
    | _ -> ("", "")
  in
  let intop (o : string) =
    let suffix =
      match o with
      | "add" | "sub" | "mul" | "and" | "or" | "xor" | "shl" | "div" | "mod" ->
          ""
      | "shr" | "cmp" | "lt" -> if suffix = "s" then "" else suffix
      | "eq" -> ""
      | _ -> suffix
    in
    sprintf "%s.%s%s" intmod o suffix
  in
  match op with
  | BopAndbool -> "&&"
  | BopOrbool -> "||"
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
      | MEnum t -> sprintf "%s_eq" (ident_to_string t)
      | _ -> intop "eq")
  | BopNeq -> (
      match ty with
      | MBool -> "neqb"
      | MEnum t -> sprintf "%s_neq" (ident_to_string t)
      | _ -> sprintf "%s %s" (intop "cmp") "Cne")
  | BopLt -> intop "lt"
  | BopGt -> sprintf "%s %s" (intop "cmp") "Cgt"
  | BopLe -> sprintf "%s %s" (intop "cmp") "Cle"
  | BopGe -> sprintf "%s %s" (intop "cmp") "Cge"

let is_simpl_atom (a : atom) : bool =
  match a with
  | ATrue _ | AFalse _ | AVar _ -> true
  | _ -> false

let field_name_prefix (ty : mtyp) : string =
  match ty with
  | MRecord rid -> String.lowercase_ascii (ident_to_string rid)
  | _ -> assert false

let typof_atom (a : atom) : mtyp = BarocqShallowgen.Monadification.typof_atom a

let rec atom_to_rocq (a : atom) : string =
  match a with
  | ATrue _ -> "true"
  | AFalse _ -> "false"
  | AInt32 (i, ty) -> int_to_rocq i ty
  | AInt64 (i, ty) -> int64_to_rocq i ty
  | AConstr (x, _) -> ident_to_string x
  | AVar (x, _) -> ident_to_string x
  | ACast (a1, dst_ty, _) ->
      let t1 = typof_atom a1 in
      begin
        match t1 with
        | MEnum tid ->
            if dst_ty = MInt32 Signed then
              sprintf "cast_%s_to_i32 %s" (ident_to_string tid) (opt_parens a1)
            else
              sprintf
                "%s (cast_%s_to_i32 %s)"
                (cast_to_rocq (MInt32 Signed) dst_ty)
                (ident_to_string tid)
                (opt_parens a1)
        | _ -> begin
            match dst_ty with
            | MEnum tid ->
                sprintf
                  "cast_i32_to_%s (%s %s)"
                  (ident_to_string tid)
                  (cast_to_rocq t1 (MInt32 Signed))
                  (opt_parens a1)
            | _ ->
                if t1 = dst_ty then atom_to_rocq a1
                else sprintf "%s %s" (cast_to_rocq t1 dst_ty) (opt_parens a1)
          end
      end
  | AUnaryOp (op, a, _) ->
      let ty = typof_atom a in
      sprintf "%s%s" (unary_op_to_rocq ty op) (opt_parens a)
  | ABinaryOp (op, a1, a2, ty) ->
      let ty1 = typof_atom a1 in
      begin
        match op with
        | BopAndbool | BopOrbool ->
            sprintf
              "%s %s %s"
              (opt_parens a1)
              (binary_op_to_rocq ty1 op)
              (opt_parens a2)
        | _ ->
            sprintf
              "%s %s %s"
              (binary_op_to_rocq ty1 op)
              (opt_parens a1)
              (opt_parens a2)
      end
  | ARecordProj (a1, x, _) ->
      sprintf
        "%s.(%s_%s)"
        (opt_parens a1)
        (field_name_prefix (typof_atom a1))
        (ident_to_string x)
  | ARecordUpdate (a1, x, a2, ty) ->
      sprintf
        "%s <| %s_%s := %s |>"
        (opt_parens a1)
        (field_name_prefix ty)
        (ident_to_string x)
        (atom_to_rocq a2)
  | ALambda (params, a1, _) ->
      sprintf
        "fun %s => %s"
        (list_to_string ~sep:" " ident_to_string params)
        (opt_parens a1)
  | ALambdaRet (params, a1, _) ->
      sprintf
        "fun %s => ret %s"
        (list_to_string ~sep:" " ident_to_string params)
        (opt_parens a1)
  | AApp (f, args, _) ->
      sprintf
        "%s %s"
        (ident_to_string f)
        (list_to_string ~sep:" " ident_to_string args)

and opt_parens (a : atom) : string =
  PrintUtils.opt_parens is_simpl_atom atom_to_rocq a

let rec expr_to_rocq_rec (prefix : string) (e : expr) : string =
  let prefix' = prefix ^ indent in
  let str =
    match e with
    | EAtom (a, _) -> atom_to_rocq a
    | EArrayGet (a1, a2, _) ->
        let sa2 =
          if Archi.ptr64 then opt_parens a2
          else sprintf "(uint_to_uint64 %s)" (opt_parens a2)
        in
        sprintf "Barray.get %s %s" (opt_parens a1) sa2
    | EArraySet (a1, a2, a3, _) ->
        let sa2 =
          if Archi.ptr64 then opt_parens a2
          else sprintf "(uint_to_uint64 %s)" (opt_parens a2)
        in
        sprintf "Barray.set %s %s %s" (opt_parens a1) sa2 (opt_parens a3)
    | EApp (a1, args, _) ->
        let sargs =
          match args with
          | [] -> "tt"
          | _ -> list_to_string ~sep:" " opt_parens args
        in
        sprintf "%s %s" (opt_parens a1) sargs
    | EIfThenElse (a1, e2, e3, _) -> begin
        match e3 with
        | EIfThenElse _ ->
            sprintf
              "if %s then\n%s\n%selse%s"
              (opt_parens a1)
              (expr_to_rocq_rec prefix' e2)
              prefix
              (let e3_str = expr_to_rocq_rec prefix e3 in
               let e3_start = String.length prefix - 1 in
               String.sub e3_str e3_start (String.length e3_str - e3_start))
        | _ ->
            sprintf
              "if %s then\n%s\n%selse\n%s"
              (opt_parens a1)
              (expr_to_rocq_rec prefix' e2)
              prefix
              (expr_to_rocq_rec prefix' e3)
      end
    | EMatch (a1, cases, _) ->
        sprintf
          "match %s with\n%s\n%send"
          (opt_parens a1)
          (list_to_string ~sep:"\n" (match_case_to_string prefix) cases)
          prefix
    | ELetIn (x, e1, e2, _) -> (
        match e1 with
        | ELetIn _ | ELetMon _ | EIfThenElse _ | EMatch _ ->
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
        | ELetIn _ | ELetMon _ | EIfThenElse _ | EMatch _ ->
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
    | ERet (e1, _) -> begin
        match e1 with
        | EAtom (a1, _) -> sprintf "ret %s" (opt_parens a1)
        | EApp _ -> sprintf "ret (%s)" (expr_to_rocq_rec "" e1)
        | _ -> assert false
      end
  in
  prefix ^ str

and match_case_to_string (prefix : string) ((p, ep) : Benum.pattern * expr) :
    string =
  let case =
    match p with
    | Benum.PIdent i -> ident_to_string i
    | Benum.PWildcard -> "_"
  in
  sprintf
    "%s| %s =>\n%s"
    prefix
    case
    (expr_to_rocq_rec (prefix ^ make_indent 2) ep)

let expr_to_rocq (e : expr) : string = expr_to_rocq_rec PrintUtils.indent e

let param_to_rocq (param : ident * mtyp) : string =
  sprintf "(%s: %s)" (ident_to_string (fst param)) (mtyp_to_rocq (snd param))

let param_list_to_rocq (params : (ident * mtyp) list) : string =
  match params with
  | [] -> "(_: unit)"
  | _ -> list_to_string ~sep:" " param_to_rocq params

let function_to_rocq (f : coq_function) : string =
  sprintf
    "%s : %s :=\n%s"
    (param_list_to_rocq f.fn_params)
    (mtyp_to_rocq f.fn_return)
    (expr_to_rocq f.fn_body)

let is_simpl_lit (l : literal) : bool =
  match l with
  | LTrue _ | LFalse _ -> true
  | _ -> false

let rec literal_to_rocq (l : literal) : string =
  match l with
  | LTrue _ -> "true"
  | LFalse _ -> "false"
  | LInt32 (i, t) -> int_to_rocq i t
  | LInt64 (i, t) -> int64_to_rocq i t
  | LArray (la, _) -> list_to_string_bracket literal_to_rocq la
  | LRecord (rc, t) -> begin
      match t with
      | MRecord rid -> record_lit_to_rocq (ident_to_string rid) rc
      | _ -> assert false
    end

and field_lit_to_rocq (rid : string) (fl : ident * literal) : string =
  sprintf
    "%s_%s := %s"
    (String.lowercase_ascii rid)
    (ident_to_string (fst fl))
    (opt_parens (snd fl))

and record_lit_to_rocq (rid : string) (rc : (ident * literal) list) : string =
  list_to_string ~delim:("{| ", " |}") ~sep:"; " (field_lit_to_rocq rid) rc

and opt_parens (l : literal) : string =
  PrintUtils.opt_parens is_simpl_lit literal_to_rocq l

let field_typ_to_rocq (rid : string) ((fname, ftyp) : ident * mtyp) : string =
  sprintf
    "%s%s_%s: %s"
    indent
    (String.lowercase_ascii rid)
    (ident_to_string fname)
    (mtyp_to_rocq ftyp)

let enum_def_to_rocq (ed : enum_def) : string =
  let eid = ident_to_string ed.ed_name in
  sprintf
    "Inductive %s :=\n%s."
    eid
    (list_to_string
       ~sep:"\n"
       (fun e -> sprintf "%s| %s" indent (ident_to_string e))
       ed.ed_elems)

let record_def_to_rocq (rd : record_def) : string =
  let rid = ident_to_string rd.rd_name in
  sprintf
    "Record %s := mk_%s {\n%s\n}."
    rid
    rid
    (list_to_string ~sep:";\n" (field_typ_to_rocq rid) rd.rd_fields)

let type_def_to_rocq (td : type_def) : string =
  match td with
  | TdEnum ed -> enum_def_to_rocq ed
  | TdRecord rd -> record_def_to_rocq rd
  | TdAbstract (t, _) -> sprintf "Parameter %s : Type." (ident_to_string t)

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
  | DeclConst (x, ty) ->
      sprintf "Parameter %s : %s." (ident_to_string x) (mtyp_to_rocq ty)
  | DeclFun (x, tparams, tret) ->
      let ty = MFun (List.map snd tparams, tret) in
      sprintf "Parameter %s : %s." (ident_to_string x) (mtyp_to_rocq ty)

let gen_record_eta_update (rd : record_def) : string =
  let rid = ident_to_string rd.rd_name in
  let fnames =
    List.map
      (fun (fname, _) ->
        sprintf "%s_%s" (String.lowercase_ascii rid) (ident_to_string fname))
      rd.rd_fields
  in
  sprintf
    "Instance eta_%s : Settable %s :=\n%ssettable! mk_%s <%s>."
    rid
    rid
    (String.make 2 ' ')
    rid
    (PrintUtils.list_to_string ~sep:"; " (fun x -> x) fnames)

let gen_enum_eq_dec (ed : enum_def) : string =
  let eid = ident_to_string ed.ed_name in
  let eq_dec =
    sprintf
      "Lemma %s_eq_dec :\n\
       %sforall (x y: %s), {x = y} + {x <> y}.\n\
       Proof.\n\
       %sdecide equality.\n\
       Defined."
      eid
      indent
      eid
      indent
  in
  let eq =
    sprintf
      "Definition %s_eq (x y: %s) : bool :=\n\
       %sif %s_eq_dec x y then true else false."
      eid
      eid
      indent
      eid
  in
  let neq =
    sprintf
      "Definition %s_neq (x y: %s) : bool :=\n\
       %sif %s_eq_dec x y then false else true."
      eid
      eid
      indent
      eid
  in
  sprintf "%s\n\n%s\n\n%s" eq_dec eq neq

let gen_enum_i32_cast (ed : enum_def) : string =
  let eid = ident_to_string ed.ed_name in
  let rec gen_elems_cast (elems : ident list) (acc : int) : string =
    match elems with
    | [] -> assert false
    | ex :: [] ->
        sprintf "%s| %s => Int.repr %d%%Z" indent (ident_to_string ex) acc
    | ex :: elems' ->
        sprintf
          "%s| %s => Int.repr %d%%Z\n%s"
          indent
          (ident_to_string ex)
          acc
          (gen_elems_cast elems' (acc + 1))
  in
  sprintf
    "Definition cast_%s_to_i32 (e: %s) : int :=\n%smatch e with\n%s\n%send."
    eid
    eid
    indent
    (gen_elems_cast ed.ed_elems 0)
    indent

let gen_i32_enum_cast (ed : enum_def) : string =
  let eid = ident_to_string ed.ed_name in
  let gen_int_cast (elems : ident list) : string =
    let rec aux (elems : ident list) (acc : int) =
      match elems with
      | [] -> sprintf "%selse fail" indent
      | ex :: elems' ->
          sprintf
            "%selse if Int.eq i (Int.repr %d%%Z) then\n%sret %s\n%s"
            indent
            acc
            (make_indent 2)
            (ident_to_string ex)
            (aux elems' acc)
    in
    match elems with
    | [] -> assert false
    | ex :: elems' ->
        sprintf
          "%sif Int.eq i (Int.repr %d%%Z) then \n%sret %s\n%s"
          indent
          0
          (make_indent 2)
          (ident_to_string ex)
          (aux elems 1)
  in

  sprintf
    "Definition cast_i32_to_%s (i: int) : res %s :=\n%s."
    eid
    eid
    (gen_int_cast ed.ed_elems)

let imports : string =
  "From Coq Require Import Bool List BinIntDef.\n\
   From compcert Require Import Integers.\n\
   From RecordUpdate Require Import RecordUpdate.\n\
   From BarocqComp Require Import Error Barray Intop.\n\
   Import BoolNotations ListNotations.\n\n\
   Open Scope error_monad_scope.\n"

let print_program (out : out_channel) (prog : program) : unit =
  let types = prog.prog_types in
  let defs = prog.prog_defs in
  fprintf out "%s" imports;
  if types <> [] then begin
    fprintf out "\n";
    fprintf out "(** * Type definitions *)\n\n";
    print_list out ~delim:("", "\n") ~sep:"\n\n" type_def_to_rocq types
  end;
  let records = get_record_defs types in
  if records <> [] then begin
    fprintf out "\n";
    fprintf out "(** * Setters for records *)\n\n";
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_record_eta_update records
  end;
  let enums = get_enum_defs types in
  if enums <> [] then begin
    fprintf out "\n";
    fprintf out "(** * Auxiliary functions *)\n\n";
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_enum_eq_dec enums;
    fprintf out "\n";
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_enum_i32_cast enums;
    fprintf out "\n";
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_i32_enum_cast enums
  end;
  fprintf out "\n";
  fprintf out "Definition neqb (b1 b2: bool) := negb (eqb b1 b2).\n";
  if defs <> [] then begin
    fprintf out "\n";
    fprintf out "(** * Program *)\n\n";
    print_list out ~delim:("", "\n") ~sep:"\n\n" globdef_to_rocq defs
  end
