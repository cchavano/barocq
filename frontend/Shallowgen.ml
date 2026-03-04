open Printf
open PrintUtils
open Types
open Syntax
open BarocqShallow.Monadic

let coqlib : string ref = ref ""

let shver : BarocqShallowgen.shallow_version ref = ref BarocqShallowgen.ShallowR

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
  | MArray ta -> sprintf "list %s" (opt_parens ta)
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
  | MRes ty' -> sprintf "option %s" (opt_parens ty')

and opt_parens (ty : mtyp) : string =
  PrintUtils.opt_parens is_simpl_mtyp mtyp_to_rocq ty


let int_to_rocq (i : Integers.Int.int) (s : signedness) : string =
  let si =
    match s with
    | Signed ->
        let si = i32_to_string i in
        if Integers.Int.lt i Integers.Int.zero then sprintf "(%s)" si else si
    | Unsigned -> u32_to_string i
  in
  match s with
  | Signed -> sprintf "%s" si (* There is a Rocq coercion *)
  | Unsigned -> sprintf "%sU" si

let int64_to_rocq (i : Integers.Int64.int) (s : signedness) : string =
  let si =
    match s with
    | Signed ->
        let si = i64_to_string i in
        if Integers.Int64.lt i Integers.Int64.zero then sprintf "(%s)" si
        else si
    | Unsigned -> u64_to_string i
  in
  match s with
  | Signed -> sprintf "%sL" si
  | Unsigned -> sprintf "%sUL" si


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


let notation_of_add (ty:mtyp) = 
  match ty with
  | MInt32 _ -> "+₃₂"
  | MInt64 _ -> "+₆₄"
  |     _    -> failwith "+ is only defined for typed Int32 and Int64"

let notation_of_mul (ty:mtyp) = 
  match ty with
  | MInt32 _ -> "*₃₂"
  | MInt64 _ -> "*₆₄"
  |     _    -> failwith "* is only defined for typed Int32 and Int64"

let notation_of_mod (ty:mtyp) = 
  match ty with
  | MInt32 Unsigned -> "modu₃₂"
  | MInt32 Signed   -> "mods₃₂"
  | MInt64 Unsigned -> "modu₆₄"
  | MInt64 Signed   -> "mods₆₄"
  |     _    -> failwith "mod is only defined for typed Int32 and Int64"


let notation_of_andint (ty:mtyp) = 
  match ty with
  | MInt32 _ -> "&₃₂"
  | MInt64 _ -> "&₆₄"
  |     _    -> failwith "& is only defined for typed Int32 and Int64"

let notation_of_orint (ty:mtyp) = 
  match ty with
  | MInt32 _ -> "|₃₂"
  | MInt64 _ -> "|₆₄"
  |     _    -> failwith "| is only defined for typed Int32 and Int64"

let notation_of_xorint (ty:mtyp) = 
  match ty with
  | MInt32 _ -> "^₃₂"
  | MInt64 _ -> "^₆₄"
  |     _    -> failwith "^ is only defined for typed Int32 and Int64"

let notation_of_shl (ty:mtyp) = 
  match ty with
  | MInt32 _   -> "<<₃₂"
  | MInt64 _   -> "<<₆₄"
  |     _    -> failwith "<< is only defined for typed Int32 and Int64"

let notation_of_shr (ty:mtyp) = 
  match ty with
  | MInt32 Unsigned -> ">>u₃₂"
  | MInt32 Signed   -> ">>₃₂"
  | MInt64 Unsigned -> ">>u₆₄"
  | MInt64 Signed   -> ">>s₆₄"
  |     _    -> failwith ">> is only defined for typed Int32 and Int64"

let notation_of_sub (ty:mtyp) = 
  match ty with
  | MInt32 _ -> "-₃₂"
  | MInt64 _ -> "-₆₄"
  |     _    -> failwith "- is only defined for typed Int32 and Int64"


let is_infix (op:binary_op) =
  match op with
  | BopAdd | BopMul | BopMod -> true
  | BopAndbool | BopOrbool -> true
  | BopAndint  | BopOrint | BopXorint -> true
  | BopShr | BopShl -> true
  | BopSub -> true
  | _ -> false (* TODO: more infix operators *)

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
  | BopAdd -> notation_of_add ty
  | BopSub -> notation_of_sub ty
  | BopMul -> notation_of_mul ty
  | BopDiv -> intop "div"
  | BopMod -> notation_of_mod ty
  | BopAndint -> notation_of_andint ty
  | BopOrint -> notation_of_orint ty
  | BopXorint -> notation_of_xorint ty
  | BopShl -> notation_of_shl ty
  | BopShr -> notation_of_shr ty
  | BopEq -> begin
      match ty with
      | MBool -> "eqb"
      | MEnum t -> begin
          match !shver with
          | BarocqShallowgen.ShallowR -> sprintf "%s_eq" (ident_to_string t)
          | BarocqShallowgen.ShallowB -> "enum_eq"
        end
      | _ -> intop "eq"
    end
  | BopNeq -> begin
      match ty with
      | MBool -> "neqb"
      | MEnum t -> begin
          match !shver with
          | BarocqShallowgen.ShallowR -> sprintf "%s_neq" (ident_to_string t)
          | BarocqShallowgen.ShallowB -> "enum_neq"
        end
      | _ -> sprintf "%s %s" (intop "cmp") "Cne"
    end
  | BopLt -> intop "lt"
  | BopGt -> sprintf "%s %s" (intop "cmp") "Cgt"
  | BopLe -> sprintf "%s %s" (intop "cmp") "Cle"
  | BopGe -> sprintf "%s %s" (intop "cmp") "Cge"

let is_simpl_atom (a : atom) : bool =
  match a with
  | ATrue | AFalse | AVar _ -> true
  | _ -> false

let field_name_prefix (ty : mtyp) : string =
  match ty with
  | MRecord rid -> String.lowercase_ascii (ident_to_string rid)
  | _ -> assert false

let typof_atom (a : atom) : mtyp = BarocqShallowgen.Monadification.typof_atom a

let rec atom_to_rocq (a : atom) : string =
  match a with
  | ATrue -> "true"
  | AFalse -> "false"
  | AInt32 (i, s) -> int_to_rocq i s
  | AInt64 (i, s) -> int64_to_rocq i s
  | AConstr (x, _) ->
      let x = ident_to_string x in
      begin match !shver with
      | BarocqShallowgen.ShallowR -> x
      | BarocqShallowgen.ShallowB -> sprintf "%s_Types.%s" !coqlib x
      end
  | AVar (x, _) -> ident_to_string x
  | ACast (a1, dst_ty, _) ->
      let t1 = typof_atom a1 in
      begin match t1 with
      | MEnum tid ->
          let cast_op =
            match !shver with
            | BarocqShallowgen.ShallowR ->
                sprintf "cast_%s_to_i32" (ident_to_string tid)
            | BarocqShallowgen.ShallowB -> "Benum.to_i32"
          in
          if dst_ty = MInt32 Signed then sprintf "%s %s" cast_op (opt_parens a1)
          else
            sprintf
              "%s (%s %s)"
              (cast_to_rocq (MInt32 Signed) dst_ty)
              cast_op
              (opt_parens a1)
      | _ -> begin
          match dst_ty with
          | MEnum tid ->
              let cast_op =
                match !shver with
                | BarocqShallowgen.ShallowR ->
                    sprintf "cast_i32_to_%s" (ident_to_string tid)
                | BarocqShallowgen.ShallowB ->
                    sprintf "Benum.of_i32 elems_of_%s" (ident_to_string tid)
              in
              sprintf
                "%s (%s %s)"
                cast_op
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
        if is_infix op
        then 
          sprintf
            "%s %s %s"
            (opt_parens a1)
            (binary_op_to_rocq ty1 op)
            (opt_parens a2)
        else
          sprintf
            "%s %s %s"
            (binary_op_to_rocq ty1 op)
            (opt_parens a1)
            (opt_parens a2)
      end
  | ARecordProj (a1, x, _) -> begin
      match !shver with
      | BarocqShallowgen.ShallowR ->
          sprintf
            "%s.(%s_%s)"
            (opt_parens a1)
            (field_name_prefix (typof_atom a1))
            (ident_to_string x)
      | BarocqShallowgen.ShallowB ->
          sprintf
            "Brecord.project %s %s eq_refl"
            (opt_parens a1)
            (Deepgen.ident_to_deep x)
    end
  | ARecordUpdate (a1, x, a2, ty) -> begin
      match !shver with
      | BarocqShallowgen.ShallowR ->
          sprintf
            "%s <| %s_%s := %s |>"
            (opt_parens a1)
            (field_name_prefix ty)
            (ident_to_string x)
            (atom_to_rocq a2)
      | BarocqShallowgen.ShallowB ->
          sprintf
            "%s <- %s := %s" (* Notation is using ltac in terms *)
            (opt_parens a1)
            (Deepgen.ident_to_deep x)
            (opt_parens a2)
    end
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
    | EMatch (a1, cases, _) -> begin
        match !shver with
        | BarocqShallowgen.ShallowR ->
            sprintf
              "match %s with\n%s\n%send"
              (opt_parens a1)
              (list_to_string ~sep:"\n" (match_case_to_string prefix) cases)
              prefix
        | BarocqShallowgen.ShallowB -> begin
            sprintf
              "match_with_err %s [\n%s\n%s]"
              (opt_parens a1)
              (list_to_string
                 ~sep:";\n"
                 (match_case_to_string (prefix ^ indent))
                 cases)
              prefix
          end
      end
    | ELetIn (x, e1, e2, _) -> begin
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
              (expr_to_rocq_rec prefix e2)
      end
    | ELetMon (x, e1, e2, _) -> begin
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
              (expr_to_rocq_rec prefix e2)
      end
    | ERet (e1, _) -> begin
        match e1 with
        | EAtom (a1, _) -> sprintf "ret %s" (opt_parens a1)
        | EApp _ -> sprintf "ret (%s)" (expr_to_rocq_rec "" e1)
        | _ -> assert false
      end
    | EAttr (_, s, _) -> expr_to_rocq_rec prefix s
  in
  prefix ^ str

and match_case_to_string (prefix : string) ((p, ep) : Benum.pattern * expr) :
    string =
  match !shver with
  | BarocqShallowgen.ShallowR ->
      let case =
        match p with
        | Benum.PIdent (i, _) -> ident_to_string i
        | Benum.PWildcard -> "_"
      in
      sprintf
        "%s| %s =>\n%s"
        prefix
        case
        (expr_to_rocq_rec (prefix ^ make_indent 2) ep)
  | BarocqShallowgen.ShallowB ->
      let case =
        match p with
        | Benum.PIdent (i, z) ->
            sprintf
              "PIdent %s %i"
              (Deepgen.ident_to_deep i)
              (Camlcoq.Z.to_int z)
        | Benum.PWildcard -> "PWildcard"
      in
      sprintf "%s(%s,\n%s)" prefix case (expr_to_rocq_rec (prefix ^ indent) ep)

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

module SR = struct
  let is_simpl_lit (l : literal) : bool =
    match l with
    | LTrue | LFalse -> true
    | _ -> false

  let rec literal_to_rocq (l : literal) : string =
    match l with
    | LTrue -> "true"
    | LFalse -> "false"
    | LInt32 (i, s) -> int_to_rocq i s
    | LInt64 (i, s) -> int64_to_rocq i s
    | LArray (la, _) -> list_to_string_bracket literal_to_rocq la
    | LRecord (rc, rid) -> record_lit_to_rocq (ident_to_string rid) rc

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

  let enum_def_to_rocq (ed_name : ident) (ed_elems : ident list) : string =
    let eid = ident_to_string ed_name in
    sprintf
      "Inductive %s :=\n%s."
      eid
      (list_to_string
         ~sep:"\n"
         (fun e -> sprintf "%s| %s" indent (ident_to_string e))
         ed_elems)

  let field_typ_to_rocq (rid : string)
      ((fname, (fty, _)) : ident * (mtyp * layout)) : string =
    sprintf
      "%s%s_%s: %s"
      indent
      (String.lowercase_ascii rid)
      (ident_to_string fname)
      (mtyp_to_rocq fty)

  let record_def_to_rocq (rd_name : ident)
      (rd_fields : (mtyp * layout) Maps2.smaplist) : string =
    let rid = ident_to_string rd_name in
    sprintf
      "Record %s := mk_%s {\n%s\n}."
      rid
      rid
      (list_to_string ~sep:";\n" (field_typ_to_rocq rid) rd_fields)

  let type_def_to_rocq ((tname, td) : ident * (mtyp * layout) type_def) : string
      =
    match td with
    | TdEnum elems -> enum_def_to_rocq tname elems
    | TdRecord fields -> record_def_to_rocq tname fields

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

  let gen_record_eta_update
      ((rd_name, rd_fields) : ident * (mtyp * layout) Maps2.smaplist) : string =
    let rid = ident_to_string rd_name in
    let fnames =
      List.map
        (fun (fname, _) ->
          sprintf "%s_%s" (String.lowercase_ascii rid) (ident_to_string fname))
        rd_fields
    in
    sprintf
      "Instance eta_%s : Settable %s :=\n%ssettable! mk_%s <%s>."
      rid
      rid
      (String.make 2 ' ')
      rid
      (PrintUtils.list_to_string ~sep:"; " (fun x -> x) fnames)

  let gen_enum_eq_dec ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
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
        "Definition %s_neq (x y: %s) : bool :=\n%snegb (%s_eq x y)."
        eid
        eid
        indent
        eid
    in
    sprintf "%s\n\n%s\n\n%s" eq_dec eq neq

  let gen_enum_i32_cast ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
    let rec gen_elems_cast (elems : ident list) (acc : int) : string =
      match elems with
      | [] -> assert false
      | ex :: [] ->
          sprintf "%s| %s => Int.repr %d" indent (ident_to_string ex) acc
      | ex :: elems' ->
          sprintf
            "%s| %s => Int.repr %d\n%s"
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
      (gen_elems_cast ed_elems 0)
      indent

  let gen_i32_enum_cast ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
    let cast_body =
      sprintf
        "%scast_enum%s[\n%s\n%s]\n%si"
        indent
        indent
        (list_to_string
           ~sep:";\n"
           (fun constr -> sprintf "%s%s" indent2 (ident_to_string constr))
           ed_elems)
        indent
        indent
    in
    sprintf
      "Definition cast_i32_to_%s (i: int) : option %s :=\n%s."
      eid
      eid
      cast_body

  let imports : string =
    "From Coq Require Import Bool List BinIntDef.\n\
     From compcert Require Import Integers.\n\
     From RecordUpdate Require Import RecordUpdate.\n\
     From BarocqComp Require Import OptionMonad Barray Intop Utils.\n\
     Import BoolNotations ListNotations BarocqNotations.\n\n\
     Open Scope Z_scope.\n\
     Open Scope option_monad_scope.\n"

  let print_program (out : out_channel) (prog : program) : unit =
    shver := BarocqShallowgen.ShallowR;
    let types = prog.prog_types in
    let tabs = prog.prog_tabs in
    let defs = prog.prog_defs in
    fprintf out "%s" imports;
    if tabs <> [] then begin
      fprintf out "\n";
      fprintf out "(** * Abstract types *)\n\n";
      print_list
        out
        ~delim:("", "\n")
        ~sep:"\n\n"
        (fun (tid, _) -> sprintf "Parameter %s : Type." (ident_to_string tid))
        tabs
    end;
    if types <> [] then begin
      fprintf out "\n";
      fprintf out "(** * Type definitions *)\n\n";
      print_list out ~delim:("", "\n") ~sep:"\n\n" type_def_to_rocq types
    end;
    let records = Syntax.get_record_typedefs types in
    if records <> [] then begin
      fprintf out "\n";
      fprintf out "(** * Setters for records *)\n\n";
      print_list out ~delim:("", "\n") ~sep:"\n\n" gen_record_eta_update records
    end;
    fprintf out "\n";
    fprintf out "(** * Auxiliary functions *)\n";
    let enums = Syntax.get_enum_typedefs types in
    if enums <> [] then begin
      fprintf out "\n";
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
end

module SB = struct
  let is_simpl_lit (l : literal) : bool =
    match l with
    | LTrue | LFalse -> true
    | _ -> false

  let rec literal_to_rocq (l : literal) : string =
    match l with
    | LTrue -> "true"
    | LFalse -> "false"
    | LInt32 (i, s) -> int_to_rocq i s
    | LInt64 (i, s) -> int64_to_rocq i s
    | LArray (la, _) -> list_to_string_bracket literal_to_rocq la
    | LRecord (rc, rid) -> record_lit_to_rocq rc

  and record_lit_to_rocq (rc : (ident * literal) list) : string =
    List.fold_right
      (fun (fname, lit) acc ->
        sprintf
          "(Field %s %s, %s)"
          (Deepgen.ident_to_deep fname)
          (opt_parens lit)
          acc)
      rc
      "tt"

  and opt_parens (l : literal) : string =
    PrintUtils.opt_parens is_simpl_lit literal_to_rocq l

  let enum_def_to_rocq (ed_name : ident) (ed_elems : ident list) : string =
    let eid = ident_to_string ed_name in
    sprintf
      "Definition elems_of_%s : list ident := [\n\
       %s\n\
       ].\n\n\
       Definition %s : Type := enum elems_of_%s."
      eid
      (list_to_string
         ~sep:";\n"
         (fun cid -> sprintf "%s%s" indent (Deepgen.ident_to_deep cid))
         ed_elems)
      eid
      eid

  let field_typ_to_rocq ((fname, fty) : ident * mtyp) : string =
    sprintf
      "%s(%s, %s : Type)"
      indent2
      (Deepgen.ident_to_deep fname)
      (mtyp_to_rocq fty)

  let record_def_to_rocq (rd_name : ident) (rd_fields : mtyp Maps2.smaplist) :
      string =
    let rid = ident_to_string rd_name in
    sprintf
      "Definition %s : Type :=\n%srecord [\n%s\n%s]."
      rid
      indent
      (list_to_string ~sep:";\n" field_typ_to_rocq rd_fields)
      indent

  let gen_ffi_fun_body (fid : ident) (tparams : mtyp list) (tret : mtyp) :
      string =
    let rec gen_args (n : int) : string =
      if n >= List.length tparams then ""
      else sprintf "a%d %s" n (gen_args (n + 1))
    in
    let conv_args : string =
      snd
        (List.fold_left
           (fun (ctr, str) ty ->
             let arg = sprintf "a%d" ctr in
             let conv_arg = Btypesgen.conv_value Btypesgen.BtoR ty arg in
             if conv_arg = arg then (ctr + 1, str)
             else
               let str' =
                 sprintf
                   "%s%slet %s := %s in\n"
                   str
                   indent2
                   arg
                   (Btypesgen.conv_value Btypesgen.BtoR ty arg)
               in
               (ctr + 1, str'))
           (0, "")
           tparams)
    in
    let gen_call () : string =
      sprintf
        "%slet* r := %s_ShallowR.%s %sin\n"
        indent2
        !coqlib
        (ident_to_string fid)
        (gen_args 0)
    in
    let gen_return () : string =
      let tret = BarocqShallowgen.Monadification.unwrap_mtyp tret in
      sprintf
        "%sret %s."
        indent2
        (Btypesgen.conv_value_opt_parens Btypesgen.RtoB tret "r")
    in
    sprintf
      "%sfun %s=>\n%s%s%s"
      indent
      (gen_args 0)
      conv_args
      (gen_call ())
      (gen_return ())

  let gen_ffi_fun (fid : ident) (tparams : (param_attr * mtyp) list)
      (tret : mtyp) : string =
    let tparams = List.map snd tparams in
    sprintf
      "Definition %s : %s :=\n%s"
      (ident_to_string fid)
      (mtyp_to_rocq (MFun (tparams, tret)))
      (gen_ffi_fun_body fid tparams tret)

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
        let x' = ident_to_string x in
        sprintf
          "Definition %s : %s := %s."
          x'
          (mtyp_to_rocq ty)
          ((Btypesgen.conv_value Btypesgen.RtoB)
             ty
             (sprintf "%s_ShallowR.%s" !coqlib x'))
    | DeclFun (x, tparams, tret) -> gen_ffi_fun x tparams tret

  let imports () : string =
    sprintf
      "From Coq Require Import Bool List BinIntDef String.\n\
       From compcert Require Import Integers.\n\
       From RecordUpdate Require Import RecordUpdate.\n\
       From BarocqComp Require Import Ident OptionMonad Barray Benum Brecord \
       Intop.\n\
       From %s Require Import %s_Types.\n\
       Import BoolNotations ListNotations BarocqNotations.\n\n\
       Open Scope Z_scope.\n\
       Open Scope string_scope.\n\
       Open Scope option_monad_scope.\n"
      !coqlib
      !coqlib

  let print_program (out : out_channel) (prog : program) : unit =
    shver := BarocqShallowgen.ShallowB;
    let defs = prog.prog_defs in
    fprintf out "%s" (imports ());
    fprintf out "\n";
    fprintf out "(** * Auxiliary functions *)\n\n";
    fprintf out "Definition neqb (b1 b2: bool) := negb (Bool.eqb b1 b2).\n";
    if defs <> [] then begin
      fprintf out "\n";
      fprintf out "(** * Program *)\n\n";
      print_list out ~delim:("", "\n") ~sep:"\n\n" globdef_to_rocq defs
    end
end
