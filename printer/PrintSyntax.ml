open Printf
open Types
open PrintTypes
open PrintUtils
open Syntax

let rec literal_to_string (l : literal) : string =
  match l with
  | LTrue -> "true"
  | LFalse -> "false"
  | LInt32 (i, Signed) -> i32_to_string i
  | LInt32 (i, Unsigned) -> u32_to_string i
  | LInt64 (i, Signed) -> i64_to_string i
  | LInt64 (i, Unsigned) -> u64_to_string i
  | LArray (a, _, _) -> list_to_string_bracket ~sep:", " literal_to_string a
  | LRecord (st, _, _) ->
      list_to_string_braces
        ~sep:", "
        (fun (x, lx) ->
          sprintf "%s = %s" (ident_to_string x) (literal_to_string lx))
        st

let unary_op_to_string (op : unary_op) : string =
  match op with
  | UopNotbool -> "!"
  | UopNotint -> "~"
  | UopNeg -> "-"
  | UopPlus -> "+"

let binary_op_to_string (op : binary_op) : string =
  match op with
  | BopAndbool -> "&&"
  | BopOrbool -> "||"
  | BopXorbool -> "^^"
  | BopAdd -> "+"
  | BopSub -> "-"
  | BopMul -> "*"
  | BopDiv -> "/"
  | BopMod -> "%"
  | BopAndint -> "&"
  | BopOrint -> "|"
  | BopXorint -> "^"
  | BopShl -> "<<"
  | BopShr -> ">>"
  | BopEq -> "="
  | BopNeq -> "!="
  | BopLt -> "<"
  | BopGt -> ">"
  | BopLe -> "<="
  | BopGe -> ">="

let is_simpl_atom (a : atom) : bool =
  match a with
  | AUnaryOp _ | ABinaryOp _ -> false
  | _ -> true

let rec atom_to_string (a : atom) : string =
  match a with
  | ATrue -> "true"
  | AFalse -> "false"
  | AInt32 (i, Signed) -> i32_to_string i
  | AInt32 (i, Unsigned) -> u32_to_string i
  | AInt64 (i, Signed) -> i64_to_string i
  | AInt64 (i, Unsigned) -> u64_to_string i
  | AConstr x -> ident_to_string x
  | AVar x -> ident_to_string x
  | ACast (a1, ty) ->
      sprintf "%s as %s" (opt_parens a1) (PrintTypes.btyp_to_string ty)
  | AUnaryOp (op, a) -> sprintf "%s %s" (unary_op_to_string op) (opt_parens a)
  | ABinaryOp (op, a1, a2) ->
      sprintf
        "%s %s %s"
        (opt_parens a1)
        (binary_op_to_string op)
        (opt_parens a2)

and opt_parens (a : atom) : string =
  PrintUtils.opt_parens is_simpl_atom atom_to_string a

let access_to_string (ac : access) : string =
  match ac with
  | AcRecordField f -> sprintf ".%s" (ident_to_string f)
  | AcArrayIndex i -> sprintf "[%s]" (atom_to_string i)

let access_list_to_string (acs : access list) : string =
  list_to_string access_to_string acs

let comp_to_string (c : comp) : string =
  match c with
  | CpAtom a -> atom_to_string a
  | CpArrayGet (a1, a2) ->
      sprintf "%s[%s]" (atom_to_string a1) (atom_to_string a2)
  | CpArraySet (a1, a2, a3) ->
      sprintf
        "%s[%s] <- %s"
        (atom_to_string a1)
        (atom_to_string a2)
        (opt_parens a3)
  | CpRecordProj (a, x) ->
      sprintf "%s.%s" (atom_to_string a) (ident_to_string x)
  | CpRecordUpdate (a1, x, a2) ->
      sprintf
        "%s.%s <- %s"
        (atom_to_string a1)
        (ident_to_string x)
        (opt_parens a2)
  | CpDeepAccess (a, acs) ->
      sprintf "%s%s" (atom_to_string a) (access_list_to_string acs)
  | CpCall (f, args) ->
      sprintf
        "%s%s"
        (atom_to_string f)
        (list_to_string_paren atom_to_string args)

module Typed = struct
  let rec untype_atom (a : Syntax.Typed.atom) : atom =
    match a with
    | Syntax.Typed.ATrue _ -> ATrue
    | Syntax.Typed.AFalse _ -> AFalse
    | Syntax.Typed.AInt32 (i, ty) -> begin
        match ty with
        | BInt32 Signed -> AInt32 (i, Signed)
        | BInt32 Unsigned -> AInt32 (i, Unsigned)
        | _ -> assert false
      end
    | Syntax.Typed.AInt64 (i, ty) -> begin
        match ty with
        | BInt64 Signed -> AInt64 (i, Signed)
        | BInt64 Unsigned -> AInt64 (i, Unsigned)
        | _ -> assert false
      end
    | Syntax.Typed.AConstr (x, _) -> AConstr x
    | Syntax.Typed.AVar (x, _) -> AVar x
    | Syntax.Typed.ACast (a1, ty) -> ACast (untype_atom a1, ty)
    | Syntax.Typed.AUnaryOp (op, a', _) -> AUnaryOp (op, untype_atom a')
    | Syntax.Typed.ABinaryOp (op, a1, a2, _) ->
        ABinaryOp (op, untype_atom a1, untype_atom a2)

  let atom_to_string (a : Syntax.Typed.atom) : string =
    atom_to_string (untype_atom a)

  let untype_access (ac : Syntax.Typed.access) : Syntax.access =
    match ac with
    | Syntax.Typed.AcRecordField (f, _, _) -> AcRecordField f
    | Syntax.Typed.AcArrayIndex (a, _, _) -> AcArrayIndex (untype_atom a)

  let untype_comp (c : Syntax.Typed.comp) : comp =
    match c with
    | Syntax.Typed.CpAtom (a, _) -> CpAtom (untype_atom a)
    | Syntax.Typed.CpArrayGet (a1, a2, _, _) ->
        CpArrayGet (untype_atom a1, untype_atom a2)
    | Syntax.Typed.CpArraySet (a1, a2, a3, _) ->
        CpArraySet (untype_atom a1, untype_atom a2, untype_atom a3)
    | Syntax.Typed.CpRecordProj (a', f, _, _) -> CpRecordProj (untype_atom a', f)
    | Syntax.Typed.CpRecordUpdate (a1, f, a2, _) ->
        CpRecordUpdate (untype_atom a1, f, untype_atom a2)
    | Syntax.Typed.CpDeepAccess (a, acs, _) ->
        CpDeepAccess (untype_atom a, List.map untype_access acs)
    | Syntax.Typed.CpCall (a', args, _) ->
        CpCall (untype_atom a', List.map untype_atom args)

  let comp_to_string (c : Syntax.Typed.comp) : string =
    comp_to_string (untype_comp c)
end

let param_to_string (param : ident * btyp) : string =
  sprintf "%s : %s" (ident_to_string (fst param)) (btyp_to_string (snd param))

let param_list_to_string (params : (ident * btyp) list) : string =
  list_to_string_paren param_to_string params

let function_to_string (body_to_string : 'a -> string)
    (typ_to_string : 'b -> string) ?(fdelim : string * string = (" =", ""))
    (f : ('a, 'b) coq_function) : string =
  sprintf
    "%s : %s%s\n%s%s"
    (param_list_to_string f.fn_params)
    (typ_to_string f.fn_return)
    (fst fdelim)
    (body_to_string f.fn_body)
    (snd fdelim)

let globdef_to_string (lit_to_string : 'a -> string)
    (func_to_string : 'b -> string) (typ_to_string : 'c -> string)
    (def : ('a, 'b, 'c) globdef) : string =
  match def with
  | DefConst (x, l, ty) ->
      sprintf
        "defn %s : %s = %s"
        (ident_to_string x)
        (typ_to_string ty)
        (lit_to_string l)
  | DefFun (x, f) -> sprintf "defn %s%s" (ident_to_string x) (func_to_string f)
  | DeclConst (x, ty) ->
      sprintf "decl %s : %s" (ident_to_string x) (typ_to_string ty)
  | DeclFun (x, tparams, tret) ->
      sprintf
        "decl %s : %s"
        (ident_to_string x)
        (typ_to_string (mk_fun_btyp tparams tret))

let enum_def_to_string (ed_name : ident) (ed_elems : ident list) : string =
  sprintf
    "enum %s {\n%s\n}"
    (ident_to_string ed_name)
    (list_to_string
       ~sep:"\n"
       (fun e -> sprintf "%s%s," indent (ident_to_string e))
       ed_elems)

let record_def_to_string (typ_to_string : 'a -> string) (rd_name : ident)
    (rd_fields : 'a Maps2.smaplist) : string =
  sprintf
    "record %s %s"
    (ident_to_string rd_name)
    (recordtyp_to_string typ_to_string rd_fields)

let type_def_to_string (typ_to_string : 'a -> string)
    ((tname, td) : ident * 'a type_def) : string =
  match td with
  | TdEnum elems -> enum_def_to_string tname elems
  | TdRecord fields -> record_def_to_string typ_to_string tname fields

let print_program (out : out_channel) (def_to_string : 'a -> string)
    (typ_to_string : 'b -> string) (prog : ('a, 'b) program) : unit =
  let defs = prog.prog_defs in
  let types = prog.prog_types in
  let sep : string ref = ref "" in
  if types <> [] then begin
    print_list
      ~delim:("", "\n")
      ~sep:"\n\n"
      out
      (type_def_to_string typ_to_string)
      types;
    sep := "\n"
  end;
  if defs <> [] then begin
    fprintf out "%s" !sep;
    print_list out ~delim:("", "\n") ~sep:"\n\n" def_to_string defs
  end
