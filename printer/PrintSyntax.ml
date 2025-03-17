open Printf
open Camlcoq
open Types
open PrintTypes
open PrintCommon
open Syntax

let rec literal_to_string (l : literal) : string =
  match l with
  | LTrue -> "true"
  | LFalse -> "false"
  | LInt32 i -> sprintf "%ld" (camlint_of_coqint i)
  | LInt64 i -> sprintf "%Ld" (camlint64_of_coqint i)
  | LArray a -> list_to_string_bracketbar literal_to_string a
  | LStruct (st, t) ->
      let sts =
        list_to_string_braces
          (fun (x, lx) ->
            sprintf "%s = %s" (ident_to_string x) (literal_to_string lx))
          st
      in
      sprintf "%s#%s" sts (ident_to_string t)

let unary_op_to_string (op : unary_op) : string =
  match op with
  | UopNotbool -> "!"
  | UopNotint -> "~"
  | UopNeg -> "-"

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
  | AInt32 i -> sprintf "%ld" (camlint_of_coqint i)
  | AInt64 i -> sprintf "%Ld" (camlint64_of_coqint i)
  | AVar x -> ident_to_string x
  | AUnaryOp (op, a) -> sprintf "%s %s" (unary_op_to_string op) (opt_parens a)
  | ABinaryOp (op, a1, a2) ->
      sprintf
        "%s %s %s"
        (opt_parens a1)
        (binary_op_to_string op)
        (opt_parens a2)

and opt_parens (a : atom) : string =
  PrintCommon.opt_parens is_simpl_atom atom_to_string a

let typed_atom_to_string (a : Typed.atom) : string =
  let rec untype_atom (a : Typed.atom) : atom =
    match a with
    | Typed.ATrue _ -> ATrue
    | Typed.AFalse _ -> AFalse
    | Typed.AInt32 (i, _) -> AInt32 i
    | Typed.AInt64 (i, _) -> AInt64 i
    | Typed.AVar (x, _) -> AVar x
    | Typed.AUnaryOp (op, a', _) -> AUnaryOp (op, untype_atom a')
    | Typed.ABinaryOp (op, a1, a2, _) ->
        ABinaryOp (op, untype_atom a1, untype_atom a2)
  in
  atom_to_string (untype_atom a)

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
  | CpStructProj (a, x) ->
      sprintf "%s.%s" (atom_to_string a) (ident_to_string x)
  | CpStructUpdate (a1, x, a2) ->
      sprintf
        "%s.%s <- %s"
        (atom_to_string a1)
        (ident_to_string x)
        (opt_parens a2)
  | CpCall (f, args) ->
      sprintf
        "%s %s"
        (atom_to_string f)
        (list_to_string_paren atom_to_string args)

module PrintTyped = struct
  let rec untype_atom (a : Syntax.Typed.atom) : atom =
    match a with
    | Typed.ATrue _ -> ATrue
    | Typed.AFalse _ -> AFalse
    | Typed.AInt32 (i, _) -> AInt32 i
    | Typed.AInt64 (i, _) -> AInt64 i
    | Typed.AVar (x, _) -> AVar x
    | Typed.AUnaryOp (op, a', _) -> AUnaryOp (op, untype_atom a')
    | Typed.ABinaryOp (op, a1, a2, _) ->
        ABinaryOp (op, untype_atom a1, untype_atom a2)

  let atom_to_string (a : Syntax.Typed.atom) : string =
    atom_to_string (untype_atom a)

  let untype_comp (c : Typed.comp) : comp =
    match c with
    | Typed.CpAtom (a, _) -> CpAtom (untype_atom a)
    | Typed.CpArrayGet (a1, a2, _) -> CpArrayGet (untype_atom a1, untype_atom a2)
    | Typed.CpArraySet (a1, a2, a3, _) ->
        CpArraySet (untype_atom a1, untype_atom a2, untype_atom a3)
    | Typed.CpStructProj (a', f, _) -> CpStructProj (untype_atom a', f)
    | Typed.CpStructUpdate (a1, f, a2, _) ->
        CpStructUpdate (untype_atom a1, f, untype_atom a2)
    | Typed.CpCall (a', args, _) ->
        CpCall (untype_atom a', List.map untype_atom args)

  let comp_to_string (c : Syntax.Typed.comp) : string =
    comp_to_string (untype_comp c)
end

let param_to_string (param : ident * ctyp) : string =
  sprintf "%s : %s" (ident_to_string (fst param)) (ctyp_to_string (snd param))

let param_list_to_string (params : (ident * ctyp) list) : string =
  list_to_string_paren param_to_string params

let function_to_string (body_to_string : 'a -> string) (f : 'a coq_function) :
    string =
  sprintf
    "%s : %s =\n%s"
    (param_list_to_string f.fn_params)
    (ctyp_to_string f.fn_return)
    (body_to_string f.fn_body)

let globdef_to_string (lit_to_string : 'a -> string)
    (func_to_string : 'b -> string) (csep : string) (fsep : string)
    (def : ('a, 'b) globdef) : string =
  match def with
  | DefConst (x, l, ty) ->
      sprintf
        "def %s : %s = %s%s"
        (ident_to_string x)
        (ctyp_to_string ty)
        (lit_to_string l)
        csep
  | DefFun (x, f) ->
      sprintf "def %s %s%s" (ident_to_string x) (func_to_string f) fsep

let struct_def_to_tring (sep : string) (sid : ident)
    (fields : (ident * ctyp) list) : string =
  sprintf
    "struct %s = %s%s"
    (ident_to_string sid)
    (structtyp_to_string ctyp_to_string fields)
    sep

let print_program (out : out_channel) (ssep : string)
    (def_to_string : 'a -> string) (prog : 'a program) : unit =
  let types = Maps.PTree.elements prog.prog_types in
  let defs = prog.prog_defs in
  let s, e =
    match (types, defs) with
    | [], [] -> ("", "")
    | _ :: _, [] -> ("\n", "")
    | _ :: _, _ :: _ -> ("\n\n", "\n")
    | [], _ :: _ -> ("", "\n")
  in
  print_list
    out
    ""
    s
    "\n\n"
    (fun (x, tx) -> struct_def_to_tring ssep x tx)
    types;
  print_list out "" e "\n\n" def_to_string defs
