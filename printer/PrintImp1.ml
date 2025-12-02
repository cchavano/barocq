open Printf
open Imp1
open PrintUtils
open PrintSyntax

let rec statement_to_string_pref (prefix : string) (s : Imp1.statement) : string
    =
  let prefix' = prefix ^ indent in
  match s with
  | StSet (x, c) ->
      sprintf "%s%s := %s;" prefix (ident_to_string x) (comp_to_string c)
  | StIfThenElse (a, s1, s2) ->
      sprintf
        "%sif %s {\n%s\n%s} else {\n%s\n%s}"
        prefix
        (atom_to_string a)
        (statement_to_string_pref prefix' s1)
        prefix
        (statement_to_string_pref prefix' s2)
        prefix
  | StSwitch (a, cases) ->
      sprintf
        "%smatch %s {\n%s\n%s}"
        prefix
        (atom_to_string a)
        (list_to_string ~sep:"\n" (switch_case_to_string prefix') cases)
        prefix
  | StSequence (s1, s2) ->
      sprintf
        "%s\n%s"
        (statement_to_string_pref prefix s1)
        (statement_to_string_pref prefix s2)
  | StReturn a -> sprintf "%sreturn %s;" prefix (atom_to_string a)
  | StAttr (a, s) ->
      sprintf
        "%s[#%s]%s"
        prefix
        (ident_to_string a)
        (statement_to_string_pref prefix s)

and switch_case_to_string (prefix : string)
    ((p, sp) : Benum.pattern * Imp1.statement) : string =
  let case =
    match p with
    | Benum.PIdent (i, _) -> sprintf "%s =>" (ident_to_string i)
    | Benum.PWildcard -> "_ =>"
  in
  sprintf "%s%s\n%s" prefix case (statement_to_string_pref (prefix ^ indent) sp)

let statement_to_string (s : Imp1.statement) : string =
  statement_to_string_pref PrintUtils.indent s

let function_to_string (f : Imp1.coq_function) : string =
  PrintSyntax.function_to_string
    ~fdelim:(" {", "\n}")
    statement_to_string
    PrintTypes.btyp_to_string
    f

let globdef_to_string (def : Imp1.globdef) : string =
  PrintSyntax.globdef_to_string
    literal_to_string
    function_to_string
    PrintTypes.btyp_to_string
    def

let print_program (out : out_channel) (prog : Imp1.program) : unit =
  PrintSyntax.print_program
    out
    globdef_to_string
    (fun (ty, ly) -> PrintTypes.btyp_to_string_rec ly ty)
    prog

module Typed : sig
  val statement_to_string_pref : string -> Imp1Typed.statement -> string

  val statement_to_string : Imp1Typed.statement -> string
end = struct
  open PrintSyntax.Typed

  let rec untype_statement (s : Imp1Typed.statement) : Imp1.statement =
    match s with
    | Imp1Typed.StSet (x, c) -> StSet (x, untype_comp c)
    | Imp1Typed.StIfThenElse (a, s1, s2) ->
        StIfThenElse (untype_atom a, untype_statement s1, untype_statement s2)
    | Imp1Typed.StSwitch (a, cases) ->
        StSwitch (untype_atom a, Maps2.MapList.map untype_statement cases)
    | Imp1Typed.StSequence (s1, s2) ->
        StSequence (untype_statement s1, untype_statement s2)
    | Imp1Typed.StReturn a -> StReturn (untype_atom a)
    | Imp1Typed.StAttr (a, s) -> StAttr (a, untype_statement s)

  let statement_to_string_pref (prefix : string) (s : Imp1Typed.statement) :
      string =
    statement_to_string_pref prefix (untype_statement s)

  let statement_to_string (s : Imp1Typed.statement) : string =
    statement_to_string (untype_statement s)
end

module PrintAliasing = struct
  open PrintSyntax.Typed

  let rec remove_alias_info (s : Imp1.Aliasing_AST.statement) : Imp1.statement =
    match s with
    | Aliasing_AST.StSet (x, c, _, _) -> StSet (x, untype_comp c)
    | Aliasing_AST.StIfThenElse (a, s1, s2, _, _) ->
        let s1' = remove_alias_info s1 in
        let s2' = remove_alias_info s2 in
        StIfThenElse (untype_atom a, s1', s2')
    | Aliasing_AST.StSwitch (a, cases, _, _) ->
        let cases' = Maps2.MapList.map remove_alias_info cases in
        StSwitch (untype_atom a, cases')
    | Aliasing_AST.StSequence (s1, s2) ->
        let s1' = remove_alias_info s1 in
        let s2' = remove_alias_info s2 in
        StSequence (s1', s2')
    | Aliasing_AST.StReturn (a, _, _) -> StReturn (untype_atom a)

  let statement_to_string_pref (prefix : string)
      (s : Imp1.Aliasing_AST.statement) : string =
    statement_to_string_pref prefix (remove_alias_info s)

  let statement_to_string (s : Imp1.Aliasing_AST.statement) : string =
    statement_to_string (remove_alias_info s)
end
