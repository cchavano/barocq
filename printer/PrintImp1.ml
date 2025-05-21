open Printf
open Imp1
open PrintCommon
open PrintSyntax

let rec statement_to_string_pref (prefix : string) (s : Imp1.statement) : string
    =
  let prefix' = prefix ^ indent in
  match s with
  | StSet (x, c) ->
      sprintf "%sset %s := %s;" prefix (ident_to_string x) (comp_to_string c)
  | StIfThenElse (a, s1, s2) ->
      sprintf
        "%sif %s then\n%s\n%selse\n%s"
        prefix
        (atom_to_string a)
        (statement_to_string_pref prefix' s1)
        prefix
        (statement_to_string_pref prefix' s2)
  | StSequence (s1, s2) ->
      sprintf
        "%s\n%s"
        (statement_to_string_pref prefix s1)
        (statement_to_string_pref prefix s2)
  | StReturn a -> sprintf "%sret %s;" prefix (atom_to_string a)

let statement_to_string (s : Imp1.statement) : string =
  statement_to_string_pref PrintCommon.indent s

let function_to_string (f : Imp1.coq_function) : string =
  PrintSyntax.function_to_string statement_to_string f

let globdef_to_string (def : Imp1.globdef) : string =
  PrintSyntax.globdef_to_string literal_to_string function_to_string ";" "" def

let print_program (out : out_channel) (prog : Imp1.program) : unit =
  PrintSyntax.print_program out ";" globdef_to_string prog

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
    | Imp1Typed.StSequence (s1, s2) ->
        StSequence (untype_statement s1, untype_statement s2)
    | Imp1Typed.StReturn a -> StReturn (untype_atom a)

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
