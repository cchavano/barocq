open Printf
open Imp1
open PrintCommon
open PrintSyntax

let rec statement_to_string_rec (prefix : string) (s : Imp1.statement) : string
    =
  let prefix' = prefix ^ indent in
  match s with
  | StSet (x, c) ->
      sprintf "%sset %s = %s" prefix (ident_to_string x) (comp_to_string c)
  | StIfThenElse (a, s1, s2) ->
      sprintf
        "%sif %s then\n%s\n%selse\n%s"
        prefix
        (atom_to_string a)
        (statement_to_string_rec prefix' s1)
        prefix
        (statement_to_string_rec prefix' s2)
  | StSequence (s1, s2) ->
      sprintf
        "%s\n%s"
        (statement_to_string_rec prefix s1)
        (statement_to_string_rec prefix s2)
  | StReturn a -> sprintf "%sret %s" prefix (atom_to_string a)

let statement_to_string (s : Imp1.statement) : string =
  statement_to_string_rec PrintCommon.indent s

let function_to_string (f : Imp1.coq_function) : string =
  PrintSyntax.function_to_string statement_to_string f

let globdef_to_string (def : Imp1.globdef) : string =
  PrintSyntax.globdef_to_string literal_to_string function_to_string def

let print_program (out : out_channel) (prog : Imp1.program) : unit =
  PrintSyntax.print_program out globdef_to_string prog
