open Printf
open BarocqBNF
open PrintCommon
open PrintSyntax

let rec expr_to_string_pref (prefix : string) (e : expr) : string =
  let prefix' = prefix ^ indent in
  let str =
    match e with
    | EAtom a -> atom_to_string a
    | EArrayGet (a1, a2) ->
        sprintf "%s[%s]" (atom_to_string a1) (atom_to_string a2)
    | EArraySet (a1, a2, a3) ->
        sprintf
          "%s[%s] <- %s"
          (atom_to_string a1)
          (atom_to_string a2)
          (PrintSyntax.opt_parens a3)
    | EStructProj (a, x) ->
        sprintf "%s.%s" (atom_to_string a) (ident_to_string x)
    | EStructUpdate (a1, x, a2) ->
        sprintf
          "%s.%s <- %s"
          (atom_to_string a1)
          (ident_to_string x)
          (PrintSyntax.opt_parens a2)
    | EDeepAccess (a, acs) ->
        sprintf
          "%s%s"
          (atom_to_string a)
          (PrintSyntax.access_list_to_string acs)
    | EApp (f, args) ->
        sprintf
          "%s%s"
          (atom_to_string f)
          (list_to_string_paren atom_to_string args)
    | EIfThenElse (a, e1, e2) ->
        sprintf
          "if %s then\n%s\n%selse\n%s"
          (atom_to_string a)
          (expr_to_string_pref prefix' e1)
          prefix
          (expr_to_string_pref prefix' e2)
    | ELetIn (x, e1, e2) -> (
        match e1 with
        | ELetIn _ | EIfThenElse _ ->
            sprintf
              "let %s =\n%s\n%sin\n%s"
              (ident_to_string x)
              (expr_to_string_pref prefix' e1)
              prefix
              (expr_to_string_pref prefix e2)
        | _ ->
            sprintf
              "let %s = %s in\n%s"
              (ident_to_string x)
              (expr_to_string_pref "" e1)
              (expr_to_string_pref prefix e2))
  in
  prefix ^ str

let expr_to_string (e : expr) : string =
  expr_to_string_pref PrintCommon.indent e

let function_to_string (f : BarocqBNF.coq_function) : string =
  PrintSyntax.function_to_string expr_to_string f

let globdef_to_string (def : BarocqBNF.globdef) : string =
  PrintSyntax.globdef_to_string
    literal_to_string
    function_to_string
    ";;"
    ";;"
    def

let print_program (out : out_channel) (prog : BarocqBNF.program) : unit =
  PrintSyntax.print_program out ";;" globdef_to_string prog
