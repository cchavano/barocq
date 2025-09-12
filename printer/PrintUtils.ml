open Printf
open Camlcoq

let indent_size : int = 2

let make_indent (n : int) : string = String.make (n * indent_size) ' '

let indent : string = make_indent 1

let indent2 : string = make_indent 2

let indent3 : string = make_indent 3

let indent4 : string = make_indent 4

let ident_to_string (x : Syntax.ident) : string =
  camlstring_of_coqstring (Ident.to_string x)

let ident_of_string (s : string) : Syntax.ident =
  Ident.of_string (coqstring_of_camlstring s)

let i32_to_string (i : Integers.Int.int) : string =
  sprintf "%ld" (camlint_of_coqint i)

let u32_to_string (i : Integers.Int.int) : string =
  sprintf "%lu" (camlint_of_coqint i)

let i64_to_string (i : Integers.Int64.int) : string =
  sprintf "%Ld" (camlint64_of_coqint i)

let u64_to_string (i : Integers.Int64.int) : string =
  sprintf "%Lu" (camlint64_of_coqint i)

let list_to_string ?(delim : string * string = ("", "")) ?(sep : string = "")
    (f : 'a -> string) (l : 'a list) : string =
  let rec aux (l : 'a list) =
    match l with
    | [] -> sprintf "%s" (snd delim)
    | x :: [] -> sprintf "%s%s" (f x) (snd delim)
    | x :: r -> sprintf "%s%s%s" (f x) sep (aux r)
  in
  sprintf "%s%s" (fst delim) (aux l)

let list_to_string_bracket (f : 'a -> string) (l : 'a list) : string =
  list_to_string ~delim:("[", "]") ~sep:"; " f l

let list_to_string_bracketbar (f : 'a -> string) (l : 'a list) : string =
  list_to_string ~delim:("[|", "|]") ~sep:"; " f l

let list_to_string_braces (f : 'a -> string) (args : 'a list) : string =
  list_to_string ~delim:("{", "}") ~sep:"; " f args

let list_to_string_paren (f : 'a -> string) (args : 'a list) : string =
  list_to_string ~delim:("(", ")") ~sep:", " f args

let print_list (out : out_channel) ?(delim : string * string = ("", ""))
    ?(sep : string = "") (f : 'a -> string) (l : 'a list) : unit =
  let rec aux (l : 'a list) =
    match l with
    | [] -> fprintf out "%s" (snd delim)
    | x :: [] -> fprintf out "%s%s" (f x) (snd delim)
    | x :: r ->
        fprintf out "%s%s" (f x) sep;
        aux r
  in
  fprintf out "%s" (fst delim);
  aux l

let opt_parens (is_simpl : 'a -> bool) (to_string : 'a -> string) (x : 'a) :
    string =
  if is_simpl x then to_string x else sprintf "(%s)" (to_string x)
