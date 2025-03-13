open Printf
open Camlcoq
open Ctypesdefs

let indent : string = String.make 2 ' '

let ident_to_string (x : Syntax.ident) : string =
  camlstring_of_coqstring (string_of_ident x)

let ident_of_string (s : string) : Syntax.ident =
  ident_of_string (coqstring_of_camlstring s)

let list_to_string (b : string) (e : string) (s : string) (f : 'a -> string)
    (l : 'a list) : string =
  let rec aux (l : 'a list) =
    match l with
    | [] -> sprintf "%s" e
    | x :: [] -> sprintf "%s%s" (f x) e
    | x :: r -> sprintf "%s%s%s" (f x) s (aux r)
  in
  sprintf "%s%s" b (aux l)

let list_to_string_bracket (f : 'a -> string) (l : 'a list) : string =
  list_to_string "[" "]" "; " f l

let list_to_string_bracketbar (f : 'a -> string) (l : 'a list) : string =
  list_to_string "[|" "|]" "; " f l

let list_to_string_braces (f : 'a -> string) (args : 'a list) : string =
  list_to_string "{" "}" "; " f args

let list_to_string_paren (f : 'a -> string) (args : 'a list) : string =
  list_to_string "(" ")" ", " f args

let print_list (out : out_channel) (b : string) (e : string) (s : string)
    (f : 'a -> string) (l : 'a list) : unit =
  let rec aux (l : 'a list) =
    match l with
    | [] -> fprintf out "%s%s" b e
    | x :: [] -> fprintf out "%s%s" (f x) e
    | x :: r ->
        fprintf out "%s%s" (f x) s;
        aux r
  in
  fprintf out "%s" b;
  aux l

let opt_parens (is_simpl : 'a -> bool) (to_string : 'a -> string) (x : 'a) :
    string =
  if is_simpl x then to_string x else sprintf "(%s)" (to_string x)
