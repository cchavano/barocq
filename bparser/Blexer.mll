{
  open Lexing
  open Bparser

  exception Error of string
    
  let error msg = raise @@ Error msg

  let keywords = Hashtbl.create 15

  let () =
    List.iter
      (fun (s, t) -> Hashtbl.add keywords s t)
      [
        ("true", TRUE); ("false", FALSE);
        ("bool", TYP_BOOL); ("i32", TYP_INT32);
        ("i64", TYP_INT64); ("array", TYP_ARRAY);
        ("struct", STRUCT); ("def", DEF); ("let", LET); ("in", IN);
        ("if", IF); ("then", THEN); ("else", ELSE)
      ]
}

let digit = ['0'-'9']
let letter = ['a'-'z''A'-'Z']
let space = [' ''\t''\r']

let lit_int = digit+
let ident_char = (letter | digit | '_')
let ident = letter ident_char* | '_' ident_char+

rule read_token = parse
  | "\n"          { new_line lexbuf; read_token lexbuf }
  | space+        { read_token lexbuf }
  | "(*"          { read_comment lexbuf }
  | "."           { DOT }
  | ","           { COMMA }
  | ";"           { SEMICOLON }
  | ":"           { COLON }
  | "("           { LPAREN }
  | ")"           { RPAREN }
  | "[|"          { LBRACKETBAR }
  | "|]"          { RBRACKETBAR }
  | "["           { LBRACKET }
  | "]"           { RBRACKET }
  | "{"           { LBRACE }
  | "}"           { RBRACE }
  | "#"           { HASHTAG }
  | "->"          { ARROW }
  | "<-"          { ARROW_INV }
  | "=="          { OP_EQ }
  | "!="          { OP_NEQ }
  | "<="          { OP_LE }
  | ">="          { OP_GE }
  | "<<"          { OP_SHL }
  | ">>"          { OP_SHR }
  | "&&"          { OP_ANDBOOL }
  | "||"          { OP_ORBOOL }
  | "^^"          { OP_XORBOOL }            
  | "+"           { OP_PLUS }
  | "-"           { OP_MINUS }
  | "*"           { OP_MUL }
  | "/"           { OP_DIV }
  | "%"           { OP_MOD }
  | "&"           { OP_ANDINT }
  | "|"           { OP_ORINT }
  | "^"           { OP_XORINT }
  | "~"           { OP_NOTINT }
  | "<"           { OP_LT }
  | ">"           { OP_GT }
  | "!"           { OP_NOTBOOL }
  | "="           { BIND }
  | lit_int as li
    {
      try
        let i : int64 ref = ref (Int64.of_string li) in
        if (Int64.of_int32 (Int32.min_int) <= !i && !i <= Int64.of_int32 (Int32.max_int)) then
          LIT_INT32 (Int64.to_int32 !i)
        else
          LIT_INT64 !i
      with Failure _ ->
        error "64-bit integer overflow"
    }
  | ident as id 
    {
      try (Hashtbl.find keywords id) with 
      Not_found -> IDENT id
    }
  | eof           { EOF }
  | _             { error "illegal character" }

and read_comment = parse
  | "*)"  { read_token lexbuf }
  | '\n'  { new_line lexbuf; read_comment lexbuf }
  | eof   { error "unterminated comment" }
  | _     { read_comment lexbuf }