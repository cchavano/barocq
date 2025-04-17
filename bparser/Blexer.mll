{
  open Lexing
  open Bparser

  exception Error of string
    
  let error msg = raise @@ Error msg

  let keywords = Hashtbl.create 15

  let comment_lvl = ref (-1)

  let parse_int_lit (il: string) : token =
      let n = String.length il in
      (* ===== u64 ===== *)
      if String.ends_with ~suffix:"UL" il then
        let il = "0u" ^ String.sub il 0 (n - 2) in
        try
          LIT_INT64 (Int64.of_string il, Types.Unsigned)
        with Failure _ ->
          error "unsigned 64-bit integer overflow."
      (* ===== i64 ===== *)
      else if String.ends_with ~suffix:"L" il then
        let il = String.sub il 0 (n - 1) in
        try
          LIT_INT64 ((Int64.of_string il), Types.Signed)
        with Failure _ ->
          error "64-bit integer overflow."
      (* ===== u32 ===== *)
      else if String.ends_with ~suffix:"U" il then
        let il = "0u" ^ String.sub il 0 (n - 1) in
        try
          LIT_INT32 ((Int32.of_string il), Types.Unsigned)
        with Failure _ ->
          error "unsigned 32-bit integer overflow"
      (* ===== i32 ===== *)
      else
        try
          LIT_INT32 ((Int32.of_string il), Types.Signed)
        with Failure _ ->
          error "32-bit integer overflow"

  let () =
    List.iter
      (fun (s, t) -> Hashtbl.add keywords s t)
      [
        ("true", TRUE); ("false", FALSE);
        ("bool", TYP_BOOL); ("i32", TYP_INT32); ("u32", TYP_UINT32);
        ("i64", TYP_INT64); ("u64", TYP_UINT64); ("array", TYP_ARRAY);
        ("struct", STRUCT); ("def", DEF); ("let", LET); ("in", IN);
        ("if", IF); ("then", THEN); ("else", ELSE)
      ]
}

let digit = ['0'-'9']
let letter = ['a'-'z''A'-'Z']
let space = [' ''\t''\r']

let int_lit = digit+ ['U']? ['L']?
let ident_char = (letter | digit | '_' | '\'')
let ident = letter ident_char* | '_' ident_char+

rule read_token = parse
  | "\n"          { new_line lexbuf; read_token lexbuf }
  | space+        { read_token lexbuf }
  | "(*"          { incr comment_lvl; read_comment lexbuf }
  | "*)"          { error "comment end before comment begin" }
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
  | int_lit as il { parse_int_lit il }
  | ident as id
    {
      try (Hashtbl.find keywords id) with 
      Not_found -> IDENT id
    }
  | eof           { EOF }
  | _             { error "illegal character" }

and read_comment = parse
  | "(*"  { incr comment_lvl; read_comment lexbuf }
  | "*)"
    {
      decr comment_lvl;
      if !comment_lvl >= 0 then
        read_comment lexbuf
      else
        read_token lexbuf
    }
  | '\n'  { new_line lexbuf; read_comment lexbuf }
  | eof   { error "unterminated comment" }
  | _     { read_comment lexbuf }