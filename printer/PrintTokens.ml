open Printf
open Bparser

let token_to_string (tok : Bparser.token) : string =
  match tok with
  | DOT -> "DOT"
  | COMMA -> "COMMA"
  | SEMICOLON -> "SEMICOLON"
  | COLON -> "COLON"
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | LBRACE -> "LBRACE"
  | RBRACE -> "RBRACE"
  | LBRACKET -> "LBRACKET"
  | RBRACKET -> "RBRACKET"
  | LBRACKETBAR -> "LBRACKETBAR"
  | RBRACKETBAR -> "RBRACKETBAR"
  | HASHTAG -> "HASHTAG"
  | ARROW -> "ARROW"
  | ARROW_INV -> "ARROW_INV"
  | BIND -> "BIND"
  | OP_PLUS -> "OP_PLUS"
  | OP_MINUS -> "OP_MINUS"
  | OP_MUL -> "OP_MUL"
  | OP_DIV -> "OP_DIV"
  | OP_MOD -> "OP_MOD"
  | OP_ANDINT -> "OP_ANDINT"
  | OP_ORINT -> "OP_ORINT"
  | OP_XORINT -> "OP_XORINT"
  | OP_SHL -> "OP_SHL"
  | OP_SHR -> "OP_SHR"
  | OP_NOTINT -> "OP_NOTINT"
  | OP_ANDBOOL -> "OP_ANDBOOL"
  | OP_ORBOOL -> "OP_ORBOOL"
  | OP_XORBOOL -> "OP_XORBOOL"
  | OP_NOTBOOL -> "OP_NOTBOOL"
  | OP_EQ -> "OP_EQ"
  | OP_NEQ -> "OP_NEQ"
  | OP_GE -> "OP_GE"
  | OP_LE -> "OP_LE"
  | OP_GT -> "OP_GT"
  | OP_LT -> "OP_LT"
  | TRUE -> "TRUE"
  | FALSE -> "FALSE"
  | TYP_BOOL -> "TYP_BOOL"
  | TYP_INT32 -> "TYP_INT32"
  | TYP_UINT32 -> "TYP_UINT32"
  | TYP_INT64 -> "TYP_INT64"
  | TYP_UINT64 -> "TYP_UINT64"
  | TYP_ARRAY -> "TYP_ARRAY"
  | STRUCT -> "STRUCT"
  | DEF -> "DEF"
  | LET -> "LET"
  | IN -> "IN"
  | IF -> "IF"
  | THEN -> "THEN"
  | ELSE -> "ELSE"
  | LIT_INT32 i -> sprintf "LIT_INT32 %ld" i
  | LIT_UINT32 i -> sprintf "LIT_UINT32 %lu" i
  | LIT_INT64 i -> sprintf "LIT_INT64 %Ld" i
  | LIT_UINT64 i -> sprintf "LIT_UINT64 %Lu" i
  | IDENT id -> sprintf "IDENT %s" id
  | EOF -> "EOF"

let rec print (lexbuf : Lexing.lexbuf) : unit =
  let token = Blexer.read_token lexbuf in
  match token with
  | EOF -> fprintf stdout "EOF\n"
  | _ ->
      fprintf stdout "%s\n" (token_to_string token);
      print lexbuf
