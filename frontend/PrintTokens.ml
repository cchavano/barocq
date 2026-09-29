open Printf
open Lexing
open Bparser

let token_to_string (tok : Bparser.token) : string =
  match tok with
  | WHILE -> "WHILE"
  | DONE   -> "DONE"
  | DO     -> "DO"
  | DECR   -> "DECR"
  | MODULE -> "MODULE"
  | IMPORT -> "IMPORT"
  | COMPUTE -> "COMPUTE"
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
  | RDARROW -> "RDARROW"
  | RARROW -> "RARROW"
  | LARROW -> "LARROW"
  | BIND -> "BIND"
  | UNDERSCORE -> "UNDERSCORE"
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
  | SHARP -> "SHARP"
  | ENUM -> "ENUM"
  | RECORD -> "RECORD"
  | TYPE -> "TYPE"
  | OF -> "OF"
  | TYP_BOOL -> "TYP_BOOL"
  | TYP_I32 -> "TYP_I32"
  | TYP_U32 -> "TYP_U32"
  | TYP_I64 -> "TYP_I64"
  | TYP_U64 -> "TYP_U64"
  | DEFN -> "DEFN"
  | DECL -> "DECL"
  | LET -> "LET"
  | MATCH -> "MATCH"
  | END -> "END"
  | WITH -> "WITH"
  | IN -> "IN"
  | IF -> "IF"
  | THEN -> "THEN"
  | ELSE -> "ELSE"
  | READ -> "READ"
  | WRITE -> "WRITE"
  | INLINE -> "INLINE"
  | ALWAYS_INLINE -> "ALWAYS_INLINE"
  | STATIC -> "STATIC"
  | ALL_STATIC -> "ALL_STATIC"
  | EXPORT -> "EXPORT"
  | UNIQUE -> "UNIQUE"
  | AS -> "AS"
  | LIT_INT32 (i, Types.Signed) -> sprintf "LIT_INT32 %ld Signed" i
  | LIT_INT32 (i, Types.Unsigned) -> sprintf "LIT_INT32 %lu Unsigned" i
  | LIT_INT64 (i, Types.Signed) -> sprintf "LIT_INT64 %Ld Signed" i
  | LIT_INT64 (i, Types.Unsigned) -> sprintf "LIT_INT64 %Lu Unsigned" i
  | LIT_STRING s -> s
  | IDENT id -> sprintf "IDENT %s" id
  | EOF -> "EOF"

let print (lexbuf : Lexing.lexbuf) : unit =
  let rec collect lexbuf =
    match Blexer.read_token lexbuf with
    | EOF -> [EOF]
    | _ as tok -> tok :: collect lexbuf
  in
  let token_list = collect lexbuf in
  let file = lexbuf.lex_curr_p.pos_fname in
  printf "Start of file \"%s\" ========\n" file;
  PrintUtils.print_list stdout ~sep:"\n" token_to_string token_list;
  printf "\n";
  printf "End of file \"%s\" ========\n" file
