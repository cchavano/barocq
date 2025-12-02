{
  open Lexing
  open Bparser

  exception Error of string
    
  let error msg = raise @@ Error msg

  let keywords = Hashtbl.create 26

  let comment_lvl = ref (-1)

  let string_buf = Buffer.create 10

  let parse_int_lit (il: string) : token =
      let il = String.lowercase_ascii il in
      let n = String.length il in
      (* ===== u64 ===== *)
      if String.ends_with ~suffix:"ul" il then
        let il =
          let n = String.sub il 0 (n - 2) in
          if String.starts_with ~prefix:"0x" il then n
          else "0u" ^ n
        in
        try
          LIT_INT64 (Int64.of_string il, Types.Unsigned)
        with Failure _ ->
          error "unsigned 64-bit integer overflow."
      (* ===== i64 ===== *)
      else if String.ends_with ~suffix:"l" il then
        let il = String.sub il 0 (n - 1) in
        try
          LIT_INT64 ((Int64.of_string il), Types.Signed)
        with Failure _ ->
          error "64-bit integer overflow."
      (* ===== u32 ===== *)
      else if String.ends_with ~suffix:"u" il then
        let il =
          let n = String.sub il 0 (n - 1) in
          if String.starts_with ~prefix:"0x" il then n
          else "0u" ^ n
        in
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

  let parse_annotation = function
    | "inline" -> INLINE
    | "always_inline" -> ALWAYS_INLINE
    | "static" -> STATIC
    | "all_static" -> ALL_STATIC
    | "export" -> EXPORT
    | "unique" -> UNIQUE
    | "read" -> READ
    | "write" -> WRITE
    | _ as s -> error (Printf.sprintf "unknown annotation '%s'" s)

  let () =
    List.iter
      (fun (s, t) -> Hashtbl.add keywords s t)
      [
        ("module", MODULE); ("import", IMPORT); ("compute", COMPUTE);
        ("true", TRUE); ("false", FALSE);
        ("bool", TYP_BOOL); ("i32", TYP_I32); ("u32", TYP_U32);
        ("i64", TYP_I64); ("u64", TYP_U64);
        ("enum", ENUM); ("record", RECORD); ("type", TYPE); ("of", OF);
        ("defn", DEFN); ("decl", DECL);
        ("let", LET); ("in", IN);
        ("match", MATCH); ("with", WITH); ("end", END);
        ("as", AS); ("if", IF); ("then", THEN); ("else", ELSE)
      ]
}

let digit = ['0'-'9']
let xdigit = digit | ['a'-'f''A'-'F']
let letter = ['a'-'z''A'-'Z']
let space = [' ''\t''\r']

let int_suffix = ('u'? 'l'?) | ('U'? 'L'?)
let dec_int_lit = digit (digit | '_')* int_suffix
let hex_int_lit = ("0x" | "0X") xdigit (xdigit | '_')* int_suffix?
let ident_char = (letter | digit | '_'|"'")
let ident = letter ident_char* | '_' ident_char+

rule read_token = parse
  | "\n"          { new_line lexbuf; read_token lexbuf }
  | space+        { read_token lexbuf }
  | "(*"          { incr comment_lvl; read_comment lexbuf }
  | "*)"          { error "comment end before comment begin" }
  | "=>"          { RDARROW }
  | "->"          { RARROW }
  | "<-"          { LARROW }
  | "=="          { OP_EQ }
  | "!="          { OP_NEQ }
  | "<="          { OP_LE }
  | ">="          { OP_GE }
  | "<<"          { OP_SHL }
  | ">>"          { OP_SHR }
  | "&&"          { OP_ANDBOOL }
  | "||"          { OP_ORBOOL }
  | "^^"          { OP_XORBOOL }   
  | "."           { DOT }
  | ","           { COMMA }
  | ";"           { SEMICOLON }
  | ":"           { COLON }
  | "("           { LPAREN }
  | ")"           { RPAREN } 
  | "["           { LBRACKET }
  | "]"           { RBRACKET }
  | "{"           { LBRACE }
  | "}"           { RBRACE }   
  | "+"           { OP_PLUS }
  | "-"           { OP_MINUS }
  | "*"           { OP_MUL }
  | "/"           { OP_DIV }
  | "%"           { OP_MOD }
  | "<"           { OP_LT }
  | ">"           { OP_GT }
  | "!"           { OP_NOTBOOL }
  | "&"           { OP_ANDINT }
  | "|"           { OP_ORINT }
  | "^"           { OP_XORINT }
  | "~"           { OP_NOTINT }
  | "="           { BIND }
  | "_"           { UNDERSCORE }
  | "#"           { SHARP }
  | "\""
    {
      Buffer.clear string_buf;
      read_string lexbuf;
      LIT_STRING (Buffer.contents string_buf)
    }
  | hex_int_lit as il   { parse_int_lit il }
  | dec_int_lit as il   { parse_int_lit il }
  | '@' (ident as id)   { parse_annotation id }
  | ident as id
    {
      try (Hashtbl.find keywords id) with 
      Not_found -> IDENT id
    }
  | eof           { EOF }
  | _             { error "illegal character" }

and read_string = parse
  | letter as l { Buffer.add_char string_buf l; read_string lexbuf }
  | "\""        { () } 
  | eof         { error "unterminated string literal" }

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
  | "\n"  { new_line lexbuf; read_comment lexbuf }
  | eof   { error "unterminated comment" }
  | _     { read_comment lexbuf }
