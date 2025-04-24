%{
  open Types
  open Syntax
  open Camlcoq
  open Ctypesdefs
  open SurfaceAST

  type prefix_op = Plus | Minus

  let aliases = Hashtbl.create 10

  let ident_of_camlstring x =
    ident_of_string (coqstring_of_camlstring x)

  let () =
    List.iter
      (fun (s, t) -> Hashtbl.add aliases s t)
      [
        ("hey", CBool)
      ]
%}

%token DOT COMMA SEMICOLON COLON
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACKETBAR RBRACKETBAR
%token LBRACE RBRACE
%token HASHTAG
%token ARROW
%token ARROW_INV BIND
%token OP_PLUS OP_MINUS OP_MUL OP_DIV OP_MOD
%token OP_ANDINT OP_ORINT OP_XORINT OP_NOTINT
%token OP_SHL OP_SHR
%token OP_EQ OP_NEQ OP_LT OP_GT OP_LE OP_GE
%token OP_ANDBOOL OP_ORBOOL OP_XORBOOL OP_NOTBOOL 
%token TRUE FALSE
%token TYPE
%token TYP_BOOL TYP_INT32 TYP_UINT32 TYP_INT64 TYP_UINT64 TYP_ARRAY
%token STRUCT DEF LET IN
%token IF THEN ELSE
%token AS
%token <int32 * Types.signedness> LIT_INT32
%token <int64 * Types.signedness> LIT_INT64
%token <string> IDENT
%token EOF

%nonassoc IN ELSE ARROW_INV
%left OP_GT OP_GE OP_LT OP_LE OP_EQ OP_NEQ
%left OP_ORBOOL OP_XORBOOL OP_ORINT OP_XORINT
%left OP_ANDBOOL OP_ANDINT
%left OP_PLUS OP_MINUS
%left OP_MUL OP_DIV OP_MOD
%left OP_SHL OP_SHR
%nonassoc AS
%nonassoc OP_NOTBOOL OP_NOTINT
%nonassoc LPAREN LBRACKET
%nonassoc DOT
%nonassoc ARROW
%nonassoc TYP_ARRAY

%start xprogram
%type<SurfaceAST.xprogram> xprogram
%%

xprogram:
  | xprog = list(command) EOF { xprog }

command:
  | def = topdef endcmd { CmdDef def }
  | e = expr endcmd { CmdExpr e }

%inline endcmd:
  | SEMICOLON SEMICOLON { }

topdef:
  | TYPE id = typ_ident BIND ty = styp { DefAlias (id, ty) }
  | STRUCT id = typ_ident BIND fields = struct_fields { DefStruct (id, fields) }
  | DEF x = ident COLON ty = styp BIND l = literal { DefConst (x, l, ty) }
  | DEF x = ident params = delimited(LPAREN, separated_list(COMMA, param), RPAREN)
    COLON ty = styp BIND e = expr { DefFun (x, {fn_return = ty; fn_params = params; fn_body = e}) }

param:
  | x = ident COLON ty = styp { (x, ty) }

raw_expr:
  | TRUE { ETrue }
  | FALSE { EFalse }
  | i = LIT_INT32 { EInt32 (coqint_of_camlint (fst i), (snd i)) }
  | i = LIT_INT64 { EInt64 (coqint_of_camlint64 (fst i), (snd i)) }
  | v = ident { EVar v }
  | e = expr AS ty = styp { ECast (e, ty) }
  | e1 = expr LBRACKET e2 = expr RBRACKET { EArrayGet (e1, e2) }
  | e1 = expr LBRACKET e2 = expr RBRACKET ARROW_INV e3 = expr { EArraySet (e1, e2, e3) }
  | e1 = expr DOT key = ident { EStructProj (e1, key) }
  | e1 = expr DOT key = ident ARROW_INV e2 = expr { EStructUpdate (e1, key, e2) }
  | LET x = ident BIND e1 = expr IN e2 = expr { ELetIn (x, e1, e2) }
  | IF e1 = expr THEN e2 = expr ELSE e3 = expr { EIfThenElse (e1, e2, e3) }
  | op = unary_op e = expr { EUnaryOp (op, e) }
  | e1 = expr op = binary_op e2 = expr { EBinaryOp (op, e1, e2) }
  | e = expr args = delimited(LPAREN, separated_list(COMMA, expr), RPAREN) { EApp (e, args) }

expr:
  | e = raw_expr { Location.make $startpos $endpos e }
  | e = delimited(LPAREN, expr, RPAREN) { e }

raw_literal:
  | TRUE { SurfaceAST.LTrue }
  | FALSE { SurfaceAST.LFalse }
  | p = prefix_op? i = LIT_INT32
    {
      let n = coqint_of_camlint (fst i) in
      let n = match p with Some Minus -> Camlcoq.Z.neg n | _ -> n in
      SurfaceAST.LInt32 (n, snd i)
    }
  | p = prefix_op? i = LIT_INT64
    {
      let n = coqint_of_camlint64 (fst i) in
      let n = match p with Some Minus -> Camlcoq.Z.neg n | _ -> n in
      SurfaceAST.LInt64 (n, snd i)
    }
  | a = delimited(LBRACKETBAR, separated_list(SEMICOLON, literal), RBRACKETBAR) { SurfaceAST.LArray a }
  | st = delimited(LBRACE, separated_nonempty_list(SEMICOLON, literal_field), RBRACE)
    HASHTAG ty = ident { SurfaceAST.LStruct (st, ty) }

literal:
  | l = raw_literal { Location.make $startpos $endpos l }

prefix_op:
  | OP_PLUS { Plus }
  | OP_MINUS { Minus }

literal_field:
  | key = ident BIND l = literal { (key, l) }

%inline unary_op:
  | OP_NOTBOOL { UopNotbool }
  | OP_NOTINT { UopNotint }
  | OP_MINUS { UopNeg }
  | OP_PLUS { UopPlus }

%inline binary_op:
  | OP_ANDBOOL { BopAndbool }
  | OP_ORBOOL { BopOrbool }
  | OP_XORBOOL { BopXorbool }
  | OP_PLUS { BopAdd }
  | OP_MINUS { BopSub }
  | OP_MUL { BopMul }
  | OP_DIV { BopDiv }
  | OP_MOD { BopMod }
  | OP_ANDINT { BopAndint }
  | OP_ORINT { BopOrint }
  | OP_XORINT { BopXorint }
  | OP_SHL { BopShl }
  | OP_SHR { BopShr }
  | OP_EQ { BopEq }
  | OP_NEQ { BopNeq }
  | OP_LT { BopLt }
  | OP_GT { BopGt }
  | OP_LE { BopLe }
  | OP_GE { BopGe }

struct_fields:
  | fields = delimited(LBRACE, nonempty_list(typ_field), RBRACE) { fields }

typ_field:
  | key = ident COLON ty = styp SEMICOLON { (key, ty) }

styp:
  | TYP_BOOL { SBool }
  | TYP_INT32 { SInt32 Signed }
  | TYP_UINT32 { SInt32 Unsigned }
  | TYP_INT64 { SInt64 Signed }
  | TYP_UINT64 { SInt64 Unsigned }
  | TYP_ARRAY ty = styp { SArray ty }
  | ty = typ_ident { SStructOrAlias ty }
  | ty = funtyp { ty }
  | LPAREN ty = styp RPAREN { ty }

funtyp:
  | LPAREN RPAREN ARROW tret = styp { SFun ([], tret) }
  | tparam = styp ARROW tret = styp { SFun ([tparam], tret) }
  | LPAREN tparam1 = styp COMMA tparams = separated_nonempty_list(COMMA, styp)
    RPAREN ARROW tret = styp
    { SFun (tparam1 :: tparams, tret) }

typ_ident:
  | id = IDENT
    {
      if String.contains id '\'' then raise Error
      else Location.make $startpos $endpos (ident_of_camlstring id)
    }

ident:
  | id = IDENT { Location.make $startpos $endpos (ident_of_camlstring id) }