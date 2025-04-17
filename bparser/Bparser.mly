%{
  open Types
  open Syntax
  open Barocq
  open Camlcoq
  open Ctypesdefs

  type prefix_op = Plus | Minus
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
%token TYP_BOOL TYP_INT32 TYP_UINT32 TYP_INT64 TYP_UINT64 TYP_ARRAY
%token STRUCT DEF LET IN
%token IF THEN ELSE
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
%nonassoc OP_NOTBOOL OP_NOTINT
%nonassoc LPAREN LBRACKET
%nonassoc DOT
%nonassoc ARROW
%nonassoc TYP_ARRAY

%start xprogram
%type<Barocq.xprogram> xprogram
%%

xprogram:
  | xprog = list(command) EOF { xprog }

command:
  | def = topdef endcmd { CmdDef def }
  | e = expr endcmd { CmdExpr e }

%inline endcmd:
  | SEMICOLON SEMICOLON { }

topdef:
  | STRUCT id = ident BIND fields = struct_fields { DefStruct (id, fields) }
  | DEF x = ident COLON ty = ctyp BIND l = literal { DefConst (x, l, ty) }
  | DEF x = ident params = delimited(LPAREN, separated_list(COMMA, param), RPAREN)
    COLON ty = ctyp BIND e = expr { DefFun (x, {fn_return = ty; fn_params = params; fn_body = e}) }

param:
  | x = ident COLON ty = ctyp { (x, ty) }

expr:
  | TRUE { ETrue }
  | FALSE { EFalse }
  | i = LIT_INT32 { EInt32 (coqint_of_camlint (fst i), (snd i)) }
  | i = LIT_INT64 { EInt64 (coqint_of_camlint64 (fst i), (snd i)) }
  | v = ident { EVar v }
  | e1 = expr LBRACKET e2 = expr RBRACKET { EArrayGet (e1, e2) }
  | e1 = expr LBRACKET e2 = expr RBRACKET ARROW_INV e3 = expr { EArraySet (e1, e2, e3) }
  | e1 = expr DOT key = ident { EStructProj (e1, key) }
  | e1 = expr DOT key = ident ARROW_INV e2 = expr { EStructUpdate (e1, key, e2) }
  | LET x = ident BIND e1 = expr IN e2 = expr { ELetIn (x, e1, e2) }
  | IF e1 = expr THEN e2 = expr ELSE e3 = expr { EIfThenElse (e1, e2, e3) }
  | op = unary_op e = expr { EUnaryOp (op, e) }
  | OP_PLUS e = expr { e }
  | e1 = expr op = binary_op e2 = expr { EBinaryOp (op, e1, e2) }
  | e = expr args = delimited(LPAREN, separated_list(COMMA, expr), RPAREN) { EApp (e, args) }
  | e = delimited(LPAREN, expr, RPAREN) { e }

access:
  | DOT f = ident { Barocq.AcStructField f }
  | LBRACKET e = expr RBRACKET { Barocq.AcArrayIndex e }

literal:
  | TRUE { LTrue }
  | FALSE { LFalse }
  | p = prefix_op? i = LIT_INT32
    {
      let n = coqint_of_camlint (fst i) in
      let n = match p with Some Minus -> Camlcoq.Z.neg n | _ -> n in
      LInt32 (n, snd i)
    }
  | p = prefix_op? i = LIT_INT64
    {
      let n = coqint_of_camlint64 (fst i) in
      let n = match p with Some Minus -> Camlcoq.Z.neg n | _ -> n in
      LInt64 (n, snd i)
    }
  | a = delimited(LBRACKETBAR, separated_list(SEMICOLON, literal), RBRACKETBAR) { LArray a }
  | st = delimited(LBRACE, separated_nonempty_list(SEMICOLON, literal_field), RBRACE)
    HASHTAG ty = ident { LStruct (st, ty) }

prefix_op:
  | OP_PLUS { Plus }
  | OP_MINUS { Minus }

literal_field:
  | key = ident BIND l = literal { (key, l) }

%inline unary_op:
  | OP_NOTBOOL { UopNotbool }
  | OP_NOTINT { UopNotint }
  | OP_MINUS { UopNeg }

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
  | key = ident COLON ty = ctyp SEMICOLON { (key, ty) }

ctyp:
  | TYP_BOOL { CBool }
  | TYP_INT32 { CInt32 Signed }
  | TYP_UINT32 { CInt32 Unsigned }
  | TYP_INT64 { CInt64 Signed }
  | TYP_UINT64 { CInt64 Unsigned }
  | TYP_ARRAY ty = ctyp { CArray ty }
  | ty = ident { CStruct ty }
  | ty = funtyp { ty }
  | LPAREN ty = ctyp RPAREN { ty }

funtyp:
  | LPAREN RPAREN ARROW tret = ctyp { CFun ([], tret) }
  | tparam = ctyp ARROW tret = ctyp { CFun ([tparam], tret) }
  | LPAREN tparam1 = ctyp COMMA tparams = separated_nonempty_list(COMMA, ctyp)
    RPAREN ARROW tret = ctyp
    { CFun (tparam1 :: tparams, tret) }

ident:
  | id = IDENT { ident_of_string (coqstring_of_camlstring id) }