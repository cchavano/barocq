%{
  open Types
  open Syntax
  open Camlcoq
  open SurfaceAST

  let aliases = Hashtbl.create 10

  (* A module name must begin with an uppercase letter. *)
  let valid_modul_ident mid =
    let re = Str.regexp {|^\([A-Z][a-zA-Z0-9_]*\)$|} in
    Str.string_match re mid 0

  let () =
    List.iter
      (fun (s, t) -> Hashtbl.add aliases s t)
      [
        ("hey", BBool)
      ]
%}

%token MODULE
%token IMPORT
%token DOT COMMA SEMICOLON COLON SEMISEMI
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACKETBAR RBRACKETBAR
%token LBRACE RBRACE
%token ARROW
%token ARROW_INV BIND
%token OP_PLUS OP_MINUS OP_MUL OP_DIV OP_MOD
%token OP_ANDINT OP_ORINT OP_XORINT OP_NOTINT
%token OP_SHL OP_SHR
%token OP_EQ OP_NEQ OP_LT OP_GT OP_LE OP_GE
%token OP_ANDBOOL OP_ORBOOL OP_XORBOOL OP_NOTBOOL 
%token TRUE FALSE
%token TYP_BOOL TYP_INT32 TYP_UINT32 TYP_INT64 TYP_UINT64 TYP_ARRAY
%token COMPUTE
%token DEFN DECL TYPE OF
%token AT_READONLY AT_WRITE
%token LET AND IN WITH
%token IF THEN ELSE
%token AS
%token <string> LIT_STRING
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
// %right ARROW
%nonassoc WITH
// %nonassoc TYP_ARRAY

%start imodul
%type<SurfaceAST.imodul> imodul
%%

imodul:
  | MODULE mname = mod_ident SEMISEMI?
    imports = list(import)
    cmds = list(command) EOF
    {
      {
        imd_name = mname;
        imd_imports = List.rev imports;
        imd_cmds = cmds
      } 
    }

import:
  | IMPORT mname = mod_ident SEMISEMI? { mname }

command:
  | def = globdef SEMISEMI? { CmdDef def }
  | COMPUTE e = expr SEMISEMI? { CmdExpr e }

globdef:
  | TYPE id = ident BIND ty = styp { DefAlias (id, ty) }
  | TYPE id = ident BIND fields = struct_fields { DefType (id, fields) }
  | TYPE id = ident OF kind = abs_type_kind { DeclType (id, kind) }
  | DEFN x = ident COLON ty = styp BIND c = const { DefConst (x, c, ty) }
  | DEFN x = ident params = delimited(LPAREN, separated_list(COMMA, param), RPAREN)
    COLON ty = styp BIND e = expr { DefFun (x, {fn_return = ty; fn_params = params; fn_body = e}) }
  | DECL x = ident COLON ty = styp
    {
      match ty with
      | SFun (tparams, tret) -> DeclFun (x, tparams, tret)
      | _ -> DeclConst (x, ty)
    }

abs_type_kind:
  | kind = LIT_STRING
    {
      match kind with
      | "struct" -> Ctypes.Struct 
      | "union" -> Ctypes.Union
      | _ -> raise Error
    }

param:
  | x = ident COLON ty = styp { (x, ty) }

raw_expr:
  | TRUE { ETrue }
  | FALSE { EFalse }
  | i = LIT_INT32 { EInt32 (coqint_of_camlint (fst i), (snd i)) }
  | i = LIT_INT64 { EInt64 (coqint_of_camlint64 (fst i), (snd i)) }
  | v = cident { EVar v }
  | e = expr AS ty = styp { ECast (e, ty) }
  | e1 = expr LBRACKET e2 = expr RBRACKET { EArrayGet (e1, e2) }
  | e1 = expr LBRACKET e2 = expr RBRACKET ARROW_INV e3 = expr { EArraySet (e1, e2, e3) }
  | e1 = expr DOT key = ident { ERecordProj (e1, key) }
  | e1 = expr DOT key = ident ARROW_INV e2 = expr { ERecordUpdate (e1, [(key, e2)]) }
  | e1 = expr WITH le = delimited(LBRACE, nonempty_list(field_update), RBRACE) { ERecordUpdate (e1, le) }
  | LET le = separated_nonempty_list(AND, binding) IN e = expr { ELetIn (le, e) }
  | IF e1 = expr THEN e2 = expr ELSE e3 = expr { EIfThenElse (e1, e2, e3) }
  | op = unary_op e = expr { EUnaryOp (op, e) }
  | e1 = expr op = binary_op e2 = expr { EBinaryOp (op, e1, e2) }
  | e = expr args = delimited(LPAREN, separated_list(COMMA, expr), RPAREN) { EApp (e, args) }

binding:
  | x = ident BIND e = expr { (x, e) }

field_update:
  | x = ident ARROW_INV e = expr SEMICOLON { (x, e) }

expr:
  | e = raw_expr { Location.make $startpos $endpos e }
  | e = delimited(LPAREN, expr, RPAREN) { e }

raw_const:
  | TRUE { SurfaceAST.CTrue }
  | FALSE { SurfaceAST.CFalse }
  | i = LIT_INT32 { SurfaceAST.CInt32 (coqint_of_camlint (fst i), (snd i)) }
  | i = LIT_INT64 { SurfaceAST.CInt64 (coqint_of_camlint64 (fst i), (snd i)) }
  | a = delimited(LBRACKETBAR, separated_list(SEMICOLON, const), RBRACKETBAR) { SurfaceAST.CArray a }
  | rc = delimited(LBRACE, nonempty_list(const_field), RBRACE)
    { SurfaceAST.CRecord rc }
  | id = cident { SurfaceAST.CVar id }
  | op = unary_op c = const { SurfaceAST.CUnop (op, c) }
  | c1 = const op = binary_op c2 = const { SurfaceAST.CBinop (op, c1, c2) }
  | c = const AS ty = styp { SurfaceAST.CCast (c, ty) }

const:
  | c = raw_const { Location.make $startpos $endpos c }
  | c = delimited(LPAREN, const, RPAREN) { c }

const_field:
  | key = ident BIND l = const SEMICOLON { (key, l) }

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
  | sty = styp_simpl { sty }
  | TYP_ARRAY ty = styp_simpl { SArray ty }
  | TYP_ARRAY LPAREN ty = styp RPAREN { SArray ty }
  | ty = styp_func { ty }

styp_simpl:
  | TYP_BOOL { SBool }
  | TYP_INT32 { SInt32 Signed }
  | TYP_UINT32 { SInt32 Unsigned }
  | TYP_INT64 { SInt64 Signed }
  | TYP_UINT64 { SInt64 Unsigned }
  | ty = cident { SIdent ty }

styp_func:
  | tparams = delimited(LPAREN, separated_list(COMMA, styp_func_param), RPAREN)
    ARROW tret = styp
    { SFun (tparams, tret) }

styp_func_param:
  | AT_READONLY ty = styp { (AttrReadonly, ty) }
  | AT_WRITE ty = styp { (AttrWrite, ty) }
  | ty = styp { (AttrNone, ty) }

mod_ident:
  | id = IDENT
    {
      if valid_modul_ident id then
        Location.make $startpos $endpos id
      else
        raise Error
    }

cident:
  | id = ident { IdSimple id }
  | mname = mod_ident COLON COLON id = ident { IdPrefixed (mname, id) }

ident:
  | id = IDENT { Location.make $startpos $endpos id }