%{
  open Types
  open Syntax
  open Camlcoq
  open SurfaceAST
  open Location

  (* A module name must consist only of alphanum characaters and begin with a capital letter. *)
  let valid_modul_ident mid =
    let re = Str.regexp {|^\([A-Z][a-zA-Z0-9]*\)$|} in
    Str.string_match re mid 0

  (* An enum constructor name must begin with an uppercase letter. *)
  let valid_constr_ident eid =
    let re = Str.regexp {|^\([A-Z][a-zA-Z0-9_]*\)$|} in
    Str.string_match re eid 0

  (* A global or local variable / function cannot begin with an uppercase letter. *)
  let valid_var_ident vid =
    let re = Str.regexp {|^\([_|a-z][a-zA-Z0-9_]*\)$|} in
    Str.string_match re vid 0

  let mk_decl x ty is_glob =
    match ty with
    | SFun (tparams, tret) ->
        if is_glob then raise Error else
        SurfaceAST.DeclFun (x, tparams, tret)
    | _ -> SurfaceAST.DeclConst (x, ty, is_glob)
%}

%token MODULE IMPORT
%token DOT COMMA SEMICOLON COLON
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE
%token RARROW
%token RDARROW
%token LARROW BIND
%token UNDERSCORE
%token OP_PLUS OP_MINUS OP_MUL OP_DIV OP_MOD
%token OP_ANDINT OP_ORINT OP_XORINT OP_NOTINT
%token OP_SHL OP_SHR
%token OP_EQ OP_NEQ OP_LT OP_GT OP_LE OP_GE
%token OP_ANDBOOL OP_ORBOOL OP_XORBOOL OP_NOTBOOL
%token AS
%token TRUE FALSE
%token SHARP
%token TYP_BOOL TYP_I32 TYP_U32 TYP_I64 TYP_U64
%token COMPUTE
%token DEFN DECL RECORD ENUM TYPE OF
%token READ WRITE
%token INLINE ALWAYS_INLINE STATIC ALL_STATIC EXPORT
%token UNIQUE
%token LET IN
%token MATCH WITH END
%token IF THEN ELSE
%token <string> LIT_STRING
%token <int32 * Types.signedness> LIT_INT32
%token <int64 * Types.signedness> LIT_INT64
%token <string> IDENT
%token EOF

%nonassoc IN ELSE LARROW
%left OP_ORBOOL OP_XORBOOL OP_ORINT OP_XORINT
%left OP_ANDBOOL OP_ANDINT
%left OP_GT OP_GE OP_LT OP_LE OP_EQ OP_NEQ
%left OP_PLUS OP_MINUS
%left OP_MUL OP_DIV OP_MOD
%left OP_SHL OP_SHR
%nonassoc AS
%nonassoc OP_NOTBOOL OP_NOTINT
%nonassoc LPAREN LBRACKET RBRACKET
%nonassoc DOT

%start imodul
%type<SurfaceAST.imodul> imodul
%%

imodul:
  | MODULE mname = mod_ident
    imports = list(import)
    vis = option(visibility)
    cmds = list(command) EOF
    {
      let vis =
        match vis with
        | Some Static -> Static
        | _ -> Export
      in
      {
        imd_name = mname;
        imd_imports = List.rev imports;
        imd_cmds = cmds;
        imd_vis = vis;
      }
    }

mod_ident:
  | id = IDENT
    {
      if valid_modul_ident id then
        Location.make $startpos $endpos id
      else
        raise Error
    }

import:
  | IMPORT mname = mod_ident { mname }

visibility:
  | ALL_STATIC { Static }

command:
  | def = globdef { CmdDef def }
  | COMPUTE LPAREN e = expr RPAREN { CmdExpr e }

globdef:
  | TYPE id = ident BIND ty = styp { DefType (id, TdAlias ty) }
  | ENUM id = ident elems = delimited(LBRACE, nonempty_list(enum_constr), RBRACE)
    { DefType (id, TdEnum elems) }
  | RECORD id = ident fields = record_fields { DefType (id, TdRecord fields) }
  | TYPE id = ident OF kind = abs_type_kind { DeclType (id, kind) }
  | DEFN x = var_ident COLON ty = styp BIND c = const { DefConst (x, c, ty, false) }
  | UNIQUE DEFN x = var_ident COLON ty = styp BIND c = const
    { DefConst (x, c, ty, true) }
  | DEFN x = var_ident fd = fundef { DefFun (x, fd) }
  | attrs = nonempty_list(c_attr) DEFN x = var_ident fd = fundef
    { DefFun (x, {fd with fn_attribs = attrs}) }
  | DECL x = var_ident COLON ty = styp { mk_decl x ty false }
  | UNIQUE DECL x = var_ident COLON ty = styp { mk_decl x ty true }

enum_constr:
  | id = IDENT COMMA
    {
      if valid_constr_ident id then
        Location.make $startpos $endpos id
      else
        raise Error
    }

record_fields:
  | fields = delimited(LBRACE, nonempty_list(field), RBRACE) { fields }

field:
  | key = var_ident COLON ty = styp_layout COMMA { (key, ty) }

abs_type_kind:
  | kind = LIT_STRING
    {
      match kind with
      | "struct" -> SU_struct
      | "union" -> SU_union
      | _ -> raise Error
    }

fundef:
  | params = delimited(LPAREN, separated_list(COMMA, param), RPAREN)
    COLON ty = styp BIND e = expr
    { { fn_return = ty; fn_params = params; fn_body = e; fn_attribs = [] } }

param:
  | x = var_ident COLON ty = styp { (x, ty) }
  
c_attr:
  | INLINE { Inline }
  | ALWAYS_INLINE { AlwaysInline }
  | STATIC { Vis Static }
  | EXPORT { Vis Export }

attr_id :
  | id = ident {id}


raw_expr:
  | TRUE { ETrue }
  | FALSE { EFalse }
  | SHARP LBRACKET id = attr_id RBRACKET  e = expr {EAttr(id,  e)}
  | i = LIT_INT32 { EInt32 (coqint_of_camlint (fst i), (snd i)) }
  | i = LIT_INT64 { EInt64 (coqint_of_camlint64 (fst i), (snd i)) }
  | cid = cident
    {
      match cid with
      | IdSimple id
      | IdPrefixed (_, id) ->
          let id = id.content in
          if valid_constr_ident id then EConstr cid
          else if valid_var_ident id then EVar cid
          else raise Error
    }
  | e = expr AS ty = styp { ECast (e, ty) }
  | e1 = expr LBRACKET e2 = expr RBRACKET { EArrayGet (e1, e2) }
  | e1 = expr LBRACKET e2 = expr RBRACKET LARROW e3 = expr { EArraySet (e1, e2, e3) }
  | e1 = expr DOT key = var_ident { ERecordProj (e1, key) }
  | e1 = expr DOT key = var_ident LARROW e2 = expr
    { ERecordUpdate (e1, [(key, e2)]) }
  | LBRACE e1 = expr WITH le = nonempty_list(field_update) RBRACE
    { ERecordUpdate (e1, le) }
  | LET x = var_ident BIND e1 = expr IN e2 = expr { ELetIn (x, e1, e2) }
  | IF e1 = expr THEN e2 = expr ELSE e3 = expr { EIfThenElse (e1, e2, e3) }
  | MATCH e = expr WITH cases = nonempty_list(match_case) END { EMatch (e, cases) }
  | op = unary_op e = expr { EUnaryOp (op, e) }
  | e1 = expr op = binary_op e2 = expr { EBinaryOp (op, e1, e2) }
  | e = expr args = delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { EApp (e, args) }

expr:
  | e = raw_expr { Location.make $startpos $endpos e }
  | e = delimited(LPAREN, expr, RPAREN) { e }

match_case:
  | cid = cident RDARROW e = expr
    { 
      match cid with
      | IdSimple id
      | IdPrefixed (_, id) ->
          if valid_constr_ident id.content then (PIdent cid, e)
          else raise Error
    }
  | und = underscore RDARROW e = expr { (und, e) }

underscore:
  | UNDERSCORE { PWildcard (Location.make $startpos $endpos ()) }

field_update:
  | x = var_ident LARROW e = expr COMMA { (x, e) }

raw_const:
  | TRUE { SurfaceAST.CTrue }
  | FALSE { SurfaceAST.CFalse }
  | i = LIT_INT32 { SurfaceAST.CInt32 (coqint_of_camlint (fst i), (snd i)) }
  | i = LIT_INT64 { SurfaceAST.CInt64 (coqint_of_camlint64 (fst i), (snd i)) }
  | a = delimited(LBRACKET, separated_list(COMMA, const), RBRACKET)
    { SurfaceAST.CArray a }
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
  | key = var_ident BIND l = const COMMA { (key, l) }

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

styp:
  | TYP_BOOL { SBool }
  | TYP_I32 { SInt32 Signed }
  | TYP_U32 { SInt32 Unsigned }
  | TYP_I64 { SInt64 Signed }
  | TYP_U64 { SInt64 Unsigned }
  | ty = cident { SIdent ty }
  | LBRACKET ty = styp_layout RBRACKET { SArray ty }
  | tparams = delimited(LPAREN, separated_list(COMMA, styp_func_param), RPAREN)
    RARROW tret = styp
    { SFun (tparams, tret) }

styp_layout:
  | ty = raw_styp_layout { Location.make $startpos $endpos ty}

raw_styp_layout:
  | ty = styp { SLBoxed ty }
  | SHARP ty = styp { SLUnboxed (ty, None) }
  | SHARP LBRACKET ty = styp_layout SEMICOLON sz = const RBRACKET
    { SLUnboxed(SArray ty, Some sz) }

styp_func_param:
  | READ ty = styp { (AttrReadonly, ty) }
  | WRITE ty = styp { (AttrWrite, ty) }
  | ty = styp { (AttrNone, ty) }

cident:
  | id = ident { IdSimple id }
  | mname = mod_ident COLON COLON id = ident { IdPrefixed (mname, id) }

var_ident:
  | id = IDENT
    {
      if valid_var_ident id then
        Location.make $startpos $endpos id
      else
        raise Error
    }

ident:
  | id = IDENT { Location.make $startpos $endpos id }
