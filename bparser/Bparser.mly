%{
  open Types
  open Syntax
  open Camlcoq
  open SurfaceAST
  open Location

  let aliases = Hashtbl.create 10

  (* A module name must begin with an uppercase letter. *)
  let valid_modul_ident mid =
    let re = Str.regexp {|^\([A-Z][a-zA-Z0-9_]*\)$|} in
    Str.string_match re mid 0

  (* An enum constructor name must begin with an uppercase letter. *)
  let valid_constr_ident eid =
    valid_modul_ident eid

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
%token RARROW
%token RDARROW
%token LARROW BIND
%token PIPE UNDERSCORE
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
%token INLINE ALWAYS_INLINE STATIC EXPORT UNIQUE
%token LET AND IN MATCH WITH END
%token IF THEN ELSE
%token AS
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
%nonassoc LPAREN LBRACKET
%nonassoc DOT
// %right RARROW
%nonassoc WITH
// %nonassoc TYP_ARRAY

%start imodul
%type<SurfaceAST.imodul> imodul
%%

imodul:
  | MODULE mname = mod_ident SEMISEMI?
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
        imd_vis = vis
      } 
    }

import:
  | IMPORT mname = mod_ident SEMISEMI? { mname }

visibility:
  | LBRACKET STATIC RBRACKET { Static }

command:
  | def = globdef SEMISEMI? { CmdDef def }
  | COMPUTE e = expr SEMISEMI? { CmdExpr e }

globdef:
  | TYPE id = ident BIND ty = styp { DefType (id, TdAlias ty) }
  | TYPE id = ident BIND elems = nonempty_list(enum_constr) { DefType (id, TdEnum elems) }
  | TYPE id = ident BIND fields = record_fields { DefType (id, TdRecord fields) }
  | TYPE id = ident OF kind = abs_type_kind { DeclType (id, kind) }
  | DEFN x = var_ident COLON ty = styp BIND c = const { DefConst (x, c, ty, false) }
  | UNIQUE DEFN x = var_ident COLON ty = styp BIND c = const { DefConst (x, c, ty, true) }
  | DEFN x = var_ident fd = fundef { DefFun (x, fd) }
  | attrs = nonempty_list(c_attr) DEFN x = var_ident fd = fundef { DefFun (x, {fd with fn_attribs = attrs}) }
  | DECL x = var_ident COLON ty = styp { mk_decl x ty false }
  | UNIQUE DECL x = var_ident COLON ty = styp { mk_decl x ty true }

fundef:
  | params = delimited(LPAREN, separated_list(COMMA, param), RPAREN)
    COLON ty = styp BIND e = expr { {fn_return = ty; fn_params = params; fn_body = e; fn_attribs = []} }

c_attr:
  | INLINE { Inline }
  | ALWAYS_INLINE { AlwaysInline }
  | STATIC { Vis Static }
  | EXPORT { Vis Export }

enum_constr:
  | PIPE id = IDENT
    {
      if valid_constr_ident id then
        Location.make $startpos $endpos id
      else
        raise Error
    }

abs_type_kind:
  | kind = LIT_STRING
    {
      match kind with
      | "struct" -> SU_struct
      | "union" -> SU_union
      | _ -> raise Error
    }

param:
  | x = var_ident COLON ty = styp { (x, ty) }

raw_expr:
  | TRUE { ETrue }
  | FALSE { EFalse }
  | i = LIT_INT32 { EInt32 (coqint_of_camlint (fst i), (snd i)) }
  | i = LIT_INT64 { EInt64 (coqint_of_camlint64 (fst i), (snd i)) }
  | v = cident
    {
      match v with
      | IdSimple id
      | IdPrefixed (_, id) ->
          let id = id.content in
          if valid_var_ident id then EVar v
          else if valid_constr_ident id then EConstr v
          else raise Error
    }
  | e = expr AS ty = styp { ECast (e, ty) }
  | e1 = expr LBRACKET e2 = expr RBRACKET { EArrayGet (e1, e2) }
  | e1 = expr LBRACKET e2 = expr RBRACKET LARROW e3 = expr { EArraySet (e1, e2, e3) }
  | e1 = expr DOT key = var_ident { ERecordProj (e1, key) }
  | e1 = expr DOT key = var_ident LARROW e2 = expr { ERecordUpdate (e1, [(key, e2)]) }
  | e1 = expr WITH le = delimited(LBRACE, nonempty_list(field_update), RBRACE) { ERecordUpdate (e1, le) }
  | LET le = separated_nonempty_list(AND, binding) IN e = expr { ELetIn (le, e) }
  | IF e1 = expr THEN e2 = expr ELSE e3 = expr { EIfThenElse (e1, e2, e3) }
  | MATCH e = expr WITH cases = nonempty_list(match_case) END { EMatch (e, cases) }
  | op = unary_op e = expr { EUnaryOp (op, e) }
  | e1 = expr op = binary_op e2 = expr { EBinaryOp (op, e1, e2) }
  | e = expr args = delimited(LPAREN, separated_list(COMMA, expr), RPAREN) { EApp (e, args) }

match_case:
  | PIPE cid = cident RDARROW e = expr
    { 
      match cid with
      | IdSimple id
      | IdPrefixed (_, id) ->
          if valid_constr_ident id.content then (PIdent cid, e)
          else raise Error
    }
  | PIPE und = underscore RDARROW e = expr { (und, e) }

underscore:
  | UNDERSCORE { PWildcard (Location.make $startpos $endpos ()) }

binding:
  | x = var_ident BIND e = expr { (x, e) }

var_ident:
  | id = IDENT
    {
      if valid_var_ident id then
        Location.make $startpos $endpos id
      else
        raise Error
    }

field_update:
  | x = var_ident LARROW e = expr SEMICOLON { (x, e) }

expr:
  | e = raw_expr { Location.make $startpos $endpos e }
  | e = delimited(LPAREN, expr, RPAREN) { e }

raw_const:
  | TRUE { SurfaceAST.CTrue }
  | FALSE { SurfaceAST.CFalse }
  | i = LIT_INT32 { SurfaceAST.CInt32 (coqint_of_camlint (fst i), (snd i)) }
  | i = LIT_INT64 { SurfaceAST.CInt64 (coqint_of_camlint64 (fst i), (snd i)) }
  | a = delimited(LBRACKETBAR, separated_list(SEMICOLON, const), RBRACKETBAR) { SurfaceAST.CArray a }
  | rc = delimited(LBRACE, nonempty_list(const_field), RBRACE) { SurfaceAST.CRecord rc }
  | id = cident { SurfaceAST.CVar id }
  | op = unary_op c = const { SurfaceAST.CUnop (op, c) }
  | c1 = const op = binary_op c2 = const { SurfaceAST.CBinop (op, c1, c2) }
  | c = const AS ty = styp { SurfaceAST.CCast (c, ty) }

const:
  | c = raw_const { Location.make $startpos $endpos c }
  | c = delimited(LPAREN, const, RPAREN) { c }

const_field:
  | key = var_ident BIND l = const SEMICOLON { (key, l) }

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

record_fields:
  | fields = delimited(LBRACE, nonempty_list(typ_field), RBRACE) { fields }

typ_field:
  | key = var_ident COLON ty = styp SEMICOLON { (key, ty) }

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
    RARROW tret = styp
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