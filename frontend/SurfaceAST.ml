open Syntax

type ident = string Location.t

(** Composed identifiers. A composed identifier refers either to a simple
    identifier which can be a local or an imported external identifier, or a
    prefixed identifier which correspond to an external identifer. *)
type cident =
  | IdSimple of ident
  | IdPrefixed of ident * ident

(** Surface types. At parsing, a type identifier cannot yet be distinguished
    between an enum type, a record type, an alias or an abstract type. *)
type styp =
  | SBool
  | SInt32 of Types.signedness
  | SInt64 of Types.signedness
  | SArray of styp_layout
  | SIdent of cident
  | SFun of (Syntax.param_attr * styp) list * styp

and raw_styp_layout =
  | SLBoxed of styp
  | SLUnboxed of styp * const option

and styp_layout = raw_styp_layout Location.t

and raw_const =
  | CTrue
  | CFalse
  | CInt32 of Integers.Int.int * Types.signedness
  | CInt64 of Integers.Int64.int * Types.signedness
  | CVar of cident
  | CArray of const list
  | CRecord of (ident * const) list
  | CUnop of unary_op * const
  | CBinop of binary_op * const * const
  | CCast of const * styp

and const = raw_const Location.t

(** Patterns for pattern-matching *)
type pattern =
  | PIdent of cident
  | PWildcard of unit Location.t

type raw_expr =
  | ETrue
  | EFalse
  | EInt32 of Integers.Int.int * Types.signedness
  | EInt64 of Integers.Int.int * Types.signedness
  | EConstr of cident
  | EVar of cident
  | ECast of expr * styp
  | EUnaryOp of unary_op * expr
  | EBinaryOp of binary_op * expr * expr
  | EArrayGet of expr * expr
  | EArraySet of expr * expr * expr
  | ERecordProj of expr * ident
  | ERecordUpdate of expr * (ident * expr) list
  | EApp of expr * expr list
  | EIfThenElse of expr * expr * expr
  | EMatch of expr * (pattern * expr) list
  | ELetIn of ident * expr * expr
  | EAttr  of ident * expr

and expr = raw_expr Location.t

type c_visibility =
  | Static
  | Export

type c_attr =
  | Inline
  | AlwaysInline
  | Vis of c_visibility

type func = {
  fn_return : styp;
  fn_params : (ident * styp) list;
  fn_body : expr;
  fn_attribs : c_attr list;
}

type type_def =
  | TdEnum of ident list
  | TdRecord of (ident * styp_layout) list
  | TdAlias of styp

type globdef =
  | DefType of ident * type_def
  | DefConst of ident * const * styp * bool
  | DefFun of ident * func
  | DeclType of ident * Syntax.struct_or_union
  | DeclConst of ident * styp * bool
  | DeclFun of ident * (Syntax.param_attr * styp) list * styp

type command =
  | CmdDef of globdef
  | CmdExpr of expr

type imodul = {
  imd_name : ident;
  imd_imports : ident list;
  imd_cmds : command list;
  imd_vis : c_visibility;
}

type iprogram = imodul list
