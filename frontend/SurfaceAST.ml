open Syntax

type ident = string Location.t

(** Composed identifiers. A composed identifier refers either to a simple
    identifier which can be local or external (and imported), or a prefixed
    identifier which correspond to an external identifer. *)
type cident =
  | IdSimple of ident
  | IdPrefixed of ident * ident

(** Surface types. At parsing, a type identifier cannot yet be distinguished
    between a struct type, an alias or an abstract type. *)
type styp =
  | SBool
  | SInt32 of Types.signedness
  | SInt64 of Types.signedness
  | SArray of styp
  | SIdent of cident
  | SFun of (Syntax.param_attr * styp) list * styp

type raw_expr =
  | ETrue
  | EFalse
  | EInt32 of Integers.Int.int * Types.signedness
  | EInt64 of Integers.Int.int * Types.signedness
  | EVar of cident
  | ECast of expr * styp
  | EUnaryOp of unary_op * expr
  | EBinaryOp of binary_op * expr * expr
  | EArrayGet of expr * expr
  | EArraySet of expr * expr * expr
  | EStructProj of expr * ident
  | EStructUpdate of expr * ident * expr
  | EApp of expr * expr list
  | EIfThenElse of expr * expr * expr
  | ELetIn of ident * expr * expr

and expr = raw_expr Location.t

type func = {
  fn_return : styp;
  fn_params : (ident * styp) list;
  fn_body : expr;
}

type raw_literal =
  | LTrue
  | LFalse
  | LInt32 of Integers.Int.int * Types.signedness
  | LInt64 of Integers.Int64.int * Types.signedness
  | LArray of literal list
  | LStruct of (ident * literal) list

and literal = raw_literal Location.t

type globdef =
  | DefAlias of ident * styp
  | DefType of ident * (ident * styp) list
  | DefConst of ident * literal * styp
  | DefFun of ident * func
  | DeclType of ident * Ctypes.struct_or_union
  | DeclConst of ident * styp
  | DeclFun of ident * (Syntax.param_attr * styp) list * styp

type modul = {
  md_name : ident;
  md_imports : ident list;
  md_defs : globdef list;
}

type program = modul list

type command =
  | CmdDef of globdef
  | CmdExpr of expr

type imodul = {
  imd_name : ident;
  imd_imports : ident list;
  imd_cmds : command list;
}

type iprogram = imodul list
