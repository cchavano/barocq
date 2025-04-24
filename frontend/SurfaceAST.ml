open Syntax

type ident = Syntax.ident Location.t

type styp =
  | SBool
  | SInt32 of Types.signedness
  | SInt64 of Types.signedness
  | SArray of styp
  | SStructOrAlias of ident
  | SFun of styp list * styp

type raw_expr =
  | ETrue
  | EFalse
  | EInt32 of Integers.Int.int * Types.signedness
  | EInt64 of Integers.Int.int * Types.signedness
  | EVar of ident
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
  | LStruct of (ident * literal) list * ident

and literal = raw_literal Location.t

type globdef =
  | DefAlias of ident * styp
  | DefStruct of ident * (ident * styp) list
  | DefConst of ident * literal * styp
  | DefFun of ident * func

type program = globdef list

type command =
  | CmdDef of globdef
  | CmdExpr of expr

type xprogram = command list
