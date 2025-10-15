From Coq Require Import List.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Benum Types Syntax.

(** * Abstract syntax *)

(** ** Types *)

Inductive typ2 : Type :=
  | TVoid
  | TBool : typ2
  | TInt32 : signedness -> typ2
  | TInt64 : signedness -> typ2
  | TArray : typ2 -> typ2
  | TEnum : ident -> typ2
  | TRecord : ident -> typ2
  | TFun : list typ2 -> typ2 -> typ2
  | TAbs : ident -> typ2.

(** ** Literals *)

Inductive literal_base : Type :=
  | LbTrue : literal_base
  | LbFalse : literal_base
  | LbInt32 : int -> literal_base
  | LbInt64 : int64 -> literal_base
  | LbVar : ident -> literal_base.

Inductive literal : Type :=
  | LBase : literal_base -> typ2 -> literal
  | LArray : list literal_base -> typ2 -> literal
  | LRecord : list (ident * literal_base) -> typ2 -> literal.

(** ** Atoms *)

Inductive atom :=
  | ATrue : atom
  | AFalse : atom
  | AInt32 : int -> typ2 -> atom
  | AInt64 : int64 -> typ2 -> atom
  | AConstr : ident -> typ2 -> atom
  | AVar : ident -> typ2 -> atom
  | ACast : atom -> typ2 -> atom
  | AUnaryOp : unary_op -> atom -> typ2 -> atom
  | ABinaryOp : binary_op -> atom -> atom -> typ2 -> atom.

Inductive access : Type :=
  | AcRecordField : ident -> typ2 -> access
  | AcArrayIndex : atom -> typ2 -> access.

(** ** Expressions ("pure" computations) *)

Inductive expr : Type :=
  | EAtom : atom -> typ2 -> expr
  | EArrayGet : atom -> atom -> typ2 -> expr
  | ERecordProj : atom -> ident -> typ2 -> expr
  | EDeepAccess : atom -> list access -> typ2 -> expr.

(** ** "Effectul" computations *)

Inductive ecomp : Type :=
  | EcArraySet : atom -> atom -> atom -> ecomp
  | EcRecordUpdate : atom -> ident -> atom -> ecomp.

(** ** Statements *)

Inductive statement : Type :=
  | StSkip : statement
  | StSetExpr : ident -> expr -> statement
  | StEcomp : ecomp -> statement
  | StCall : option ident -> atom -> list atom -> typ2 -> statement
  | StIfThenElse : atom -> statement -> statement -> statement
  | StSwitch : atom -> list (pattern * statement) -> statement
  | StSequence : statement -> statement -> statement
  | StReturn : option atom -> statement.

(** ** Functions *)

Record function : Type := mk_function {
  fn_return: typ2;
  fn_params: list (ident * typ2);
  fn_vars: list (ident * typ2);
  fn_body: statement
}.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function typ2.

(** ** Programs *)

Definition program : Type := Syntax.program globdef typ2.