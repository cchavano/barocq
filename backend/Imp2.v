From Coq Require Import List.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Types Syntax Benum.

(** * Abstract syntax *)

(** ** Types *)

Inductive typ2 : Type :=
  | TVoid : typ2
  | TBool : typ2
  | TInt32 : signedness -> typ2
  | TInt64 : signedness -> typ2
  | TArray : typ2 -> layout -> typ2
  | TEnum : ident -> typ2
  | TRecord : ident -> typ2
  | TFun : list typ2 -> typ2 -> typ2
  | TAbs : ident -> typ2.

(** ** Literals *)

Inductive literal :=
  | LTrue : literal
  | LFalse : literal
  | LInt32 : int -> signedness -> literal
  | LInt64 : int64 -> signedness -> literal
  | LVar : ident -> typ2 -> literal
  | LArray : list literal -> typ2 -> layout -> literal
  | LRecord : list (ident * literal) -> list ident -> ident -> literal.

(** ** Atoms *)

Inductive atom :=
  | ATrue : atom
  | AFalse : atom
  | AInt32 : int -> signedness -> atom
  | AInt64 : int64 -> signedness -> atom
  | AConstr : ident -> int -> typ2 -> atom
  | AVar : ident -> typ2 -> atom
  | ACast : atom -> typ2 -> atom
  | AUnaryOp : unary_op -> atom -> typ2 -> atom
  | ABinaryOp : binary_op -> atom -> atom -> typ2 -> atom
  | AArrayGet : atom -> atom -> layout -> typ2 -> atom
  | ARecordProj : atom -> ident -> layout -> typ2 -> atom
  | APureCall : ident -> typ2 -> list atom -> typ2 -> atom.

(** ** "Effectul" computations *)

Inductive ecomp : Type :=
  | EcArraySet : atom -> atom -> atom -> ecomp
  | EcRecordUpdate : atom -> ident -> atom -> ecomp.

(** ** Statements *)

Inductive statement : Type :=
  | StSkip : statement
  | StSet : ident -> atom -> statement
  | StEcomp : ecomp -> statement
  | StCall : option ident -> ident -> typ2 -> list atom -> typ2 -> statement
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

Definition program : Type := Syntax.program globdef (typ2 * layout).

Definition typof_atom (a: atom) : typ2 :=
  match a with
  | ATrue
  | AFalse => TBool
  | AInt32 _ s => TInt32 s
  | AInt64 _ s => TInt64 s
  | AConstr _ _ ty
  | AVar _ ty
  | ACast _ ty
  | AUnaryOp _ _ ty
  | ABinaryOp _ _ _ ty
  | AArrayGet _ _ _ ty
  | ARecordProj _ _ _ ty
  | APureCall _ _ _ ty => ty
  end.