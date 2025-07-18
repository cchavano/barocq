From Coq Require Import List.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Types Syntax.

(** * Abstract syntax *)

(** ** Literals *)

Inductive literal_base : Type :=
  | LbTrue : literal_base
  | LbFalse : literal_base
  | LbInt32 : int -> literal_base
  | LbInt64 : int64 -> literal_base
  | LbVar : ident -> literal_base.

Inductive literal : Type :=
  | LBase : literal_base -> btyp -> literal
  | LArray : list literal_base -> btyp -> literal
  | LRecord : list (ident * literal_base) -> btyp -> literal.

(** ** Atoms *)

Definition atom : Type := Syntax.Typed.atom.

Definition access : Type := Syntax.Typed.access.

(** ** Expressions ("pure" computations) *)

Inductive expr : Type :=
  | EAtom : atom -> btyp -> expr
  | EArrayGet : atom -> atom -> btyp -> expr
  | ERecordProj : atom -> ident -> btyp -> expr
  | EDeepAccess : atom -> list access -> btyp -> expr.

(** ** "Effectul" computations *)

Inductive ecomp : Type :=
  | EcArraySet : atom -> atom -> atom -> ecomp
  | EcRecordUpdate : atom -> ident -> atom -> ecomp.

(** ** Statements *)

Inductive statement : Type :=
  | StSkip : statement
  | StSetExpr : ident -> expr -> statement
  | StSetEcomp : ident -> ecomp -> statement
  | StCall : ident -> atom -> list atom -> statement
  | StIfThenElse : atom -> statement -> statement -> statement
  | StSequence : statement -> statement -> statement
  | StReturn : atom -> statement.

(** ** Functions *)

Record function : Type := mk_function {
  fn_return: btyp;
  fn_params: list (ident * btyp);
  fn_vars: list (ident * btyp);
  fn_body: statement
}.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function.

(** ** Programs *)

Definition program : Type := Syntax.program globdef.