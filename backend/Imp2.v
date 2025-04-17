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
  | LBase : literal_base -> ctyp -> literal
  | LArray : list literal_base -> ctyp -> literal
  | LStruct : list (ident * literal_base) -> ctyp -> literal.

(** ** Atoms *)

Definition atom : Type := Syntax.Typed.atom.

Definition access : Type := Syntax.Typed.access.

(** ** Expressions ("pure" computations) *)

Inductive expr : Type :=
  | EAtom : atom -> ctyp -> expr
  | EArrayGet : atom -> atom -> ctyp -> expr
  | EStructProj : atom -> ident -> ctyp -> expr
  | EDeepAccess : atom -> list access -> ctyp -> expr.

(** ** "Effectul" computations *)

Inductive ecomp : Type :=
  | EcArraySet : atom -> atom -> atom -> ecomp
  | EcStructUpdate : atom -> ident -> atom -> ecomp.

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
  fn_return: ctyp;
  fn_params: list (ident * ctyp);
  fn_vars: list (ident * ctyp);
  fn_body: statement
}.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function.

(** ** Programs *)

Definition program : Type := Syntax.program globdef.