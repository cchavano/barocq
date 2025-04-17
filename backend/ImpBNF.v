From BarocqComp Require Import Syntax.

(** * Abstract syntax *)

(** ** Literals *)

Definition literal : Type := Syntax.literal.

(** ** Atoms *)

Definition atom : Type := Syntax.atom.

(** ** Tail computations *)

Inductive tailcomp : Type :=
  | TcBegin : statement -> tailcomp -> tailcomp
  | TcComp : comp -> tailcomp
  | TcIfThenElse : atom -> tailcomp -> tailcomp -> tailcomp

(** ** Statements *)

with statement : Type :=
  | StSetTailcomp : ident -> tailcomp -> statement.

(** ** Functions *)

Definition function : Type := Syntax.function tailcomp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function.

(** ** Programs *)

Definition program : Type := Syntax.program globdef.