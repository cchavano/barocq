From BarocqComp Require Import Syntax.

(** * Asbtract syntax *)

(** ** Literals *)

Definition literal : Type := Syntax.literal.

(** ** Atoms *)

Definition atom : Type := Syntax.atom.

(** ** Statements *)

Inductive statement : Type :=
  | StBegin : list statement -> statement
  | StSet : ident -> comp -> statement
  | StIfThenElse : atom -> statement  -> statement -> statement.

(** ** Tail computations *)

Inductive tailcomp : Type :=
  | TcBegin : list statement -> tailcomp -> tailcomp
  | TcComp : comp -> tailcomp
  | TcIfThenElse : atom -> tailcomp -> tailcomp -> tailcomp.

(** ** Functions *)

Definition function : Type := Syntax.function tailcomp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function.

(** ** Programs *)

Definition program : Type := Syntax.program globdef.
