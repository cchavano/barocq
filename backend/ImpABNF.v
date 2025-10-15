From BarocqComp Require Import Types Benum Syntax.

(** * Asbtract syntax *)

(** ** Literals *)

Definition literal : Type := Syntax.literal.

(** ** Atoms *)

Definition atom : Type := Syntax.atom.

(** ** Statements *)

Inductive statement : Type :=
  | StSequence : statement -> statement -> statement
  | StSet : ident -> comp -> statement
  | StIfThenElse : atom -> statement  -> statement -> statement
  | StSwitch : atom -> list (pattern * statement) -> statement.

(** ** Tail computations *)

Inductive tailcomp : Type :=
  | TcBegin : statement -> tailcomp -> tailcomp
  | TcComp : comp -> tailcomp
  | TcIfThenElse : atom -> tailcomp -> tailcomp -> tailcomp
  | TcSwitch : atom -> list (pattern * tailcomp) -> tailcomp.

(** ** Functions *)

Definition function : Type := Syntax.function tailcomp btyp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function btyp.

(** ** Programs *)

Definition program : Type := Syntax.program globdef btyp.
