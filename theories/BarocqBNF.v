From BarocqComp Require Import Syntax.

(** * Abstract syntax *)

(** ** Literals *)

Definition literal : Type := Syntax.literal.

(** ** Atoms *)

Definition atom : Type := Syntax.atom.

(** ** Expressions *)

Inductive expr : Type :=
  | EAtom : atom -> expr
  | EArrayGet : atom -> atom -> expr
  | EArraySet : atom -> atom -> atom -> expr
  | EStructProj : atom -> ident -> expr
  | EStructUpdate : atom -> ident -> atom -> expr
  | EApp : atom -> list atom -> expr
  | EIfThenElse : atom -> expr -> expr -> expr
  | ELetIn : ident -> expr -> expr -> expr.

(** ** Functions *)

Definition function : Type := Syntax.function expr.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function.

(** ** Programs *)

Definition program : Type := Syntax.program globdef.