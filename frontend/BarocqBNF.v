From BarocqComp Require Import Types Syntax Benum.

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
  | ERecordProj : atom -> ident -> expr
  | ERecordUpdate : atom -> ident -> atom -> expr
  | EDeepAccess : atom -> list access -> expr
  | EApp : atom -> list atom -> expr
  | EIfThenElse : atom -> expr -> expr -> expr
  | EMatch : atom -> list (pattern * expr) -> expr
  | ELetIn : ident -> expr -> expr -> expr.

(** ** Functions *)

Definition function : Type := Syntax.function expr btyp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function btyp.

(** ** Programs *)

Definition program : Type := Syntax.program globdef field_descr.