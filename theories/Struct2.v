From Coq Require Import PArith List String.
From BarocqComp Require Import Error Common.

Definition key : Type := positive.

Definition key_eq_dec := Pos.eq_dec.

Inductive field (k: key) (A: Type) : Type :=
  Field : forall (a: A), field k A.

Arguments Field k {A}.

Inductive struct_t : list (ident * Type) -> Type :=
  | StNil : struct_t nil
  | StCons :
      forall {k: key} {A: Type} (f: field k A) {l: list (ident * Type)}
      (st: struct_t l), struct_t ((k, A) :: l).

From compcert Require Import Clightdefs.
Import ClightNotations.
Import ListNotations.

Open Scope clight_scope.
Open Scope string_scope.

Definition point : Type := struct_t [($"x", nat: Type); ($"y", nat: Type)].

Definition p := StCons (Field $"x" 5) (StCons (Field $"y" 6) StNil).

(* Declare Scope struct_scope.

Notation "{ }" := StNil (format "{ }") : struct_scope.
Notation "{ x }" := (StCons x StNil) : struct_scope.
Notation "{x ; y ; ... ; z }" :=
  (StCons x (StCons y .. (StCons z StNil) .. ))
  (format "[ '{' x ; '/' y ; '/' .. ; '/' z '}' ]") : struct_scope. *)



