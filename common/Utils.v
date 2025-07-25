From Coq Require Import PArith ZArith String DecimalString List MSetPositive.
From compcert Require Import AST Ctypesdefs Maps Integers.
From BarocqComp Require Import Error Monads Ident.
Import MonCounter.
Import MonCounterErr.
Import ListNotations.

(** * Identifiers *)

Definition transl_user_ident (i: Ident.t) : Ident.t :=
  Ident.prefix_with "u_" i.

Open Scope state_monad_scope.

Definition fresh_var (prefix: string) : cmon Ident.t :=
  let* ctr := MonCounter.get in
  let var := Ident.prefix_with prefix (Ident.of_str_nat ctr) in
  MonCounter.incr var.

Close Scope state_monad_scope.

Open Scope state_err_monad_scope.

Definition fresh_var_err (prefix: string) : crmon Ident.t :=
  let* ctr := MonCounterErr.get in
  let var := Ident.prefix_with prefix (Ident.of_str_nat ctr) in
  MonCounterErr.incr var.

Close Scope state_err_monad_scope.

(** * Lists *)

Definition nth_err {A: Type} (l: list A) (n: nat) : res A :=
  err_of_opt (nth_error l n).

Fixpoint fold_left_err {A B: Type} (f: A -> B -> res A) (l: list B) (a0: res A) : res A :=
  match l with
  | nil => a0
  | x :: l' =>
      let* a0 := a0 in
      fold_left_err f l' (f a0 x)
  end.

Definition list_is_empty {A: Type} (l: list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.
  
(** * Sets *)

Notation pset := PositiveSet.t.

Definition smem (s: pset) (p: positive) : bool := PositiveSet.mem p s.

Definition sadd (s: pset) (p: positive) : pset := PositiveSet.add p s.

Definition sremove (s: pset) (p: positive) : pset := PositiveSet.remove p s.

Definition sunion (s1 s2: pset) : pset := PositiveSet.union s1 s2.

Notation sempty := PositiveSet.empty.