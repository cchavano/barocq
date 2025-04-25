From Coq Require Import PArith ZArith String DecimalString List MSetPositive.
From compcert Require Import AST Ctypesdefs Maps Integers.
From BarocqComp Require Import Error Monads.
Import MonCounter.
Import MonCounterErr.
Import ListNotations.

(** * Identifiers *)

Definition ident : Type := AST.ident.

Definition ident_eq_dec := Pos.eq_dec.

Definition prefix_ident (p: string) (x: ident) : ident :=
  let sx := string_of_ident x in
  let sx' := (p ++ sx)%string in
  ident_of_string sx'.

Definition transl_user_ident (x: ident) : ident :=
  prefix_ident "u_" x.

Definition ident_of_nat (n: nat) : ident :=
  let str := NilEmpty.string_of_uint (Nat.to_uint n) in
  ident_of_string str.

Open Scope state_monad_scope.

Definition fresh_var (prefix: string) : cmon ident :=
  let* ctr := MonCounter.get in
  let var := prefix_ident prefix (ident_of_nat ctr) in
  MonCounter.incr var.

Close Scope state_monad_scope.

Open Scope state_err_monad_scope.

Definition fresh_var_err (prefix: string) : crmon ident :=
  let* ctr := MonCounterErr.get in
  let var := prefix_ident prefix (ident_of_nat ctr) in
  MonCounterErr.incr var.

Close Scope state_err_monad_scope.

(** * Arithmetic *)

Definition uint_to_nat (i: int) : nat :=
  Z.to_nat (Int.unsigned i).

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

(** * Maps *)

Notation ptree := PTree.t.

Definition tget {A: Type} (t: ptree A) (p: positive) : option A := PTree.get p t.

Definition tset {A: Type} (t: ptree A) (p: positive) (x: A) : ptree A := PTree.set p x t.

Notation tempty := PTree.Empty.

(** * Sets *)

Notation pset := PositiveSet.t.

Definition smem (s: pset) (p: positive) : bool := PositiveSet.mem p s.

Definition sadd (s: pset) (p: positive) : pset := PositiveSet.add p s.

Definition sremove (s: pset) (p: positive) : pset := PositiveSet.remove p s.

Notation sempty := PositiveSet.empty.

(** * Decidability *)

Definition eq_dec_bool {A} (eq_dec: forall a b, {a = b} + {a <> b}) (x y: A) : bool :=
  if eq_dec x y then true else false.