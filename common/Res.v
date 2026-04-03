(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Error reporting and the error monad. *)

From Stdlib Require Import String RelationClasses.
From compcert Require Import Coqlib.

Close Scope string_scope.

Set Implicit Arguments.

(** * Representation of error messages. *)

(** Compile-time errors produce an error message, represented in Coq
  as a list of either substrings or positive numbers encoding
  a source-level identifier (see module AST). *)

Inductive errcode: Type :=
  | MSG: string -> errcode
  | CTX: positive -> errcode    (* a top-level identifier *)
  | POS: positive -> errcode.   (* a positive integer, e.g. a PC *)

Definition errmsg: Type := list errcode.

Definition msg (s: string) : errmsg := MSG s :: nil.

(** * The error monad *)

(** Compilation functions that can fail have return type [res A].
  The return value is either [OK res] to indicate success,
  or [Error msg] to indicate failure. *)

Inductive res (A: Type) : Type :=
| OK: A -> res A
| Error: errmsg -> res A.

Arguments Error [A].

Definition isOK {A: Type} (v: res A) : Prop :=
  exists x, v = OK x.

Definition isError {A: Type} (v: res A) : Prop :=
  exists e, v = Error e.

Lemma isOK_Error : forall {A: Type} (v : res A),
    isOK v -> forall e, v = Error e -> False.
Proof.
  unfold isOK.
  intros. destruct H. congruence.
Qed.

Definition eret {A: Type} (a: A) : res A := OK a.

Definition efail {A: Type} : res A := Error nil.

Definition efailwith {A: Type} (m: string) : res A := Error (msg m).

(** To automate the propagation of errors, we use a monadic style
  with the following [bind] operation. *)

Definition bind (A B: Type) (f: res A) (g: A -> res B) : res B :=
  match f with
  | OK x => g x
  | Error msg => Error msg
  end.

Definition bind2 (A B C: Type) (f: res (A * B)) (g: A -> B -> res C) : res C :=
  match f with
  | OK (x, y) => g x y
  | Error msg => Error msg
  end.

Definition bind_catch {A B: Type} (f: res A) (g: A -> res B) (h: res B) : res B :=
  match f with
  | OK a => g a
  | Error _ => h
  end. 

Definition of_opt {A: Type} (o: option A) : res A :=
  match o with
  | Some v => OK v
  | None => efail
  end.

Remark ok_imp_some:
  forall (A: Type) (o: option A) (v: A),
  of_opt o = OK v ->
  o = Some v.
Proof.
  unfold of_opt; intros.
  destruct o; try discriminate.
  congruence.
Qed.

(** The [do] notation, inspired by Haskell's, keeps the code readable. *)

Declare Scope error_monad_scope.
Delimit Scope error_monad_scope with error_monad.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X name, A at level 100, B at level 200)
  : error_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : error_monad_scope.

Notation "'do' ( X , Y , Z ) <- A ; B" := (bind2 A (fun '(X, Y) Z => B))
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : error_monad_scope.

Notation "'do' ( X , Y , Z , W ) <- A ; B" := (bind2 A (fun '(X, Y, Z) W => B))
  (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
  : error_monad_scope.

Notation "do/c X <- A '/>' M ; B" := (bind_catch A (fun X => B) M)
  (at level 200, X name, A at level 100, M at level 100, B at level 200)
  : error_monad_scope.

Remark bind_inversion:
  forall (A B: Type) (f: res A) (g: A -> res B) (y: B),
  bind f g = OK y ->
  exists x, f = OK x /\ g x = OK y.
Proof.
  intros until y. destruct f; simpl; intros.
  exists a; auto.
  discriminate.
Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: res (A*B)) (g: A -> B -> res C) (z: C),
  bind2 f g = OK z ->
  exists x, exists y, f = OK (x, y) /\ g x y = OK z.
Proof.
  intros until z. destruct f; simpl.
  destruct p; simpl; intros. exists a; exists b; auto.
  intros; discriminate.
Qed.

(** Assertions *)

Definition assertion_failed {A: Type} : res A := Error(msg "Assertion failed").

Notation "'assertion' A ; B" := (if A then B else assertion_failed)
  (at level 200, A at level 100, B at level 200)
  : error_monad_scope.

(** This is the familiar monadic map iterator. *)

Local Open Scope error_monad_scope.

Section mmap.
  Context (A B: Type).
  Variable (f: A -> res B).

  Fixpoint mmap (l: list A) {struct l} : res (list B) :=
    match l with
    | nil => OK nil
    | hd :: tl => do hd' <- f hd; do tl' <- mmap tl; OK (hd' :: tl')
    end.

  Remark mmap_inversion:
    forall (l: list A) (l': list B),
      mmap l = OK l' ->
      list_forall2 (fun x y => f x = OK y) l l'.
  Proof.
    induction l; simpl; intros.
    inversion_clear H. constructor.
    destruct (bind_inversion _ _ H) as [hd' [P Q]].
    destruct (bind_inversion _ _ Q) as [tl' [R S]].
    inversion_clear S.
    constructor. auto. auto.
  Qed.
End mmap.

Definition res_pred {A : Type} (P : A -> Prop) (r:res A) :=
  match r with
  | OK a => P a
  | Error _ => True
  end.

(** * Relation on errors *)

Inductive res_rel {A B : Type} (R : A -> B -> Prop) : res A -> res B -> Prop :=
  res_rel_error : forall m, res_rel R (Error m) (Error m)
| res_rel_ok : forall (x : A) (y : B), R x y -> res_rel R (OK x) (OK y).

Lemma res_rel_trans : forall {A : Type} (R: A -> A -> Prop),
    Transitive R -> Transitive (res_rel R).
Proof.
  repeat intro.
  inv H0;inv H1; try constructor.
  eapply H; eauto.
Qed.

Lemma res_rel_sym : forall {A : Type} (R: A -> A -> Prop),
    Symmetric R -> Symmetric (res_rel R).
Proof.
  repeat intro.
  inv H0; try constructor.
  apply H; eauto.
Qed.

Lemma res_rel_refl : forall {A : Type} (R: A -> A -> Prop),
    Reflexive R -> Reflexive (res_rel R).
Proof.
  repeat intro.
  destruct x. constructor; auto.
  constructor.
Qed.

Lemma res_eq_dec (T: Type) (eq_dec : forall (x y: T), {x = y} + { x <> y})
                  (x y: res T) : {x = y} + {x <> y}.
Proof.
  decide equality.
  apply list_eq_dec.
  decide equality.
  apply string_dec.
  apply Pos.eq_dec.
  apply Pos.eq_dec.
Qed.

Lemma option_rel_res_rel : forall {A: Type} (R : A -> A -> Prop) v1 v2,
  option_rel R v1 v2 ->
  res_rel R (of_opt v1) (of_opt v2).
Proof.
  intros. inv H; simpl; constructor;auto.
Qed.

(** * Reasoning over monadic computations *)

(** The [monadInv H] tactic below simplifies hypotheses of the form
<<
        H: (do x <- a; b) = OK res
>>
    By definition of the bind operation, both computations [a] and
    [b] must succeed for their composition to succeed.  The tactic
    therefore generates the following hypotheses:

         x: ...
        H1: a = OK x
        H2: b x = OK res
*)

Ltac monadInv1 H :=
  match type of H with
  | (OK _ = OK _) =>
      inversion H; clear H; try subst
  | (Error _ = OK _) =>
      discriminate
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInv1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInv1 EQ2)))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
      destruct X; [try (monadInv1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; simpl negb in H; [discriminate | try (monadInv1 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [try (monadInv1 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  end.

Ltac monadInv H :=
  monadInv1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.
