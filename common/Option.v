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

(** Option monad. *)

From Stdlib Require Import String RelationClasses.
From compcert Require Import Coqlib.
Import ListNotations.
Close Scope string_scope.

Set Implicit Arguments.

(** * The option monad *)

Definition ret {A: Type} (v: A) : option A := Some v.

Definition fail {A: Type} : option A := None.

Definition isSome {A: Type} (v: option A) := exists x, v = Some x.

Lemma isSome_None : forall {A: Type} (v:option A), isSome v <-> (v <> None).
Proof.
  unfold isSome.
  split ; intros.
  destruct H. congruence.
  destruct v. exists a; auto.
  congruence.
Qed.

Definition bind (A B: Type) (f: option A) (g: A -> option B) : option B :=
  match f with
  | Some x => g x
  | None => None
  end.

Definition bind2 (A B C: Type) (f: option (A * B)) (g: A -> B -> option C) : option C :=
  match f with
  | Some (x, y) => g x y
  | None => None
  end.

(** The [let*] notation keeps the code readable. *)

Declare Scope option_monad_scope.
Delimit Scope option_monad_scope with option_monad.

Notation "'let*' X := A 'in' B" := (bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200)
    : option_monad_scope.

Notation "'let*' ( X , Y ) := A 'in' B" := (bind2 A (fun X Y => B))
    (at level 200, X name, Y name, A at level 100, B at level 200)
    : option_monad_scope.

Notation "'let*' ( X , Y , Z ) := A 'in' B" := (bind2 A (fun '(X, Y) Z => B))
    (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
    : option_monad_scope.

Notation "'let*' ( X , Y , Z , W ) := A 'in' B" := (bind2 A (fun '(X, Y, Z) W => B))
    (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
    : option_monad_scope.

Remark bind_inversion:
  forall (A B: Type) (f: option A) (g: A -> option B) (y: B),
  bind f g = Some y ->
  exists x, f = Some x /\ g x = Some y.
Proof.
  intros until y. destruct f; simpl; intros.
  exists a; auto.
  discriminate.
Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: option (A*B)) (g: A -> B -> option C) (z: C),
  bind2 f g = Some z ->
  exists x, exists y, f = Some (x, y) /\ g x y = Some z.
Proof.
  intros until z. destruct f; simpl.
  destruct p; simpl; intros. exists a; exists b; auto.
  intros; discriminate.
Qed.

Local Open Scope option_monad_scope.

Lemma assoc_bind : forall {A B C: Type}
                          (e1 : option A)
                          (e2 : A -> option B)
                          (e3 : B -> option C),
    (let* x := (let* y := e1 in e2 y) in e3 x) =
      (let* y := e1 in let* x := e2 y in e3 x).
Proof.
  intros.
  destruct e1.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma bind_equal : forall {A B:Type} (e1:option A) (e2 e2': A -> option B),
    (forall x, e1 = Some x -> e2 x = e2' x) ->
    (let* x := e1 in e2 x) =
    (let* x := e1 in e2' x).
Proof.
  intros.
  destruct e1 ;auto.
  simpl. apply H; auto.
Qed.

Lemma bind_ret : forall {A B:Type} (e:A) (f: A -> option B),
    bind (ret e) f = f e.
Proof.
  reflexivity.
Qed.

Lemma bind_if : forall {A B: Type} (c:bool) (e1 e2:option A) (e3: A -> option B),
    bind (if c then e1 else e2) e3 = if c then (bind e1 e3) else (bind e2 e3).
Proof.
  destruct c; reflexivity.
Qed.

(** Assertions *)

(** This is the familiar monadic map iterator. *)

Section mmap.
  Context (A B: Type).
  Variable (f: A -> option B).

  Fixpoint mmap (l: list A) {struct l} : option (list B) :=
    match l with
    | nil => Some nil
    | hd :: tl => let* hd' := f hd in let* tl' := mmap tl in Some (hd' :: tl')
    end.

  Remark mmap_inversion:
    forall (l: list A) (l': list B),
      mmap l = Some l' ->
      list_forall2 (fun x y => f x = Some y) l l'.
  Proof.
    induction l; simpl; intros.
    inversion_clear H. constructor.
    destruct (bind_inversion _ _ H) as [hd' [P Q]].
    destruct (bind_inversion _ _ Q) as [tl' [R S]].
    inversion_clear S.
    constructor. auto. auto.
  Qed.
End mmap.

Section FOLD.
  Context {A B: Type}.
  Variable f : A -> B -> option A.

  Fixpoint fold_left_err (l:list B) (a:A) {struct l} : option A :=
  match l with
  | [] => Some a
  | x :: l' => let* acc :=(f a x) in fold_left_err l' acc
  end.

End FOLD.

Section ASSOC.

  Section MMAPASSOC.
    Context {K V A:Type}.
    Variable F : V -> option A.
    Definition mmap_assoc (l: list (K * V)) := mmap (fun x => let* v := F (snd x) in Some (fst x,v)) l.

  End MMAPASSOC.

  Section FINDERR.
    Context {K V: Type}.
    Variable key_eq : forall (k1 k2:K), {k1 = k2} + {k1 <> k2}.

    Fixpoint find_err (k: K) (l: list (K * V)) : option V :=
      match l with
      | nil => fail
      | (x, v) :: l' =>
          if key_eq x k then ret v
          else find_err k l'
      end.

  End FINDERR.

End ASSOC.

Lemma option_rel_trans : forall {A : Type} (R: A -> A -> Prop),
    Transitive R -> Transitive (option_rel R).
Proof.
  repeat intro.
  inv H0;inv H1; try constructor.
  eapply H; eauto.
Qed.

Lemma option_rel_sym : forall {A : Type} (R: A -> A -> Prop),
  Symmetric R -> Symmetric (option_rel R).
Proof.
  repeat intro.
  inv H0; try constructor.
  apply H; eauto.
Qed.

Lemma option_rel_refl : forall {A : Type} (R: A -> A -> Prop),
  Reflexive R -> Reflexive (option_rel R).
Proof.
  repeat intro.
  destruct x. constructor; auto.
  constructor.
Qed.

Lemma option_eq_dec (T: Type) (eq_dec : forall (x y: T), {x = y} + { x <> y})
                  (x y: option T) : {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

(** * Reasoning over monadic computations *)

(** The [monadInv H] tactic below simplifies hypotheses of the form
<<
        H: (let* x := a in b) = Some res
>>
    By definition of the bind operation, both computations [a] and
    [b] must succeed for their composition to succeed.  The tactic
    therefore generates the following hypotheses:

         x: ...
        H1: a = Some x
        H2: b x = Some res
*)

Ltac monadInv1 H :=
  match type of H with
  | (Some _ = Some _) =>
      inversion H; clear H; try subst
  | (None = Some _) =>
      discriminate
  | (bind ?F ?G = Some ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInv1 EQ2))))
  | (bind2 ?F ?G = Some ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInv1 EQ2)))))
(*  | (match ?X with left _ => _ | right _ => assertion_failed end = Some _) =>
      destruct X; [try (monadInv1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = Some _) =>
      destruct X as [] eqn:?; simpl negb in H; [discriminate | try (monadInv1 H)]
  | (match ?X with true => _ | false => assertion_failed end = Some _) =>
      destruct X as [] eqn:?; [try (monadInv1 H) | discriminate] *)
  | (mmap ?F ?L = Some ?M) =>
      generalize (mmap_inversion F L H); intro
  end.

Ltac monadInv H :=
  monadInv1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.
