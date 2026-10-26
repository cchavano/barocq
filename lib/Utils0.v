From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Ctypesdefs Maps Integers.

Lemma elim_if : forall {A: Type} (c:bool) (e1 e1' e2 e2':A),
  e1 = e1' -> e2 = e2' ->
  (if c then e1 else e2) = (if c then e1' else e2').
Proof.
  destruct c; auto.
Qed.

Lemma lift_if : forall {A:Type} (P : A -> Prop) (c:bool) (e1 e2:A),
    (c = true -> P e1) -> (c = false -> P e2) ->
    P (if c then e1 else e2).
Proof.
  destruct c;
    intuition congruence.
Qed.

Definition eqDec (A: Type) := forall (x y: A),{x=y}+{x<>y}.


Polymorphic Definition cast {A B: Type} (EQ : A = B) (v: A) : B.
  rewrite EQ in v. exact v.
Defined.

Lemma cast_ok_imp_eq:
  forall (A B: Type) (EQ: A = B) (v: A) (v': B),
  @cast A B EQ v = v' ->
  A = B.
Proof.
  tauto.
Qed.

(*Inductive Forall2In {A B: Type} (P : A -> B -> Prop) : list A -> list B -> Prop :=*)



Lemma Forall2_gen : forall {A B:Type} (P : A -> B -> Prop),
  (forall x y, P x y) -> forall l1 l2, length l1 = length l2 -> Forall2 P l1 l2.
Proof.
  induction l1; destruct l2; try discriminate.
  - constructor.
  - constructor. apply H.
    apply IHl1. inv H0;reflexivity.
Qed.

(** Given a goal of the form [Forall P l], instead of doing [repeat Forall_cons] (slow),
    do [apply Forall_app_sound]  (fast) *)

(* [Forall_app [l1;...;ln] G] generates the formula P l1 -> ... -> P ln -> G *)
Fixpoint Forall_app {A: Type} (P : A -> Prop) (l:list A) (G:Prop) {struct l} :=
  match l with
  | nil => G
  | e::l' => P e -> (Forall_app P l' G)
  end.

Lemma Forall_app_Forall : forall {A: Type} (P : A -> Prop) l G,
    (Forall P l -> G) ->  Forall_app P l G.
Proof.
  induction l; simpl;auto.
Qed.

Lemma Forall_app_sound : forall {A: Type} (P: A -> Prop) l,
    Forall_app P l (Forall P l).
Proof.
  intros.
  apply Forall_app_Forall.
  auto.
Qed.

Section S.
  (** is-it already defined elsewhere? *)
  Context {A B: Type}.
  Variable f : A -> B -> bool.

  Fixpoint forall2b  (l1: list A) (l2: list B) {struct l1} : bool :=
    match l1 , l2 with
  | nil , nil => true
  | e1::l1, e2::l2 => if f e1 e2 then forall2b l1 l2 else false
  | _ , _ => false
  end.

End S.

Lemma forall2b_eqb_eq : forall {A: Type}
                            (eqb:A -> A -> bool),
  forall l1 l2,
  (forall x y, In x l1 -> In y l2 -> eqb x y = true <-> x = y) ->
    forall2b eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1; destruct l2; simpl; try intuition congruence.
  intros.
  apply lift_if.
  - intros.
    rewrite IHl1. intuition try congruence.
    f_equal;auto.
    apply H ; try tauto.
    intros. apply H. tauto.
    tauto.
  - intuition try congruence.
    inv H1. specialize (H a0 a0); intuition congruence.
Qed.



(* Tactics *)

Ltac destruct_conj H :=
  match type of H with
  | _ && _ = _ =>
      apply andb_prop in H;
      destruct_conj H
  | _ /\ _ =>
      let c1 := fresh "C" in
      let c2 := fresh "C" in
      destruct H as [c1 c2];
      destruct_conj c1;
      destruct_conj c2
  | _ => idtac
  end.

Ltac inv H := Coqlib.inv H.

Ltac rew H :=
  match type of H with
  | ?A = _ => destruct A ; try discriminate ; inv H
  end.
