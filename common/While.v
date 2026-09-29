(**  [while] combinator
 *)
From Stdlib Require Import List.
From compcert Require Import Coqlib.
From BarocqComp Require Import Option.
From Stdlib Require Import FunctionalExtensionality.
Open Scope option_monad_scope.

(** [while] is used by the barocq semantics *)
Fixpoint while {A: Type} (C : A -> option bool) (B : A -> option A) (fuel:nat) (le:A)  : option A :=
    let* b:= C le in
    if b
    then
      let* le' := B le in
      match fuel with
      | O => None (* Not enough fuel *)
      | S fuel' => while C B fuel' le'
      end
    else Some le.

Lemma while_rel : forall {A: Type} (P: A -> A -> Prop) (C1 C2 : A -> option bool) (B1 B2: A -> option A) (fuel: nat) (I1 I2:A),
    P I1 I2 ->
    (forall i1 i2, P i1 i2 -> C1 i1 = C2 i2) ->
    (forall i1 i2, P i1 i2 -> option_rel P (B1 i1) (B2 i2)) ->
    option_rel P (while  C1 B1 fuel I1) (while C2 B2 fuel I2).
Proof.
  induction fuel.
  - simpl. intros.
    apply option_rel_bind_rel with (RA:= @eq _).
    rewrite (H0 _ _ H).
    destruct (C2 I2); constructor. reflexivity.
    intros. subst.
    destruct y.
    apply option_rel_bind_rel with (RA:= P).
    apply H1; auto.
    constructor.
    constructor;auto.
  - intros.
    simpl.
    apply option_rel_bind_rel with (RA:= @eq _).
    rewrite (H0 _ _ H).
    destruct (C2 I2); constructor. reflexivity.
    intros. subst.
    destruct y.
    apply option_rel_bind_rel with (RA:= P).
    apply H1; auto.
    auto.
    constructor;auto.
Qed.


Lemma less_def_while : forall {A: Type}  (C1 C2 : A -> option bool) (B1 B2: A -> option A) (fuel: nat) (I1:A),
    (forall i1, less_def (C1 i1) (C2 i1)) ->
    (forall i1, less_def (B1 i1) (B2 i1)) ->
    less_def (while  C1 B1 fuel I1) (while C2 B2 fuel I1).
Proof.
  induction fuel.
  - simpl. intros.
    apply less_def_bind_less_def.
    apply H.
    destruct x.
    apply less_def_bind_less_def.
    apply H0; auto.
    constructor.
    constructor.
  - intros.
    simpl.
    apply less_def_bind_less_def.
    apply H.
    destruct x.
    apply less_def_bind_less_def.
    apply H0; auto.
    auto.
    constructor;auto.
Qed.

Lemma less_def_with_while : forall {A: Type}  P (C1 C2 : A -> option bool) (B1 B2: A -> option A) (fuel: nat) (I1 I2:A),
    (forall i1 i2, P i1 i2 -> less_def (C1 i1) (C2 i2)) ->
    (forall i1 i2, P i1 i2 -> less_def_with P (B1 i1) (B2 i2)) ->
    P I1 I2 ->
    less_def_with P (while  C1 B1 fuel I1) (while C2 B2 fuel I2).
Proof.
  induction fuel.
  - simpl. intros.
    specialize (H _ _ H1).
    inv H.
    + simpl. constructor.
    + destruct (C1 I1); simpl; try constructor.
      destruct b; try constructor; auto.
      specialize (H0 _ _ H1).
      inv H0; constructor.
  - intros.
    simpl.
    pose proof (H _ _ H1) as HC.
    inv HC.
    + simpl. constructor.
    + destruct (C1 I1); simpl; try constructor.
      destruct b; try constructor; auto.
      pose proof (H0 _ _ H1) as HB.
      inv HB.
      constructor.
      simpl.
      apply IHfuel;auto.
Qed.
