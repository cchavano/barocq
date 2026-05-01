(** Some usual primitives to build OrderedType.
    In particular, we provide a [list_compare] which uses less hypotheses than Stdlib
 *)
From Stdlib Require Import List Lia.

Definition pair_compare {A B:Type} (cmp1 : A -> A -> comparison)
  (cmp2 : B -> B -> comparison) (e1 e2:A * B) : comparison :=
  match cmp1 (fst e1) (fst e2) with
  | Eq => cmp2 (snd e1) (snd e2)
  | Lt => Lt
  | Gt => Gt
  end.


From Stdlib Require String.
Lemma ascii_compare_refl : forall (a:Ascii.ascii),
    Ascii.compare a a = Eq.
Proof.
  unfold Ascii.compare.
  intros.
  apply BinNat.N.compare_refl.
Qed.

Lemma string_compare_refl : forall s,
    String.compare s s = Eq.
Proof.
  induction s ; simpl; auto.
  rewrite IHs.
  rewrite ascii_compare_refl.
  reflexivity.
Qed.

Lemma string_compare_eq_iff : forall s1 s2,
    String.compare s1 s2 = Eq <-> s1 = s2.
Proof.
  split; intros.
  - apply String.compare_eq_iff. auto.
  - subst.
    apply string_compare_refl.
Qed.

Lemma pair_compare_trans :
  forall {A B: Type} (cmp1 : A -> A -> comparison) (cmp2 : B -> B -> comparison)
         (CMPEQ : forall a b, cmp1 a b = Eq -> a = b),
  forall a1 b1 a2 b2 a3 b3
         (TR1 : forall c, cmp1 a1 a2 = c -> cmp1 a2 a3 = c -> cmp1 a1 a3 = c)
         (TR2 : forall c, cmp2 b1 b2 = c -> cmp2 b2 b3 = c -> cmp2 b1 b3 = c)
  ,
  forall c, pair_compare cmp1 cmp2 (a1,b1) (a2,b2) = c ->
            pair_compare cmp1 cmp2 (a2,b2) (a3,b3) = c ->
            pair_compare cmp1 cmp2 (a1,b1) (a3,b3) = c.
Proof.
  unfold pair_compare. simpl; intros.
  destruct (cmp1 a1 a2) eqn:A1A2.
  { apply CMPEQ in A1A2.
    subst.
    destruct (cmp1 a2 a3) eqn:A2A3;auto.
  }
  destruct (cmp1 a2 a3) eqn:A2A3; try discriminate ; auto.
  {
    apply CMPEQ in A2A3.
    subst.
    rewrite A1A2. auto.
  }
  {
    rewrite (TR1 Lt); auto.
  }
  congruence.
  destruct (cmp1 a2 a3) eqn:A2A3; try discriminate ; auto.
  {
    apply CMPEQ in A2A3.
    subst.
    rewrite A1A2. auto.
  }
  congruence.
  rewrite (TR1 Gt);auto.
Qed.

Lemma pair_compare_eq : forall {A B: Type}
                               (cmp1 : A -> A -> comparison)
                               (cmp2 : B -> B -> comparison),
  forall x1 y1 x2 y2,
    (cmp1 x1 y1 = Eq <-> x1 = y1) ->
    (cmp2 x2 y2 = Eq <-> x2 = y2) ->
    pair_compare cmp1 cmp2 (x1,x2) (y1,y2) = Eq <-> (x1,x2) = (y1,y2).
Proof.
  intros.
  unfold pair_compare.
  simpl.
  split; intros.
  destruct (cmp1 x1 y1);
    destruct (cmp2 x2 y2); intuition try congruence.
  injection H1. intros; subst.
  destruct (cmp1 y1 y1);
    destruct (cmp2 y2 y2); intuition try congruence.
Defined.

Section LISTCOMPARE.
  Context {A: Type}.
  Variable cmp : A -> A -> comparison.

  Fixpoint list_compare_eq (l1 l2: list A) :
    (forall x y, In x l1 -> cmp x y = Eq <-> x = y) ->
    list_compare cmp l1 l2 = Eq <-> l1 = l2.
  Proof.
    destruct l1.
    - simpl.
      destruct l2. tauto.
      intuition congruence.
    - destruct l2;simpl.
      intuition congruence.
      intros.
      generalize (H a a0 (or_introl Logic.eq_refl)).
      destruct (cmp a a0).
      rewrite list_compare_eq. intuition congruence.
      intros.
      apply H. tauto.
      intuition try congruence.
      injection H0 ; intuition congruence.
      intuition try congruence.
      injection H0 ; intuition congruence.
  Defined.

End LISTCOMPARE.

Lemma string_compare_trans :
  forall (x y z : String.string) (c : comparison), String.compare x y = c -> String.compare y z = c -> String.compare x z = c.
Proof.
  intro.
  induction x.
  - destruct y,z; simpl; try discriminate; congruence.
  - simpl.
    destruct y,z; simpl; try discriminate; try congruence.
    apply pair_compare_trans.
    {
      unfold Ascii.compare.
      intros.
      apply BinNat.N.compare_eq in H.
      rewrite <- (Ascii.ascii_N_embedding a2).
      rewrite <- (Ascii.ascii_N_embedding b).
      congruence.
    }
    {
      unfold Ascii.compare.
      destruct c.
      intros.
      apply BinNat.N.compare_eq in H.
      apply BinNat.N.compare_eq in H0.
      rewrite H. rewrite H0.
      apply BinNat.N.compare_refl.
      intros.
      rewrite BinNat.N.compare_lt_iff in *.
      lia.
      intros.
      rewrite BinNat.N.compare_gt_iff in *.
      lia.
    }
    apply IHx.
Qed.

Lemma list_compare_trans :  forall (A : Type) (cmp : A -> A -> comparison),
    (forall x y : A, cmp x y = Eq <-> x = y) ->
    forall (xs ys zs : list A) (c : comparison),
      (forall (x y z : A) (c0 : comparison), In x xs -> In y ys -> In z zs -> cmp x y = c0 -> cmp y z = c0 -> cmp x z = c0) ->
      list_compare cmp xs ys = c -> list_compare cmp ys zs = c -> list_compare cmp xs zs = c.
Proof.
  induction xs ; destruct ys,zs; simpl; try congruence.
  intros.
  destruct (cmp a a0) eqn:AA0.
  destruct (cmp a0 a1) eqn:A0A1.
  {assert (cmp a a1 = Eq).
   { eapply H0. tauto.
     left ; tauto. left. tauto.
     auto. auto.
   }
   rewrite H3.
   revert H1 H2.
   apply IHxs.
   intros x y z c' I1 I2 I3.
   apply H0.
   tauto. right ; apply I2.
   tauto.
  }
  { subst.
    rewrite H in AA0.
    subst.
    rewrite A0A1.
    auto.
  }
  {subst.
   rewrite H in AA0.
   subst.
   rewrite A0A1.
   auto.
  }
  destruct (cmp a0 a1) eqn:A0A1.
  { rewrite H in A0A1.
    subst.
    rewrite AA0. auto.
  }
  {
    subst.
    rewrite H0 with (y:=a0) (c0:=Lt);auto.
  }
  {
    congruence.
  }
  destruct (cmp a0 a1) eqn:A0A1.
  { rewrite H in A0A1.
    subst.
    rewrite AA0. auto.
  }
  {
    subst.
    discriminate.
  }
  {
    subst.
    rewrite H0 with (y:=a0) (c0:=Gt);auto.
  }
Qed.

Lemma pair_compare_antisym :
  forall {A B: Type} (cmp1 : A -> A -> comparison) (cmp2 : B -> B -> comparison),
  forall x y
         (CMP1 : cmp1 (fst x) (fst y) = CompOpp (cmp1 (fst y) (fst x)))
         (CMP2 : cmp2 (snd x) (snd y) = CompOpp (cmp2 (snd y) (snd x))),
    pair_compare cmp1 cmp2 x y =
      CompOpp (pair_compare cmp1 cmp2 y x).
Proof.
  destruct x,y; simpl.
  unfold pair_compare; simpl.
  intros.
  rewrite CMP1.
  destruct (cmp1 a0 a) ; try discriminate.
  simpl. apply CMP2.
  reflexivity.
  reflexivity.
Qed.

Lemma list_compare_antisym :
  forall (A : Type) (cmp : A -> A -> comparison),
    (forall x y : A, cmp x y = Eq <-> x = y) ->
    forall xs ys : list A,
      (forall x y : A, In y ys -> In x xs -> cmp y x = CompOpp (cmp x y)) ->
      list_compare cmp ys xs = CompOpp (list_compare cmp xs ys).
Proof.
  induction xs; destruct ys ; simpl; try tauto.
  intros.
  rewrite H0 by tauto.
  destruct (cmp a a0).
  simpl. apply IHxs. intros. apply H0;auto.
  simpl. reflexivity.
  reflexivity.
Qed.