(** Some usual primitives to build OrderedType.
    In particular, we provide a [list_compare] which uses less hypotheses than Stdlib
 *)
From Stdlib Require Import Bool List Lia.
From Stdlib Require Import Structures.OrderedType.
From BarocqComp Require Import Utils0.

Definition comparison_of_Compare
{A: Type} {lt: A -> A -> Prop} {eq: A -> A -> Prop}
  {x y: A} (c: Compare lt eq x y) : comparison :=
    match c with
    | EQ _ => Eq
    | LT _ => Lt
    | GT _ => Gt
    end.

Definition compare_of_compare {A: Type} {lt: A -> A -> Prop} {eq: A -> A -> Prop}
  (c: forall x y, Compare lt eq x y) : A -> A -> comparison :=
  fun x y => comparison_of_Compare (c x y).

Lemma compare_of_compare_antisym : forall {A: Type} {lt: A -> A -> Prop} {eq: A -> A -> Prop}
  (cmp: forall x y, Compare lt eq x y)
  (EQREFL  : forall x, eq x x)
  (EQSYM  : forall x y, eq x y -> eq y x)
  (LTNOTEQ : forall x y, lt x y -> not (eq x y))
    (LTTRANS : forall x y z, lt x y -> lt y z -> lt x z),
    forall x y,
    ExtOrdered.compare_of_compare cmp  x y =
    CompOpp (ExtOrdered.compare_of_compare cmp y x).
Proof.
  unfold compare_of_compare.
  unfold comparison_of_Compare.
  intros. destruct (cmp x y).
  destruct (cmp y x) ; auto.
  { exfalso.
    eapply (LTNOTEQ x).
    eapply LTTRANS;eauto.
    apply EQREFL.
  }
  { exfalso.
    eapply (LTNOTEQ x y); auto.
  }
  {
    apply EQSYM in e.
    destruct (cmp y x); auto.
    - exfalso.
      eapply (LTNOTEQ y x); auto.
    - exfalso.
      eapply (LTNOTEQ x y); auto.
  }
  destruct (cmp y x); auto.
  {
    exfalso.
    eapply (LTNOTEQ y x); auto.
  }
  {
    exfalso.
    eapply (LTNOTEQ x x); auto.
    eapply LTTRANS;eauto.
  }
Qed.

Lemma compare_of_compare_eq :
  forall {A: Type}
         {eq: A -> A -> Prop}
         {lt: A -> A -> Prop}
         (compare : forall (x y:A), Compare lt eq x y)
         (eq_eq : forall x y, eq x y <-> x = y)
         (lt_not_eq : forall x y, lt x y -> ~ eq x y),
  forall x y,
    compare_of_compare compare x y = Eq <-> x = y.
Proof.
  intros.
  unfold compare_of_compare.
  destruct (compare x y); simpl; try (intuition congruence).
  apply lt_not_eq in l.
  rewrite eq_eq in l. intuition congruence.
  rewrite eq_eq in e. intuition congruence.
  apply lt_not_eq in l.
  rewrite eq_eq in l.
  intuition congruence.
Qed.

Lemma compare_of_compare_trans :
  forall {A: Type}
         {eq: A -> A -> Prop}
         {lt: A -> A -> Prop}
         (compare : forall (x y:A), Compare lt eq x y)
         (eq_eq : forall x y, eq x y <-> x = y)
         (lt_trans : forall x y z, lt x y -> lt y z -> lt x z)
         (lt_not_eq : forall x y, lt x y -> ~ eq x y),
  forall x y z c,
    compare_of_compare compare x y = c -> compare_of_compare compare y z = c ->
    compare_of_compare compare x z = c.
Proof.
  intros.
  unfold compare_of_compare in *.
  unfold comparison_of_Compare in *.
  destruct (compare x y);
    destruct (compare y z);
    destruct (compare x z); subst; auto; try discriminate;
    repeat rewrite eq_eq in *; subst.
  - exfalso. apply (lt_not_eq y y).
    eapply lt_trans;eauto.
    rewrite eq_eq. reflexivity.
  - exfalso. apply (lt_not_eq z z).
    eapply lt_trans;eauto.
    rewrite eq_eq. reflexivity.
  - exfalso. apply (lt_not_eq z z).
    eapply lt_trans;eauto.
    rewrite eq_eq. reflexivity.
  - exfalso. apply (lt_not_eq z z);auto.
    rewrite eq_eq. reflexivity.
  - exfalso. apply (lt_not_eq y y).
    eapply lt_trans;eauto.
    rewrite eq_eq. reflexivity.
  - exfalso. apply (lt_not_eq y y).
    eapply lt_trans;eauto.
    rewrite eq_eq. reflexivity.
Qed.



Definition pair_compare {A B:Type} (cmp1 : A -> A -> comparison)
  (cmp2 : B -> B -> comparison) (e1 e2:A * B) : comparison :=
  match cmp1 (fst e1) (fst e2) with
  | Eq => cmp2 (snd e1) (snd e2)
  | Lt => Lt
  | Gt => Gt
  end.

Definition pair_eqb {A B:Type} (eqb1 : A -> A -> bool)
  (eqb2 : B -> B -> bool) (e1 e2:A * B) : bool :=
  let (x1,x2) := e1 in
  let (y1,y2) := e2 in
  match eqb1 x1 y1 with
  | true => eqb2 x2 y2
  | false => false
  end.

Definition pair_eq_dec {A B:Type} (eqb1 : eqDec A)  (eqb2 : eqDec B) : eqDec (A*B).
Proof.
  intros [x1 x2] [y1 y2].
  destruct (eqb1 x1 y1).
  destruct (eqb2 x2 y2).
  - left. congruence.
  - right; congruence.
  - right. congruence.
Defined.

Definition option_compare {A:Type} (cmp : A -> A -> comparison)
  (e1 e2: option A)  : comparison :=
     match e1, e2 with
     | None , None => Eq
     | None , _    => Lt
     | _    , None => Gt
     | Some v1 , Some v2 => cmp v1 v2
     end.

Definition option_eqb {A:Type} (eqb : A -> A -> bool)
  (e1 e2: option A)  : bool :=
     match e1, e2 with
     | None , None => true
     | Some v1 , Some v2 => eqb v1 v2
     | _ , _ => false
     end.

Lemma option_compare_eqb :
  forall {A: Type} (eqb: A -> A -> bool)
         (cmp: A -> A -> comparison),
         (forall x y, cmp x y = Eq <-> eqb x y = true) ->
         forall x y,
           option_compare cmp x y = Eq <-> option_eqb eqb x y = true.
Proof.
  destruct x,y; simpl; try intuition congruence.
  apply H.
Qed.


Lemma option_compare_eq :
  forall {A: Type} 
         (cmp: A -> A -> comparison),
         (forall x y, cmp x y = Eq <-> x = y) ->
         forall x y,
           option_compare cmp x y = Eq <-> x= y.
Proof.
  destruct x,y; simpl; try intuition congruence.
  rewrite H. intuition congruence.
Qed.

Lemma option_compare_trans :
  forall {A: Type} (cmp : A -> A -> comparison),
  (forall a1 a2 a3 c, cmp a1 a2 = c -> cmp a2 a3 = c -> cmp a1 a3 = c) ->
  forall o1 o2 o3 c, option_compare cmp o1 o2 = c ->
            option_compare cmp o2 o3 = c ->
            option_compare cmp o1 o3 = c.
Proof.
  destruct o1,o2,o3; simpl; intuition; try congruence.
  eapply H; eauto.
Qed.


Lemma option_eqb_eq :
  forall {A: Type} (eqb: A -> A -> bool),
         (forall x y, eqb x y = true <-> x = y) ->
         forall x y,
           option_eqb eqb x y = true <-> x = y.
Proof.
  destruct x,y; simpl; try intuition congruence.
  rewrite H. intuition congruence.
Qed.

Lemma pair_eqb_eq :
  forall {A B: Type} (eqb1: A -> A -> bool)
         (eqb2: B -> B -> bool)
  ,
    forall x y,
      eqb1 (fst x) (fst y) = true <-> (fst x) = (fst y) ->
      eqb2 (snd x) (snd y) = true <-> (snd x) = (snd y) ->
      pair_eqb eqb1 eqb2 x y = true <-> x = y.
Proof.
  destruct x,y; simpl; try intuition congruence.
  intros.
  apply lift_if; intuition try congruence.
  inv H3. intuition congruence.
  inv H0. intuition congruence.
Qed.


From Stdlib Require String.
Lemma ascii_compare_refl : forall (a:Ascii.ascii),
    Ascii.compare a a = Eq.
Proof.
  unfold Ascii.compare.
  intros.
  apply BinNat.N.compare_refl.
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
  forall x y,
    (cmp1 (fst x) (fst y) = Eq <-> fst x = fst y) ->
    (cmp2 (snd x) (snd y) = Eq <-> snd x = snd y) ->
    pair_compare cmp1 cmp2 x y = Eq <-> x = y.
Proof.
  intros.
  unfold pair_compare.
  simpl.
  destruct x as (x1,x2);
    destruct y as (y1,y2); simpl in *.
  destruct (cmp1 x1 y1).
  - intuition try congruence.
    inv H2; intuition congruence.
  - intuition try congruence.
    inv H4; intuition congruence.
  - intuition try congruence.
    inv H4; intuition congruence.
Qed.

Section LIST_LE.
  Context {A: Type}.
  Variable leb : A -> A -> bool.

  Fixpoint list_leb (l1 l2:list A) :=
    match l1 with
    | nil => true
    | e1::l1 => match l2 with
                | nil => false
                | e2::l2 => leb e1 e2 &&  list_leb l1 l2
                end
    end.
End LIST_LE.



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

Definition option_rel_some {A: Type} (R : A -> A -> Prop) (o1 o2:option A) :=
  match o1, o2 with
  | Some v1 , Some v2 => R v1 v2
  | _ , _ => True
  end.



Lemma option_compare_antisym : forall {A: Type}
                                      (cmp : A -> A -> comparison) o1 o2,
    option_rel_some (fun v1 v2 => cmp v1 v2 = CompOpp (cmp v2 v1)) o1 o2 ->
    option_compare cmp o1 o2 = CompOpp (option_compare cmp o2 o1).
Proof.
  destruct o1,o2 ; simpl; auto.
Qed.


Definition eqb_of_compare {A:Type} (cmp : A -> A -> comparison) (x y:A) : bool :=
  match cmp x y with
  | Eq => true
  | _  => false
  end.


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

Module Type OrderedCompare.
  Axiom t : Type.
  Axiom compare : t -> t -> comparison.

  Axiom compare_antisym  : forall x y, compare x y = CompOpp (compare y x).
  Axiom compare_trans : forall x y z c, compare x y = c -> compare y z = c -> compare x z = c.

End OrderedCompare.


Module Type OrderedCompareEq.
  Include OrderedCompare.

  Axiom compare_eq : forall x y, compare x y = Eq <-> x = y.

End OrderedCompareEq.



Module Make(O:OrderedCompare) <: OrderedType.
  Definition t := O.t.
  Definition eq: t -> t -> Prop := fun x y => O.compare x y = Eq.
  Definition lt: t -> t -> Prop := fun x y => O.compare x y = Lt.
  Definition eq_refl : forall x, eq x x.
  Proof.
    unfold eq. intro. specialize (O.compare_antisym x x).
    destruct (O.compare x x); auto.
    discriminate. discriminate.
  Qed.

  Lemma eq_sym   : forall x y, eq x y -> eq y x.
  Proof.
    unfold eq.
    intros.
    rewrite O.compare_antisym. rewrite H. reflexivity.
  Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. intros x y z.
    apply O.compare_trans.
  Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt. intros x y z.
    apply O.compare_trans.
  Qed.


  Lemma lt_not_eq : forall x y, lt x y -> not (eq x y).
  Proof.
    unfold lt,eq. repeat intro.
    congruence.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    unfold lt,eq.
    destruct (O.compare x y) eqn:CMP.
    - apply EQ ;assumption.
    - apply LT ;assumption.
    - apply GT. rewrite O.compare_antisym. rewrite CMP. reflexivity.
  Qed.

  Definition eq_dec : forall (x y:t),{eq x y} + {not (eq x y)}.
  Proof.
    intros.
    unfold eq. destruct (O.compare x y).
    left ; reflexivity.
    right;discriminate.
    right;discriminate.
  Defined.

  Definition eqb (x y:t) :=
    match O.compare x y with
    | Eq => true
    | _  => false
    end.

  Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
  Proof.
    unfold eq,eqb. intros.
    destruct (O.compare x y); intuition congruence.
  Qed.
End Make.



Module MakeEq(O:OrderedCompareEq) <: OrderedType.
  Definition t := O.t.
  Definition eq: t -> t -> Prop := @eq t.
  Definition lt: t -> t -> Prop := fun x y => O.compare x y = Lt.
  Definition eq_refl : forall x, eq x x.
  Proof.
    unfold eq. intro. reflexivity.
  Qed.

  Lemma eq_sym   : forall x y, eq x y -> eq y x.
  Proof.
    unfold eq. congruence.
  Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. congruence.
  Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt. intros x y z.
    apply O.compare_trans.
  Qed.


  Lemma lt_not_eq : forall x y, lt x y -> not (eq x y).
  Proof.
    unfold lt,eq. repeat intro.
    rewrite <- O.compare_eq in H0.
    congruence.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    unfold lt,eq.
    destruct (O.compare x y) eqn:CMP.
    - rewrite O.compare_eq in CMP.
      apply EQ ;assumption.
    - apply LT ;assumption.
    - apply GT. rewrite O.compare_antisym. rewrite CMP. reflexivity.
  Qed.

  Definition eq_dec : forall (x y:t),{eq x y} + {not (eq x y)}.
  Proof.
    intros.
    unfold eq. destruct (O.compare x y) eqn:CMP.
    - rewrite O.compare_eq in CMP. left; assumption.
    - right; intro. rewrite <- O.compare_eq in H. congruence.
    - right; intro. rewrite <- O.compare_eq in H. congruence.
  Defined.

  Definition eqb (x y:t) :=
    match O.compare x y with
    | Eq => true
    | _  => false
    end.

  Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
  Proof.
    unfold eq,eqb. intros.
    destruct (O.compare x y) eqn:CMP; try intuition congruence.
    rewrite O.compare_eq in CMP. tauto.
    rewrite <- O.compare_eq. intuition congruence.
    rewrite <- O.compare_eq. intuition congruence.
  Qed.
End MakeEq.



Lemma string_compare_refl : forall s,
    String.compare s s = Eq.
Proof.
  induction s ; simpl; auto.
  rewrite IHs.
  rewrite ascii_compare_refl.
  reflexivity.
Qed.

Lemma string_compare_eq : forall s1 s2,
    String.compare s1 s2 = Eq <-> s1 = s2.
Proof.
  split; intros.
  - apply String.compare_eq_iff. auto.
  - subst.
    apply string_compare_refl.
Qed.

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

Module Str <: OrderedCompare.
  Import String.
  Definition t := string.
  Definition compare := String.compare.
  Definition compare_antisym := String.compare_antisym.
  Definition compare_trans   := string_compare_trans.
  Definition compare_eq := string_compare_eq.
End Str.

Module OString := MakeEq(Str). (* An ordered type using equality *)
