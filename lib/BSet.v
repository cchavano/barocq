(** Boolean sets *)
From Stdlib Require Import Bool List Btauto.

Section S.
  Context {A: Type}.

  Definition t := A -> bool.

  Variable eq_dec : forall (x y: A), {x = y} + {x <> y}.

  Definition bot : t :=  fun x => false.

  Definition top : t :=  fun x => true.

  Definition singleton (e:A) : t := fun x => if eq_dec x e then true else false.

  Definition union (s1 s2:t) := fun x => s1 x || s2 x.

  Definition inter (s1 s2:t) := fun x => s1 x && s2 x.

  Definition diff (s1 s2:t)  := fun x => s1 x && negb (s2 x).

  Definition compl (s1:t) := fun x => negb (s1 x).

  Definition subset (s1 s2:t) := forall x, s1 x = true -> s2 x = true.

  Definition subset_diff : forall s1 s2, subset (diff s1 s2) s1.
  Proof.
    unfold subset,diff.
    intros.
    rewrite andb_true_iff in H. tauto.
  Qed.


  Lemma subset_inter2_iff : forall s1 s2 s3,
      subset s1 (inter s2 s3) <-> (subset s1 s2 /\ subset s1 s3).
  Proof.
    unfold subset,inter.
    split; intros.
    -
      repeat split; intros.
      apply H in H0. rewrite andb_true_iff in H0. tauto.
      apply H in H0. rewrite andb_true_iff in H0. tauto.
    -  rewrite andb_true_iff.
       destruct H ; split; auto.
  Qed.


  Definition is_empty (s:t) := subset s bot.


  Lemma subset_refl : forall s, subset s s.
  Proof.
    unfold subset. auto.
  Qed.

  Lemma compl_bot : forall x, compl bot x = top x.
  Proof.
    reflexivity.
  Qed.

  Lemma compl_top : forall x, compl top x = bot x.
  Proof.
    reflexivity.
  Qed.



  Lemma subset_trans : forall s1 s2 s3, subset s1 s2 -> subset s2 s3 -> subset s1 s3.
  Proof.
    unfold subset. auto.
  Qed.



  Lemma is_empty_inter_subset : forall s1 s2,
      is_empty (inter s1 s2) <->
        subset s1 (compl s2).
  Proof.
    unfold is_empty,inter,compl,subset.
    split; intros.
    - destruct (s2 x) eqn:S.
    apply (H x);auto.
    rewrite andb_true_iff. split; assumption.
    simpl. reflexivity.
    - destruct (s2 x) eqn:S.
      specialize (H x).
      rewrite S in H. apply H.
      rewrite andb_true_r in H0.
      auto.
      rewrite andb_false_r in H0.
      discriminate.
  Qed.

  Section MAKEUNION.
    Context {T:Type}.
    Variable set_of : T -> t.

    Fixpoint union_list (l:list T) :=
      match l with
      | nil => bot
      | e::l => union (set_of e) (union_list l)
      end.

  End MAKEUNION.

  Definition unionl (l:list t) := union_list (fun x => x) l.

  Definition of_list (l:list A) := union_list singleton l.

  Lemma singleton_refl : forall i, singleton  i i = true.
  Proof.
    intros. unfold singleton. destruct (eq_dec i i); congruence.
  Qed.

  Lemma diff_assoc : forall s1 s2 s3 x,
      diff (diff s1 s2) s3 x = diff s1 (union s2 s3) x.
  Proof.
    unfold diff,union.
    intros. destruct (s1 x); auto.
    simpl. rewrite negb_orb.
    reflexivity.
  Qed.

  Lemma subset_morph1 : forall s1' s1 s2,
    (forall x, s1 x = s1' x) ->
      subset s1' s2 ->
      subset s1 s2.
  Proof.
    unfold subset.
    intros.
    apply H0. rewrite <- H; auto.
  Qed.

  Lemma subset_morph2 : forall s1 s2 s2',
    (forall x, s2 x = s2' x) ->
      subset s1 s2' ->
      subset s1 s2.
  Proof.
    unfold subset.
    intros.
    rewrite H. auto.
  Qed.


  Lemma subset_diff_anti : forall s1 s2 s2',
      subset s2' s2 ->
      subset (diff s1 s2) (diff s1 s2').
  Proof.
    unfold subset, diff.
    intros.
    rewrite andb_true_iff in *.
    rewrite negb_true_iff in *.
    specialize (H x).
    destruct (s2' x); intuition congruence.
  Qed.

  Lemma union_sym : forall s1 s2 x,
      union s1 s2 x = union s2 s1 x.
  Proof.
    unfold union.
    intros. rewrite orb_comm.
    reflexivity.
  Qed.

  Lemma union_assoc : forall s1 s2 s3 x,
      union (union s1 s2) s3 x = union s1 (union s2 s3) x.
  Proof.
    unfold union.
    intros. rewrite orb_assoc.
    reflexivity.
  Qed.


  Lemma subset_union1 : forall s1 s2,
      subset s1 (union s1 s2).
  Proof.
    unfold subset, union; intros.
    rewrite orb_true_iff.
    tauto.
  Qed.

  Lemma diff_union_1 : forall s1 s2,
      subset (diff (union s1 s2) s1) s2.
  Proof.
    unfold subset,diff,union.
    intros.
    destruct (s1 x),(s2 x); simpl in * ; auto.
  Qed.

  Lemma subset_compl : forall s1 s2,
      subset (compl s1) (compl s2) <->
        subset s2 s1.
  Proof.
    unfold subset,compl;intros.
    split; intros;
    specialize (H x).
    - rewrite! negb_true_iff in *.
    destruct (s1 x);intuition congruence.
    - rewrite! negb_true_iff in *.
      destruct (s2 x); intuition congruence.
  Qed.

  Lemma subset_union_mono : forall s1 s2 s1' s2',
      subset s1 s1' ->
      subset s2 s2' ->
      subset (union s1 s2) (union s1' s2').
  Proof.
    unfold union, subset.
    intros.
    rewrite orb_true_iff in *.
    specialize (H x). specialize (H0 x).
    tauto.
  Qed.

  Lemma compl_union: forall s1 s2 x,
      compl (union s1 s2) x = inter (compl s1) (compl s2) x.
  Proof.
    unfold compl,union,inter. intros.
    rewrite negb_orb. reflexivity.
  Qed.

  Lemma compl_union_diff: forall s1 s2 x,
      compl (union s1 s2) x = diff (compl s1) s2 x.
  Proof.
    unfold compl,union,diff. intros.
    rewrite negb_orb. reflexivity.
  Qed.

  Lemma union_list_map : forall {T1 T2:Type} (F : T2  -> t) (G : T1 -> T2) l x,
      union_list F (map G l) x = union_list (fun x => F (G x)) l x.
  Proof.
    induction l; simpl;auto.
    -
      intros.
      unfold union.
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma union_list_morph : forall {T: Type} (F1 F2: T -> t) l,
      (forall s x, In s l -> F1 s x = F2 s x) ->
      forall x, union_list F1 l x = union_list F2 l x.
  Proof.
    induction l; simpl; auto.
    intros.
    unfold union. rewrite IHl by auto. rewrite H.
    reflexivity. tauto.
  Qed.


  Lemma subset_union_list : forall  {T1 T2:Type}(F1:T1 -> t) (F2: T2 -> t) (G: T1 -> T2) l,
    (forall s x, F1 s x = F2 (G s) x) ->
    subset (union_list F1 l) (union_list F2 (map G l)).
  Proof.
    repeat intro.
    rewrite union_list_map.
    rewrite <- H0.
    apply union_list_morph; eauto.
  Qed.


  Lemma subset_union_list_mono : forall  {T1:Type}(F1:T1 -> t) (F2: T1 -> t)  l,
    (forall s, In s l -> subset (F1 s) (F2 s)) ->
    subset (union_list F1 l) (union_list F2 l).
  Proof.
    repeat intro.
    induction l ; simpl in *; auto.
    unfold union in H0. unfold union.
    rewrite orb_true_iff in *.
    destruct H0. left. revert H0. apply H. tauto.
    right.
    apply IHl. intros. apply H; tauto.
    auto.
  Qed.


  Lemma subset_union_list_in : forall {T1:Type} (F: T1 -> t) l v,
      In v l ->
      subset (F v) (union_list F l).
  Proof.
    induction l ; simpl; auto.
    - tauto.
    - intros.
      destruct H; subst.
      apply subset_union1.
      apply IHl in H.
      eapply subset_morph2.
      intros. rewrite union_sym.
      reflexivity.
      eapply subset_trans;eauto.
      eapply subset_union1.
  Qed.

  Lemma is_empty_morph : forall s1 s2,
      (forall x, s1 x = s2 x) ->
      is_empty s2 ->
      is_empty s1.
  Proof.
    unfold is_empty,bot; repeat intro.
    rewrite H in H1. apply H0 in H1.
    auto.
  Qed.

  Lemma inter_union : forall s1 s2 s3,
      forall x, inter s1 (union s2 s3) x = union (inter s1 s2) (inter s1 s3) x.
  Proof.
    unfold inter,union.
    intros.
    btauto.
  Qed.

  Lemma is_empty_union : forall s1 s2,
      is_empty (union s1 s2) <-> (is_empty s1 /\ is_empty s2).
  Proof.
    unfold is_empty,union,subset, bot.
    repeat split; repeat intro.
    specialize (H x). rewrite orb_true_iff in H. apply H; tauto.
    specialize (H x). rewrite orb_true_iff in H. apply H; tauto.
    rewrite orb_true_iff in H0.
    destruct H; destruct H0; auto.
    apply (H x); auto.
    apply (H1 x); auto.
  Qed.


End S.

#[global]  Create HintDb bset.

#[global] Hint Resolve singleton_refl : bset.


Lemma singleton_true_iff :
  forall {A: Type}
         (eq_dec: forall (x y: A), {x = y}+{x <> y}) i x,
    (singleton eq_dec i x = true) <-> i = x.
Proof.
  unfold singleton.
  intros.
  destruct (eq_dec x i); intuition congruence.
Qed.

Lemma singleton_false_iff :
  forall {A: Type}
         (eq_dec: forall (x y: A), {x = y}+{x <> y}) i x,
    (singleton eq_dec i x = false) <-> i <> x.
Proof.
  unfold singleton.
  intros.
  destruct (eq_dec x i); intuition congruence.
Qed.



Ltac sset :=
  unfold subset,inter,union,singleton,compl,diff;
  intros;
  repeat
  match goal with
  | H :context[ _ && _ = true]|- _ => rewrite andb_true_iff in H
  | H : context[_ || _ = true] |- _ => rewrite orb_true_iff in H
  | H : context[negb _ = true] |- _ => rewrite negb_true_iff in H

  | |- context[ _ && _ = true] => rewrite andb_true_iff
  | |- context[_ || _ = true]  => rewrite orb_true_iff
  | |- context[negb _ = true] => rewrite negb_true_iff

  | H :context[ _ && _ = false]|- _ => rewrite andb_false_iff in H
  | H : context[_ || _ = false] |- _ => rewrite orb_false_iff in H

  | |- context[ _ && _ = false] => rewrite andb_false_iff
  | |- context[_ || _ = false]  => rewrite orb_false_iff

  | H : context[singleton _ _ _ = true] |- _ => rewrite singleton_true_iff in H
  | H : context[singleton _ _ _ = false] |- _ => rewrite singleton_false_iff in H
  | |- context[singleton _ _ _ = true] =>  rewrite singleton_true_iff
  | |- context[singleton _ _ _ = false] =>  rewrite singleton_false_iff
  end ; try tauto.
