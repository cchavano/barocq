From Coq Require Import List ZArith Zcomplements ZifyBool Lia.
From VST Require Import Zlist.
From compcert Require Import Integers Coqlib.
From BarocqComp Require Import Intop Utils Option ZlistPlus.
Local Open Scope option_monad_scope.

Import ListNotations.

Set Implicit Arguments.

Polymorphic Definition array (A: Type) := list A.

Section ARRAYS.

  Variable A: Type.

  Definition Zlength (a: array A) : Z := Zlength a.

  Definition valid_index (a: array A) (i: int64) : bool :=
    (Int64.unsigned i <? Zlength a)%Z.

  Definition get (a: array A) (i: int64) : option A :=
    Coqlib.list_nth_z a (Int64.unsigned i).

  Definition set (a: array A) (i: int64) (x: A) : option ((array A):Type) :=
    if valid_index a i then ret (sublist 0 (Int64.unsigned i) a ++ x :: sublist ((Int64.unsigned i)+1) (Zlength a) a)
    else fail.

  Definition map (B: Type) (f: A -> B) (a: array A) : array B :=
    @List.map A B f a.

End ARRAYS.

Section Specs.

  Lemma map_preserve_length :
    forall (A B: Type) (f: A -> B) (a: array A),
      Zlength (map f a) = Zlength a.
  Proof.
    apply Zlength_map.
  Qed.

  Lemma map_preserve_valid_index :
    forall (A B: Type) (f: A -> B) (a: array A) (i: int64),
    valid_index (map f a) i = valid_index a i.
  Proof.
    intros. unfold valid_index. f_equal.
    apply map_preserve_length.
  Qed.

  Lemma get_map_same :
    forall (A B: Type) (f: A -> B) (a: array A) (i: int64),
    get (map f a) i =
    let* x := get a i in
    ret (f x).
  Proof.
    intros. unfold get.
    rewrite Coqlib.list_nth_z_map.
    destruct ((Coqlib.list_nth_z a (Int64.unsigned i))); reflexivity.
  Qed.

  Lemma set_map_same :
    forall (A B: Type) (f: A -> B) (v: A) (a: array A) (i: int64),
    set (map f a) i (f v) =
    let* a' := set a i v in
    ret (map f a').
  Proof.
    intros. unfold set. rewrite map_preserve_valid_index.
    destruct (valid_index a i); try reflexivity.
    unfold ret. simpl.
    f_equal.
    rewrite sublist_map.
    unfold map. rewrite List.map_app.
    simpl.
    rewrite sublist_map.
    rewrite Zlength_map.
    reflexivity.
  Qed.

  Lemma get_Some : forall (T:Type) (a: array T) id,
      let PRE := fun a id => Barray.valid_index a id = true in
      let POST := fun a id v => True in
      PRE a id ->
      exists v, Barray.get a id = Some v /\ POST a id v.
  Proof.
    unfold Barray.get.
    intros.
    unfold valid_index in H.
    assert (0 <= Int64.unsigned id < Zlength a) %Z.
    {
      generalize (Int64.unsigned_range id).
      lia.
    }
    rewrite <- list_nth_z_Some in H0.
    destruct (Coqlib.list_nth_z a (Int64.unsigned id)); try congruence.
    eexists ; split; eauto.
  Qed.


  Record setSPEC {T: Type} (a:array T) (id:int64) (v:T) (a':array T) :=
    {
      set_len : Zlength a = Zlength a';
      set_gss : Barray.get a' id = Some v;
      set_gso : forall id', id <> id' ->
                            Barray.get a id' = Barray.get a' id'}.

  Import Zcomplements.


  Lemma sublist_app_2 : forall {A: Type} lo hi (l1 l2:list A),
      lo = Zlength l1 ->
      hi = Zlength (l1 ++ l2) ->
      sublist lo hi (l1++l2) = l2.
  Proof.
    unfold sublist.
    intros. subst.
    rewrite firstn_same.
    rewrite skipn_app2.
    rewrite Zlength_correct.
    replace ((Z.to_nat (Z.of_nat (Datatypes.length l1)) - Datatypes.length l1))%nat with 0%nat.
    apply skipn_0.
    lia.
    rewrite Zlength_correct.
    lia.
    rewrite Zlength_correct.
    lia.
  Qed.

  Lemma set_Some : forall {T: Type} (a:array T) id v,
      valid_index a id = true ->
      exists a', set a id v = Some a' /\ setSPEC a id v a'.
  Proof.
    unfold set.
    intros.
    rewrite H.
    unfold valid_index in H.
    unfold Zlength in *.
    assert (BOUND := Int64.unsigned_range id).
    eexists ; split; eauto.
    constructor.
    - unfold Barray.Zlength in *.
      Zlength_solve.
    - unfold Barray.get.
      unfold Barray.Zlength in *.
      rewrite list_nth_z_app2.
      simpl.
      destruct (zeq (Int64.unsigned id - Zlength (sublist 0 (Int64.unsigned id) a)) 0).
      reflexivity.
      rewrite Zlength_sublist2 in n.
      lia.
      Zlength_solve.
    - intros. unfold Barray.get.
      unfold Barray.Zlength in *.
      assert (BOUND2 := Int64.unsigned_range id').
      assert (INBOUND : 0 <= (Int64.unsigned id) < Zlength a).
      { lia. }
      rewrite <- list_nth_z_Some in INBOUND.
      destruct (list_nth_z a (Int64.unsigned id)) eqn:GET; try congruence.
      apply list_nth_z_split in GET.
      destruct GET as (l1 & l2 & EQ & LEN).
      subst.
      rewrite sublist0_app2.
      rewrite LEN.
      rewrite Z.sub_diag.
      rewrite sublist_nil.
      rewrite <- app_assoc. simpl.
      replace (l1 ++ t :: l2) with ((l1 ++ t :: nil) ++ l2) at 3.
      rewrite sublist_app_2.
      rewrite! list_nth_z_app.
      destruct (Z_lt_dec (Int64.unsigned id') (Zlength l1)); auto.
      rewrite! list_nth_z_cons.
      destruct (Z.eq_dec (Int64.unsigned id' - Zlength l1) 0).
      assert (Int64.unsigned id <> Int64.unsigned id').
      { intro.
        apply H0.
        apply Int64.same_if_eq.
        unfold Int64.eq.
        destruct (zeq (Int64.unsigned id) (Int64.unsigned id')); congruence.
      }
      lia.
      reflexivity.
      rewrite Zlength_app.
      Zlength_solve.
      Zlength_solve.
      rewrite <- app_assoc. simpl. reflexivity.
      Zlength_solve.
  Qed.

  
End Specs.


Notation "t .[ i ]" := (get t i)
  (at level 2, left associativity, format "t .[ i ]").
Notation "t .[ i <- a ]" := (set t i a)
  (at level 2, left associativity, format "t .[ i <- a ]").
