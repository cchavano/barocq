From Stdlib Require Import List ZifyBool Lia.
From compcert Require Import Coqlib.
From VST Require Import Zlist.

Lemma list_nth_z_eq : forall {A: Type} z (l:list A),
    list_nth_z l z = if Z_lt_dec z 0 then None
                     else nth_error l (Z.to_nat z).
Proof.
  intros.
  destruct (Z_lt_dec z 0).
  { revert z l0. induction l; simpl.
    - reflexivity.
    - intros. destruct (zeq z 0). lia.
      apply IHl. lia.
  }
  {
    assert (Z.of_nat (Z.to_nat z) = z) by lia.
    rewrite <- H at 1.
    clear n H.
    revert l.
    induction (Z.to_nat z); simpl.
    - destruct l; simpl; auto.
    - destruct l. simpl. reflexivity.
      rewrite <- IHn.
      simpl. f_equal.
      destruct (Pos.of_succ_nat n) eqn:POS; lia.
  }
Qed.

Lemma list_nth_z_Some: forall [A : Type] (l : list A) (n : Z), list_nth_z l n <> None <-> (0 <= n < Zlength l)%Z.
Proof.
  intros.
  rewrite list_nth_z_eq.
  destruct (Z_lt_dec n 0).
  - rewrite Zlength_correct.
    intuition try congruence.
    lia.
  - rewrite nth_error_Some.
    rewrite Zlength_correct.
    lia.
Qed.

Lemma list_nth_z_split:
  forall [A : Type] (l : list A) (n : Z) [a : A],
    list_nth_z l n = Some a -> exists l1 l2 : list A, l = l1 ++ a :: l2 /\ Zlength l1 = n.
Proof.
  intros.
  rewrite list_nth_z_eq in H.
  destruct (Z_lt_dec n 0). discriminate.
  apply nth_error_split in H.
  destruct H as (l1 & l2 & EQ & LEN).
  do 2 eexists. split. apply EQ.
  rewrite Zlength_correct. lia.
Qed.

Lemma  list_nthz_app1: forall [A : Type] (l l' : list A) [n : Z], (n < Zlength l)%Z -> list_nth_z (l ++ l') n = list_nth_z l n.
Proof.
  intros.
  rewrite! list_nth_z_eq.
  destruct (Z_lt_dec n 0); auto.
  apply nth_error_app1.
  rewrite Zlength_correct in H. lia.
Qed.


Lemma list_nth_z_app2:
  forall [A : Type] (l l' : list A) [n : Z],
    (Zlength l <= n)%Z ->
    list_nth_z (l ++ l') n = list_nth_z l' (n - Zlength l)%Z.
Proof.
  intros.
  rewrite! list_nth_z_eq.
  destruct (Z_lt_dec n 0); auto.
  specialize (Zlength_nonneg l); lia.
  destruct (Z_lt_dec (n - Zlength l) 0).
  lia.
  rewrite nth_error_app2.
  f_equal.
  rewrite Zlength_correct in *. lia.
  rewrite Zlength_correct in *. lia.
Qed.

Lemma list_nth_z_app :   forall [A : Type] (l l' : list A) (n : Z),
    list_nth_z (l ++ l') n = (if Z_lt_dec n (Zlength l) then list_nth_z l n else list_nth_z l' (n - Zlength l)%Z).
Proof.
  intros.
  rewrite Zlength_correct.
  rewrite! list_nth_z_eq.
  destruct (Z_lt_dec n 0).
  - destruct (Z_lt_dec n (Z.of_nat (Datatypes.length l))).
    auto.
    specialize (Zlength_nonneg l); lia.
  - rewrite nth_error_app.
    destruct (Z_lt_dec n (Z.of_nat (Datatypes.length l))).
    +
      replace ((Z.to_nat n <? Datatypes.length l)%nat) with true by lia.
      reflexivity.
    + replace ((Z.to_nat n <? Datatypes.length l)%nat) with false by lia.
      destruct (Z_lt_dec (n - Z.of_nat (Datatypes.length l)) 0); try lia.
      f_equal. lia.
Qed.

Lemma list_nth_z_skipn: forall [A : Type] (n : nat) (l : list A) (i : Z),
    list_nth_z (skipn n l) i = if Z_lt_dec i 0 then None else list_nth_z l (Z.of_nat n + i)%Z.
Proof.
  intros.
  rewrite! list_nth_z_eq.
  rewrite nth_error_skipn.
  destruct (Z_lt_dec i 0). auto.
  destruct (Z_lt_dec (Z.of_nat n + i) 0); auto.
  lia. f_equal. lia.
Qed.

Lemma list_nth_z_firstn: forall [A : Type] (n : nat) (l : list A) (i : Z),
    list_nth_z (firstn n l) i = (if Z_lt_dec i (Z.of_nat n) then list_nth_z l i else None).
Proof.
  intros.
  rewrite! list_nth_z_eq.
  rewrite nth_error_firstn.
  destruct (Z_lt_dec i 0).
  destruct (Z_lt_dec i (Z.of_nat n)); auto.
  destruct (Z.to_nat i <? n)%nat eqn:LT.
  destruct (Z_lt_dec i (Z.of_nat n)); try lia.
  reflexivity.
  destruct (Z_lt_dec i (Z.of_nat n)). lia.
  reflexivity.
Qed.

Lemma list_nth_z_cons: forall [A : Type]  (l : list A) (a : A) (i : Z),
    list_nth_z (a::l) i = if Z.eq_dec i 0 then Some a
                          else list_nth_z l (i-1).
Proof.
  intros.
  rewrite! list_nth_z_eq.
  destruct (Z_lt_dec i 0); auto.
  destruct (Z.eq_dec i 0); try lia.
  destruct (Z_lt_dec (i - 1) 0); try lia.
  reflexivity.
  destruct (Z.to_nat i) eqn:I.
  - rewrite nth_error_cons_0.
    destruct (Z.eq_dec i 0); try lia.
    reflexivity.
  - rewrite nth_error_cons_succ. destruct (Z.eq_dec i 0); try lia.
    destruct (Z_lt_dec (i - 1) 0); try lia.
    f_equal. lia.
Qed.
