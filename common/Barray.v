From Coq Require Import List ZArith.
From compcert Require Import Integers.
From BarocqComp Require Import Intop Utils OptionMonad.
Open Scope option_monad_scope.

Import ListNotations.

Set Implicit Arguments.

Polymorphic Definition array (A: Type) := list A.

Section ARRAYS.

  Variable A: Type.

  Definition length (a: array A) : nat := length a.

  Definition valid_index (a: array A) (i: int64) : bool :=
    Int64.cmpu Cle Int64.zero i &&
    ((U64.to_nat i) <? (length a))%nat.

  Definition get (a: array A) (i: int64) : option A :=
    if valid_index a i then nth_error a (U64.to_nat i)
    else fail.
  
  Fixpoint set_rec (l: list A) (n: nat) (x: A) {struct n} : list A :=
    match n, l with
    | O, y :: l' => x :: l'
    | S n', y :: l' => y :: (set_rec l' n' x)
    | _ , _ => nil
    end.

  Definition set (a: array A) (i: int64) (x: A) : option ((array A):Type) :=
    if valid_index a i then ret (set_rec a (U64.to_nat i) x)
    else fail.

  Definition map (B: Type) (f: A -> B) (a: array A) : array B :=
    @List.map A B f a.

End ARRAYS.

Section Specs.

  Lemma map_preserve_length :
    forall (A B: Type) (f: A -> B) (a: array A),
    length (map f a) = length a.
  Proof.
    induction a.
    - reflexivity.
    - simpl. f_equal. apply IHa.
  Qed.

  Lemma map_preserve_valid_index :
    forall (A B: Type) (f: A -> B) (a: array A) (i: int64),
    valid_index (map f a) i = valid_index a i.
  Proof.
    intros. unfold valid_index. f_equal.
    rewrite map_preserve_length.
    reflexivity.
  Qed. 

  Lemma get_map_same :
    forall (A B: Type) (f: A -> B) (a: array A) (i: int64),
    get (map f a) i =
    let* x := get a i in
    ret (f x).
  Proof.
    intros. unfold get. rewrite map_preserve_valid_index.
    destruct (valid_index a i); try reflexivity.
    apply Utils.nth_error_map_same.
  Qed.

  Lemma set_rec_map_same :
    forall (A B: Type) (f: A -> B) (v: A) (a: array A) (n: nat),
    set_rec (map f a) n (f v) =
    map f (set_rec a n v).
  Proof.
    induction a; destruct n.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - simpl. f_equal. apply (IHa n).
  Qed.

  Lemma set_map_same :
    forall (A B: Type) (f: A -> B) (v: A) (a: array A) (i: int64),
    set (map f a) i (f v) =
    let* a' := set a i v in
    ret (map f a').
  Proof.
    intros. unfold set. rewrite map_preserve_valid_index.
    destruct (valid_index a i); try reflexivity.
    rewrite set_rec_map_same. reflexivity.
  Qed.

End Specs.
