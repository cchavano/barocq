From Coq Require Import List ZArith.
From compcert Require Import Integers.
From BarocqComp Require Import Error Utils.

Import ListNotations.

Set Implicit Arguments.

Definition array (A: Type) := list A.

Section ARRAYS.

  Variable A: Type.

  Definition length (a: array A) : nat := length a.

  Definition valid_index (a: array A) (i: int64) : bool :=
    Int64.cmpu Cle Int64.zero i &&
    ((uint64_to_nat i) <? (length a))%nat.

  Definition get (a: array A) (i: int64) : res A :=
    if valid_index a i then err_of_opt (nth_error a (uint64_to_nat i))
    else fail.
  
  Fixpoint set_rec (l: list A) (n: nat) (x: A) {struct n} : list A :=
    match n, l with
    | O, y :: l' => x :: l'
    | S n', y :: l' => y :: (set_rec l' n' x)
    | _ , _ => nil
    end.

  Definition set (a: array A) (i: int64) (x: A) : res (array A) :=
    if valid_index a i then ret (set_rec a (uint64_to_nat i) x)
    else fail.

End ARRAYS.