From Coq Require Import List ZArith.
From compcert Require Import Integers.
From BarocqComp Require Import Error Common.

Import ListNotations.

Set Implicit Arguments.

Definition array (A: Type) := list A.

Section ARRAYS.

  Variable A: Type.

  Definition length (a: array A) : nat := length a.

  Definition valid_index (a: array A) (i: int) : bool :=
    Int.cmp Cle Int.zero i &&
    ((int_to_nat i) <? (length a))%nat.

  Definition get (a: array A) (i: int) : res A :=
    if valid_index a i then err_of_opt (nth_error a (int_to_nat i))
    else fail.
  
  Fixpoint set_rec (l: list A) (n: nat) (x: A) {struct n} : list A :=
    match n, l with
    | O, y :: l' => y :: l'
    | S n', y :: l' => y :: (set_rec l' n' x)
    | _ , _ => nil
    end.

  Definition set (a: array A) (i: int) (x: A) : res (array A) :=
    if valid_index a i then ret (set_rec a (int_to_nat i) x)
    else fail.

End ARRAYS.