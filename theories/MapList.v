From Coq Require Import List.
From BarocqComp Require Import Error.
Import ListNotations.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Section MAPLISTS.

  Variable K : Type.
  Variable V : Type.

  Hypothesis KeqDec : forall (x y: K), {x = y} + {x <> y}.

  Fixpoint find_k (k: K) (l: list (K * V)) (default: V): V :=
    match l with
    | nil => default
    | (x, v) :: l' =>
        if KeqDec x k then v
        else find_k k l' default
    end.

  Fixpoint find_k_err (k: K) (l: list (K * V)) : res V :=
    match l with
    | nil => fail
    | (x, v) :: l' =>
        if KeqDec x k then ret v
        else find_k_err k l'
    end.

  Definition map_k {A: Type} (f: V -> A) (l: list (K * V)) : list (K * A) :=
    map (fun '(x, v) => (x, f v)) l.

  Definition map_k_err {A: Type} (f: V -> res A) (l: list (K * V)) : res (list (K * A)) :=
    mmap (fun '(x, v) => let* a := f v in ret (x, a)) l.

  Fixpoint in_k (k: K) (l: list (K * V)) : bool :=
    match l with
    | nil => false
    | (x, _) :: l' =>
        if KeqDec x k then true
        else in_k k l'
    end.

  Fixpoint nodup_k (l: list (K * V)) : bool :=
    match l with
    | nil => true
    | (k, _) :: l' =>
        if in_k k l' then false
        else nodup_k l'
    end.

  Fixpoint merge_k (l1 l2: list (K * V)) : list (K * V) :=
    match l1 with
    | nil => l2
    | (k1, v1) :: l1' =>
        if in_k k1 l2 then merge_k l1' l2
        else (k1, v1) :: merge_k l1' l2
    end.

End MAPLISTS.