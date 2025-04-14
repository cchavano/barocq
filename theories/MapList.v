From Coq Require Import List.
From BarocqComp Require Import Error.
Import ListNotations.

Set Implicit Arguments.

Section MAPLISTS.

  Definition t (A B: Type) : Type := list (A * B).

  Variable K : Type.
  Variable V : Type.

  Hypothesis KeqDec : forall (x y: K), {x = y} + {x <> y}.

  Definition empty : t K V := nil.

  Fixpoint add_k (k: K) (v: V) (l: t K V) : t K V :=
    match l with
    | nil => [(k, v)]
    | (x, vx) :: l' =>
        if KeqDec x k then (k, v) :: l'
        else (x, vx) :: (add_k k v l')
    end.

  Fixpoint find_k (k: K) (l: t K V) (default: V) : V :=
    match l with
    | nil => default
    | (x, v) :: l' =>
        if KeqDec x k then v
        else find_k k l' default
    end.

  Fixpoint find_k_err (k: K) (l: t K V) : res V :=
    match l with
    | nil => fail
    | (x, v) :: l' =>
        if KeqDec x k then ret v
        else find_k_err k l'
    end.

  Definition map_k {A: Type} (f: V -> A) (l: t K V) : t K A :=
    map (fun '(x, v) => (x, f v)) l.

  Definition map_k_err {A: Type} (f: V -> res A) (l: t K V) : res (t K A) :=
    mmap (fun '(x, v) => let* a := f v in ret (x, a)) l.

  Fixpoint in_k (k: K) (l: t K V) : bool :=
    match l with
    | nil => false
    | (x, _) :: l' =>
        if KeqDec x k then true
        else in_k k l'
    end.

  Fixpoint nodup_k (l: t K V) : bool :=
    match l with
    | nil => true
    | (k, _) :: l' =>
        if in_k k l' then false
        else nodup_k l'
    end.

  Fixpoint merge_k (l1 l2: t K V) : t K V :=
    match l1 with
    | nil => l2
    | (k1, v1) :: l1' =>
        if in_k k1 l2 then merge_k l1' l2
        else (k1, v1) :: merge_k l1' l2
    end.

  Definition fold_left_k {A: Type} (f: A -> K -> V -> A) (l: t K V) (acc: A) : A :=
    List.fold_left (fun a '(k, v) => f a k v) l acc.

End MAPLISTS.

Arguments empty {K V}.