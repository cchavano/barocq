From Coq Require Import List String BinaryString.
From compcert Require Import Maps Ctypesdefs.
From BarocqComp Require Import Ident Error.

Import ListNotations.

(** * A collection of different kind of maps. *)

(** ** String maps and trees *)

Module StringIndexed <: INDEXED_TYPE.
  
  Definition t := string.

  Definition eq := string_dec.
  
  Definition index := Ident.to_pos.

  Lemma index_inj:
    forall (x y: t), index x = index y -> x = y.
  Proof.
    apply ident_of_string_injective.
  Qed.

End StringIndexed.

Module SMap := IMap(StringIndexed).

Module STree.

  Include ITree(StringIndexed).

  Definition fold {A B} (f: B -> StringIndexed.t -> A -> B) (m: STree.t A) (v: B) : B :=
    PTree.fold (fun acc ki vi => f acc (Ident.of_pos ki) vi) m v.

  Definition map {A B} (f : BinNums.positive -> A -> B) (m : STree.t A) : STree.t B :=
    PTree.map f m.

  Definition mem {A} (e:elt) (m: STree.t A) :=
    match get e m with
    | None => false
    | Some _ => true
    end.

End STree.

Arguments STree.empty {A}.

(** ** Maps as associtation lists *)

Module MapList.

  Section KEY.

  Variable key : Type.
  Variable V : Type.

  Variable key_eq : forall (x y: key), {x = y} + {x <> y}.

  Polymorphic Definition t (A: Type) : Type := list (key * A).

  Fixpoint add (k: key) (v: V) (l: t V) : t V :=
    match l with
    | nil => [(k, v)]
    | (x, vx) :: l' =>
        if key_eq x k then (k, v) :: l'
        else (x, vx) :: (add k v l')
    end.

  Fixpoint find (k: key) (l: t V) (default: V) : V :=
    match l with
    | nil => default
    | (x, v) :: l' =>
        if key_eq x k then v
        else find k l' default
    end.

  Fixpoint find_err (k: key) (l: t V) : res V :=
    match l with
    | nil => fail
    | (x, v) :: l' =>
        if key_eq x k then ret v
        else find_err k l'
    end.

  Definition map (A: Type) (f: V -> A) (l: t V) : t A :=
    map (fun '(x, v) => (x, f v)) l.

  Definition map_err (A: Type) (f: V -> res A) (l: t V) : res (t A) :=
    mmap (fun '(x, v) => let* a := f v in ret (x, a)) l.

  Fixpoint mem (k: key) (l: t V) : bool :=
    match l with
    | nil => false
    | (x, _) :: l' =>
        if key_eq x k then true
        else mem k l'
    end.

  Fixpoint nodup (l: t V) : bool :=
    match l with
    | nil => true
    | (k, _) :: l' =>
        if mem k l' then false
        else nodup l'
    end.

  Fixpoint merge (l1 l2: t V) : t V :=
    match l1 with
    | nil => l2
    | (k1, v1) :: l1' =>
        if mem k1 l2 then merge l1' l2
        else (k1, v1) :: merge l1' l2
    end.

  Definition fold_left (A: Type) (f: A -> key -> V -> A) (l: t V) (acc: A) : A :=
    List.fold_left (fun a '(k, v) => f a k v) l acc.

  Section EQDEC.
    Variable Veq_dec  : forall (v1 v2:V),{v1 = v2} + {v1 <> v2}.

    Definition eq_dec_pair (x y: key * V) : {x = y} + {x <> y}.
    Proof.
      decide equality;auto.
    Defined.

  
  Definition eq_dec : forall (l1 l2: t V), {l1 = l2} +{l1 <> l2} := List.list_eq_dec eq_dec_pair.

  End EQDEC.

  Definition empty : t V := nil.

  End KEY.

  Arguments add {key V}.
  Arguments find {key V}.
  Arguments find_err {key V}.
  Arguments map {key V A}.
  Arguments map_err {key V A}.
  Arguments mem {key V}.
  Arguments nodup {key V}.
  Arguments merge {key V}.
  Arguments fold_left {key V A}.
  Arguments empty {key V}.

End MapList.

Polymorphic Definition smaplist := MapList.t string.
