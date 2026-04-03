From Stdlib Require Import List String BinaryString.
From compcert Require Import Maps Ctypesdefs.
From BarocqComp Require Import Ident Res.
From BarocqComp Require Import Pp.
Import ListNotations.

Local Open Scope error_monad_scope.

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

Module SSet.
  Module _Set := ITree(StringIndexed).

  Definition t := _Set.t unit.

  Definition empty : t := _Set.empty unit.

  Definition add (x:StringIndexed.t) (s:t) := _Set.set x tt s.

  Definition mem (x:StringIndexed.t) (s:t) :=
    match _Set.get x s with
    | None => false
    | Some _ => true
    end.

  Definition union_elt (e1 e2:option unit) :=
    match e1 , e2 with
    | Some x , _ | _ , Some x => Some x
    | None , None => None
    end.

  Definition union (s1 s2:t) := _Set.combine union_elt s1 s2.
End SSet.

Module PTree.
  Include Maps.PTree.

  Lemma map1'_set0:
    forall (A B: Type) (f: A -> B) k x,
    map1' f (set0 k x) = set0 k (f x).
  Proof.
    induction k; intros; simpl.
    - rewrite IHk. reflexivity.
    - rewrite IHk. reflexivity.
    - reflexivity.
  Qed.

  Lemma map1'_set':
    forall (A B: Type) (f: A -> B) (m: tree' A) (k: BinNums.positive) (x: A),
    map1' f (set' k x m) = set' k (f x) (map1' f m).
  Proof.
    intros A. induction m; intros;
    destruct k; simpl; try (reflexivity || rewrite map1'_set0; reflexivity).
    - rewrite IHm; reflexivity.
    - rewrite IHm; reflexivity.
    - rewrite IHm; reflexivity.
    - rewrite IHm2; reflexivity.
    - rewrite IHm1; reflexivity.
    - rewrite IHm; reflexivity.
    - rewrite IHm2; reflexivity.
    - rewrite IHm1; reflexivity.
  Qed.

  Theorem map1_set:
    forall (A B: Type) (f: A -> B) (m: tree A) (k: BinNums.positive) (x: A),
    map1 f (set k x m) = set k (f x) (map1 f m).
  Proof.
    destruct m; intros.
    - simpl. unfold set. rewrite map1'_set0. reflexivity.
    - unfold map1. unfold set.
      rewrite map1'_set'. reflexivity.
  Qed.

End PTree.

Module STree.

  Include ITree(StringIndexed).

  Definition fold {A B} (f: B -> StringIndexed.t -> A -> B) (m: STree.t A) (v: B) : B :=
    PTree.fold (fun acc ki vi => f acc (Ident.of_pos ki) vi) m v.

  Definition map {A B} (f : StringIndexed.t -> A -> B) (m : STree.t A) : STree.t B :=
    PTree.map (fun ki vi => f (Ident.of_pos ki) vi) m.

  Definition map1 {A B} (f: A -> B) (m: STree.t A) : STree.t B :=
    PTree.map1 f m.

  Definition keys {A: Type} (m: STree.t A) : SSet.t :=
    map1 (fun _ => tt) m.
    
  Lemma keys_get_some_mem:
    forall (A: Type) (m: STree.t A) k v,
    STree.get k m = Some v ->
    SSet.mem k (keys m) = true.
  Proof.
    unfold keys, SSet.mem, SSet._Set.get; intros.
    rewrite PTree.gmap1. unfold get in H. rewrite H.
    reflexivity.
  Qed.

  Lemma keys_mem_true_get:
    forall (A: Type) (m: STree.t A) k,
    SSet.mem k (keys m) = true ->
    (exists v, STree.get k m = Some v).
  Proof.
    unfold keys, SSet.mem, SSet._Set.get; intros.
    destruct (map1 (fun _ : A => tt) m) ! (StringIndexed.index k) eqn:Emem.
    - unfold STree.map1 in Emem. rewrite PTree.gmap1 in Emem.
      unfold Coqlib.option_map in Emem.
      destruct (m!(StringIndexed.index k)) eqn:Eget; try discriminate.
      exists a. exact Eget.
    - unfold STree.map1 in Emem. rewrite PTree.gmap1 in Emem.
      unfold Coqlib.option_map in Emem.
      destruct (m!(StringIndexed.index k)) eqn:Eget; discriminate.
  Qed.

  Lemma keys_get_none_iff:
    forall (A: Type) (m: STree.t A) k,
    STree.get k m = None <->
    STree.get k (keys m) = None.
  Proof.
    unfold keys, STree.get, STree.map1; split; intros.
    - rewrite PTree.gmap1. rewrite H. reflexivity.
    - rewrite PTree.gmap1 in H.
      destruct (m!(StringIndexed.index k)); try discriminate.
      reflexivity.
  Qed.

  Lemma keys_get_mem_false_iff:
    forall (A: Type) (m: STree.t A) k,
    STree.get k m = None <->
    SSet.mem k (keys m) = false.
  Proof.
    unfold SSet.mem, SSet._Set.get. split; intros.
    - rewrite keys_get_none_iff in H. unfold get in H.
      rewrite H. reflexivity.
    - destruct ((keys m)!(StringIndexed.index k)) eqn:Eget; try discriminate.
      apply keys_get_none_iff in Eget. exact Eget. 
  Qed.

  Lemma keys_set:
    forall (A: Type) (m: STree.t A) k v,
      STree.keys (STree.set k v m) = SSet.add k (STree.keys m).
  Proof.
    intros. apply PTree.map1_set.
  Qed.

  Definition mem {A} (e:elt) (m: STree.t A) :=
    match get e m with
    | None => false
    | Some _ => true
    end.

  Definition getl {A: Type} (s:string) (m:STree.t (list A)) : list A :=
    match get s m with
    | None => nil
    | Some l => l
    end.

  Definition setl {A: Type} (s:string) (e:A) (m:STree.t (list A)) : STree.t (list A) :=
    set s (e::getl s m) m.

  Definition pp {A: Type} (sep:box) (pp_elt : A -> box) (s:STree.t A) : box :=
    STree.fold (fun acc k v => Bstack acc (Bcat (Bstr k)
                                             (Bcat
                                                sep (pp_elt v))) Left) s Bemp.

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
    | nil => efail
    | (x, v) :: l' =>
        if key_eq x k then eret v
        else find_err k l'
    end.

  Definition map (A: Type) (f: V -> A) (l: t V) : t A :=
    List.map (fun kv => (fst kv, f (snd kv))) l.

  Definition map_err (A: Type) (f: V -> res A) (l: t V) : res (t A) :=
    mmap (fun '(x, v) => do a <- f v; eret (x, a)) l.

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

  Definition fold_right (A: Type) (f: key -> V -> A -> A) (acc: A) (l: t V) : A :=
    List.fold_right (fun '(k, v) a => f k v a) acc l.

  Definition fold_left (A: Type) (f: A -> key -> V -> A) (l: t V) (acc: A) : A :=
    List.fold_left (fun a '(k, v) => f a k v) l acc.

  Definition filter (f: key -> V -> bool) (l: t V): t V :=
    List.filter (fun '(k, v) => f k v) l.

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
  Arguments fold_right {key V A}.
  Arguments fold_left {key V A}.
  Arguments filter {key V}.
  Arguments empty {key V}.

End MapList.

Definition smaplist (A:Type) := MapList.t string A.
