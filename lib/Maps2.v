From Stdlib Require Import List String BinaryString.
From compcert Require Import Coqlib Maps Ctypesdefs.
From BarocqComp Require Import Ident Option BSet Res.
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


Lemma set'_set0 : forall {A: Type} i j (v1 v2:A),
    i <> j ->
    PTree.set' i v1 (PTree.set0 j v2) = PTree.set' j v2 (PTree.set0 i v1).
Proof.
  induction i ; simpl; auto.
  + intros. destruct j ; simpl; auto.
    f_equal. apply IHi; auto.
    congruence.
  + intros. destruct j ; simpl; auto.
    f_equal. apply IHi. congruence.
  + intros. destruct j ; simpl; auto.
    congruence.
Qed.

Lemma set_swap :
  forall {A: Type} i j (v1 v2:A) s,
    i <> j ->
    PTree.set i v1 (PTree.set j v2 s) = PTree.set j v2 (PTree.set i v1 s).
  Proof.
    unfold PTree.set.
    destruct s; auto.
    - intros.
      f_equal.
      apply set'_set0; auto.
    - intros.
      f_equal.
      revert j t H.
      induction i ; simpl; auto.
      + intros.
        destruct j ; simpl.
        * destruct t; try rewrite IHi by congruence; try reflexivity.
          rewrite set'_set0 by congruence. reflexivity.
          rewrite set'_set0 by congruence. reflexivity.
          rewrite set'_set0 by congruence. reflexivity.
        * destruct t; try rewrite IHi by congruence; try reflexivity.
        * destruct t; try rewrite IHi by congruence; try reflexivity.
      + destruct j ; simpl.
        * destruct t; try rewrite IHi by congruence; try reflexivity.
        * destruct t; intros; try rewrite IHi by congruence; try reflexivity;
          rewrite set'_set0 by congruence. reflexivity.
          rewrite set'_set0 by congruence. reflexivity.
          rewrite set'_set0 by congruence. reflexivity.
        * destruct t; try rewrite IHi by congruence; try reflexivity.
      + destruct j ; simpl.
        * destruct t; try rewrite IHi by congruence; try reflexivity.
        * destruct t; try rewrite IHi by congruence; try reflexivity.
        * congruence.
  Qed.


Module SMap := IMap(StringIndexed).

Module SSet.
  (** How do we fold over this structure?
      The advantage is that we get *strong* equality.
      But, the encoding hurts...
   *)

  Module _Set := ITree(StringIndexed).

  Definition t := _Set.t unit.

  Definition empty : t := _Set.empty unit.


  Definition add (x:StringIndexed.t) (s:t) := _Set.set x tt s.

  Definition singleton (x:StringIndexed.t)  := add x empty.

  Lemma add_swap : forall x y s, add x (add y s) = add y (add x s).
  Proof.
    intros.
    unfold add, _Set.set.
    destruct (Pos.eq_dec (StringIndexed.index x) (StringIndexed.index y)).
    - rewrite e.
      rewrite PTree.set2. reflexivity.
    -
    apply set_swap; auto.
  Qed.

  Definition mem (x:StringIndexed.t) (s:t) :=
    match _Set.get x s with
    | None => false
    | Some _ => true
    end.

  Definition positive_is_ident (p:positive) : bool :=
    Pos.eqb (ident_of_string (string_of_ident p)) p.


  (** [is_empty] is not efficient - no early stop *)
  Definition is_empty (s: t) :=
    PTree_Properties.for_all s (fun k _ => negb (positive_is_ident k)) .

  Lemma is_empty_correct : forall s,
      is_empty s = true <-> forall x, mem x s = false.
  Proof.
    unfold is_empty,mem in *; intros.
    unfold _Set.get.
    split; intros.
    - rewrite PTree_Properties.for_all_correct in H.
    unfold PTree.elt in H.
    destruct (s ! (StringIndexed.index x)) eqn:GET; auto.
    apply H in GET.
    unfold positive_is_ident in GET.
    rewrite string_of_ident_of_string in GET.
    rewrite negb_true_iff in GET.
    rewrite Pos.eqb_refl in GET. auto.
    - rewrite PTree_Properties.for_all_correct.
      intros.
      unfold positive_is_ident.
      specialize (H (string_of_ident x)).
      unfold StringIndexed.index in H.
      unfold to_pos in H.
      destruct ((ident_of_string (string_of_ident x) =? x)%positive) eqn:IDENT; auto.
      apply Pos.eqb_eq in IDENT.
      rewrite IDENT in H.
      destruct (s! x); try discriminate.
  Qed.


  Definition bset (s:t) (x:StringIndexed.t) : bool := mem x s.

  Lemma add_already_mem : forall x s,
      mem x s = true ->
      add x s = s.
  Proof.
    unfold mem,add.
    intros.
    destruct (_Set.get x s) eqn:GET; try discriminate.
    unfold _Set.get in GET.
    unfold _Set.set. revert GET.
    generalize (StringIndexed.index x).
    intro. clear H.
    destruct s. rewrite PTree.gempty. discriminate.
    unfold PTree.get,PTree.set.
    intro. f_equal.
    revert GET. revert t0.
    generalize  tt.
    induction p ; simpl.
    - destruct t0; simpl; intros; try discriminate ; f_equal; auto.
    - destruct t0; simpl; intros; try discriminate ; f_equal; auto.
    - destruct t0; simpl; intros; try discriminate ; f_equal; auto.
      destruct u0,u1; auto.
      destruct u0,u1; auto.
      destruct u0,u1; auto.
      destruct u0,u1; auto.
  Qed.

    
  Definition union_elt (e1 e2:option unit) :=
    match e1 , e2 with
    | Some _ , _ | _ , Some _ => Some tt
    | None , None => None
    end.

  Definition union (s1 s2:t) := _Set.combine union_elt s1 s2.

  Definition inter_elt (e1 e2:option unit) :=
    match e1 , e2 with
    | Some _ , Some _ => Some tt
    | _ , _ => None
    end.

  Definition inter (s1 s2:t) : t := _Set.combine inter_elt s1 s2.

  Definition diff_elt (e1 e2:option unit) :=
    match e1 with
    | None  => None
    | Some _ => match e2 with
                | None => Some tt
                | Some _ => None
                end
    end.

  Definition diff (s1 s2:t) := _Set.combine diff_elt s1 s2.


  Lemma union_empty : forall s, union s empty = s.
  Proof.
    destruct s. reflexivity.
    unfold union.
    unfold empty. unfold _Set.combine.
    unfold PTree.combine.
    unfold _Set.empty, PTree.empty.
    simpl.
    set (F:= (fix tree_rec' (m : PTree.tree' unit) : PTree.tree unit :=
     match m with
     | PTree.Node001 r =>
         match tree_rec' r with
         | PTree.Empty => PTree.Empty
         | PTree.Nodes r' => PTree.Nodes (PTree.Node001 r')
         end
     | PTree.Node010 _ => PTree.Nodes (PTree.Node010 tt)
     | PTree.Node011 _ r =>
         match tree_rec' r with
         | PTree.Empty => PTree.Nodes (PTree.Node010 tt)
         | PTree.Nodes r' => PTree.Nodes (PTree.Node011 tt r')
         end
     | PTree.Node100 l =>
         match tree_rec' l with
         | PTree.Empty => PTree.Empty
         | PTree.Nodes l' => PTree.Nodes (PTree.Node100 l')
         end
     | PTree.Node101 l r =>
         match tree_rec' l with
         | PTree.Empty =>
             match tree_rec' r with
             | PTree.Empty => PTree.Empty
             | PTree.Nodes r' => PTree.Nodes (PTree.Node001 r')
             end
         | PTree.Nodes l' =>
             match tree_rec' r with
             | PTree.Empty => PTree.Nodes (PTree.Node100 l')
             | PTree.Nodes r' => PTree.Nodes (PTree.Node101 l' r')
             end
         end
     | PTree.Node110 l _ =>
         match tree_rec' l with
         | PTree.Empty => PTree.Nodes (PTree.Node010 tt)
         | PTree.Nodes l' => PTree.Nodes (PTree.Node110 l' tt)
         end
     | PTree.Node111 l _ r =>
         match tree_rec' l with
         | PTree.Empty =>
             match tree_rec' r with
             | PTree.Empty => PTree.Nodes (PTree.Node010 tt)
             | PTree.Nodes r' => PTree.Nodes (PTree.Node011 tt r')
             end
         | PTree.Nodes l' =>
             match tree_rec' r with
             | PTree.Empty => PTree.Nodes (PTree.Node110 l' tt)
             | PTree.Nodes r' => PTree.Nodes (PTree.Node111 l' tt r')
             end
         end
     end)).
    induction t0; simpl;
      (try rewrite IHt0;
       try rewrite IHt0_1;
       try rewrite IHt0_2;
       try destruct a; reflexivity).
  Qed.


  Section MAKEUNION.
    Context {T:Type}.
    Variable set_of : T -> t.

    Fixpoint union_list (l:list T) :=
      match l with
      | nil => empty
      | e::l => union (set_of e) (union_list l)
      end.

  End MAKEUNION.

  Definition unionl (l:list t) := union_list (fun x => x) l.

  Definition of_list (l:list StringIndexed.t) := union_list singleton l.

  Definition remove (x:StringIndexed.t) (s:t) := _Set.remove x s.


  Lemma mem_empty : forall x,
      mem x empty = false.
  Proof.
    unfold mem,empty.
    intros.
    rewrite _Set.gempty.
    reflexivity.
  Qed.


  Lemma mem_add : forall x y s,
      mem x (add y s) = if String.string_dec x y then true
                        else mem x s.
  Proof.
    unfold mem,add.
    intros.
    rewrite _Set.gsspec.
    unfold _Set.elt_eq.
    unfold StringIndexed.eq.
    destruct (string_dec x y); auto.
  Qed.


  Lemma mem_singleton : forall i j, mem i (singleton j) = if string_dec j i then true else false.
  Proof.
    unfold singleton.
    intros. rewrite mem_add.
    rewrite mem_empty.
    destruct (string_dec i j); destruct (string_dec j i); congruence.
  Qed.

  
  Definition _remove_list (s:t) (l:list ident) :=
    List.fold_left (fun s e => remove e s) l s.

  Definition is_subset (s:t) (l:list ident) :=
    _Set.beq (fun _ _ => true) (_remove_list s l) empty.

  Lemma _get_remove_list : forall x l s,
      _Set.get x (_remove_list s l) = if In_dec string_dec x l then None
                                      else _Set.get x s.
  Proof.
    induction l; simpl; auto.
    - destruct (string_dec a x).
      + subst.
        intros.
        rewrite IHl. destruct (in_dec string_dec x l); auto.
        apply _Set.grs.
      + intros.
        rewrite IHl.
        destruct (in_dec string_dec x l); auto.
        apply _Set.gro. congruence.
  Qed.



  Lemma is_subset_sound : forall s l,
      is_subset s l = true ->
      forall x, mem x s = true -> In x l.
  Proof.
    unfold is_subset, mem.
    intros.
    destruct (_Set.get x s) eqn:GET; try discriminate.
    apply _Set.beq_sound with (x:=x) in H.
    intros.
    rewrite _Set.gempty in H.
    inv H.
    rewrite _get_remove_list in H2.
    destruct (in_dec string_dec x l); auto.
    congruence.
  Qed.

  Lemma mem_union : forall x P Q,
      mem x (union P Q) = mem x P || mem x Q.
  Proof.
    unfold mem,union.
    intros.
    rewrite _Set.gcombine.
    -
      destruct (_Set.get x P), (_Set.get x Q); reflexivity.
    - reflexivity.
  Qed.

  Lemma mem_inter : forall s1 s2 x,
      mem x (inter s1 s2) = mem x s1 && mem x s2.
  Proof.
    unfold mem,inter. intros.
    rewrite _Set.gcombine.
    -
      destruct (_Set.get x s1), (_Set.get x s2); try reflexivity.
    - reflexivity.
  Qed.

  Lemma set_singleton_refl : forall i, bset (singleton i) i = true.
  Proof.
    unfold bset,singleton.
    intros. rewrite mem_add. destruct (string_dec i i); congruence.
  Qed.

  Lemma bset_union : forall (P Q:t) x,
      bset (union P Q) x = BSet.union (bset P) (bset Q) x.
  Proof.
    unfold bset, BSet.union.
    intros. apply mem_union.
  Qed.

  Lemma bset_singleton : forall i x,
      bset (singleton i) x = BSet.singleton string_dec i x.
  Proof.
    unfold bset,singleton.
    intros. rewrite mem_add. unfold BSet.singleton.
    destruct (string_dec x i); auto.
  Qed.

  Lemma bset_inter : forall (P Q:t) x,
      bset (inter P Q) x = BSet.inter (bset P) (bset Q) x.
  Proof.
    unfold bset, BSet.inter.
    intros. apply mem_inter.
  Qed.

  Lemma bset_add : forall (P :t) y x,
      bset (add y P) x = BSet.union (bset (singleton y)) (bset P) x.
  Proof.
    unfold bset.
    intros. rewrite mem_add.
    unfold BSet.union.
    rewrite mem_singleton.
    destruct (string_dec x y); destruct (string_dec y x); try congruence;
    reflexivity.
  Qed.




  Lemma mem_diff : forall s1 s2 x,
      mem x (diff s1 s2) = mem x s1 && negb (mem x s2).
  Proof.
    unfold mem,diff. intros.
    rewrite _Set.gcombine.
    -
      destruct (_Set.get x s1), (_Set.get x s2); reflexivity.
    - reflexivity.
  Qed.

  Lemma bset_diff : forall s1 s2 x,
      bset (diff s1 s2) x = BSet.diff (bset s1) (bset s2)  x.
  Proof.
    unfold bset,BSet.diff.
    intros. rewrite mem_diff. reflexivity.
  Qed.

  Lemma bset_is_empty : forall s1,
      is_empty s1 = true <-> BSet.is_empty (bset s1).
  Proof.
    unfold BSet.is_empty.
    split; intros.
    -
    rewrite is_empty_correct in H.
    unfold subset,bset,bot.
    intros.
    rewrite H in H0. discriminate.
    - rewrite is_empty_correct.
    unfold subset,bset,bot in *.
    intros.
    specialize (H x). symmetry.  destruct (mem x s1); simpl;auto.
  Qed.

  Lemma is_empty_iff : forall s1 s2,
      (BSet.is_empty (bset s1) <-> BSet.is_empty (bset s2)) <-> is_empty s1 = is_empty s2.
  Proof.
    intros.
    destruct (is_empty s1) eqn:EMPTY.
    split; intros.
    symmetry.
    - rewrite bset_is_empty in *.
      tauto.
    - symmetry in H.
      rewrite bset_is_empty in *.
      tauto.
    - rewrite <- not_true_iff_false in EMPTY.
      rewrite bset_is_empty in EMPTY.
      split; intros.
      symmetry.
      rewrite <- not_true_iff_false.
      rewrite bset_is_empty. tauto.
      symmetry in H.
      rewrite <- not_true_iff_false in H.
      rewrite bset_is_empty in H. tauto.
  Qed.

  Lemma bset_union_list : forall {T: Type} F (l:list T) x,
      bset (union_list F l) x  = BSet.union_list (fun x => bset (F x)) l x.
  Proof.
    induction l; simpl;auto.
    intros. rewrite bset_union.
    unfold BSet.union.
    rewrite IHl. auto.
  Qed.

  Lemma bset_empty : forall x, bset empty x = bot x.
  Proof.
    unfold bset.
    intros. rewrite mem_empty.
    reflexivity.
  Qed.

  Lemma mem_remove : forall v s x, mem x (remove v s)  = if string_dec x v then false else mem x s.
  Proof.
    unfold mem,remove.
    intros.
    rewrite _Set.grspec.
    unfold _Set.elt_eq. unfold StringIndexed.eq.
    destruct (string_dec x v); auto.
  Qed.

  
  Lemma bset_remove : forall (v:ident) (s:t) x,
      bset (remove v s) x = BSet.diff (bset s) (BSet.singleton string_dec v) x.
  Proof.
    unfold bset.
    intros.
    rewrite mem_remove.
    unfold BSet.diff. unfold BSet.singleton.
    destruct (string_dec x v); auto.
    rewrite andb_comm. reflexivity.
    rewrite andb_comm. reflexivity.
  Qed.




#[global]  Create HintDb set.

#[global] Hint Resolve set_singleton_refl : set.






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

  Lemma keys_of_set : forall (s:SSet.t),
      keys s = s.
  Proof.
    unfold keys.
    unfold map1.
    unfold PTree.map1.
    destruct s; auto.
    f_equal.
    induction t0; simpl; auto.
    - congruence.
    - destruct a. reflexivity.
    - destruct a. congruence.
    - congruence.
    - congruence.
    - destruct a. congruence.
    - destruct a. congruence.
  Qed.

  Lemma get_set_same : forall {A: Type} x (v:A) (le: STree.t A),
      get x le = Some v ->
      set x v le = le.
  Proof.
    unfold get,set.
    unfold Maps.PTree.set.
    destruct le ; simpl.
    - intros. rewrite Maps.PTree.gempty in H.
      discriminate.
    - intros.
      f_equal.
      unfold Maps.PTree.get in H.
      revert t0 H.
      { induction (StringIndexed.index x); simpl.
        - destruct t0;try discriminate; intros; try f_equal;auto.
        - destruct t0;try discriminate; intros; try f_equal;auto.
        - destruct t0;try discriminate; intros; try f_equal;auto;
            congruence.
      }
  Qed.

  Lemma set_swap : forall {A: Type} x y (v1 v2:A) s, x <> y ->
                                 set x v1 (set y v2 s) =
                                   set y v2 (set x v1 s).
  Proof.
    intros.
    apply set_swap.
    intro.
    apply StringIndexed.index_inj in H0. congruence.
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

    Context {key : Type}.
    Context {V : Type}.

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

  Definition map {A: Type} (f: V -> A) (l: t V) : t A :=
    List.map (fun kv => (fst kv, f (snd kv))) l.

  Lemma in_map_iff : forall {A: Type} {f : V -> A} (l:t V) x,
      In x (map f l) <-> exists y, (fst y,f (snd y)) = x /\ In y l.
  Proof.
    unfold map.
    intros.
    rewrite in_map_iff.
    reflexivity.
  Qed.


  Definition map_err {A: Type} (f: V -> res A) (l: t V) : res (t A) :=
    mmap (fun '(x, v) => do a <- f v; eret (x, a)) l.


  Definition mmap {A: Type} (f: V -> option A) (l: t V) : option (t A) :=
    Option.mmap (fun x => Option.bind (f (snd x)) (fun a =>  Some (fst x, a))) l.

  Lemma mmap_In : forall {A: Type} (f : V -> option A) (l : t V) (r:t A),
      mmap f l = Some r ->
      forall vr v, In (vr,v) r -> exists v0, In (vr,v0) l /\ f v0 = Some v.
  Proof.
    unfold mmap.
    induction l ; simpl.
    - intros. inv H. simpl in H0. tauto.
    - intros. Option.monadInv H.
      Option.monadInv EQ.
      simpl in H0.
      destruct a; simpl in *.
      destruct H0.
      +  inv H.
         eexists; split. left. reflexivity. auto.
      +  eapply IHl in EQ1; eauto.
         destruct EQ1 as (vl & IN & EQ).
         eexists; split. right. eauto. auto.
  Qed.

  Lemma mmap_fst : forall {A: Type} (f : V -> option A) (l: t V) l',
      mmap f l = Some l' ->
      List.map fst l = List.map fst l'.
  Proof.
    induction l; simpl.
    - intros. inv H. reflexivity.
    - intros.
      Option.monadInv H.
      Option.monadInv EQ.
      simpl. f_equal. apply IHl ; auto.
  Qed.


  Fixpoint mem (k: key) (l: t V) : bool :=
    match l with
    | nil => false
    | (x, _) :: l' =>
        if key_eq x k then true
        else mem k l'
    end.

  Lemma in_mem : forall l x v,
      In (x,v) l ->
      mem x l = true.
  Proof.
    induction l;simpl.
    - tauto.
    - intros. destruct a.
      destruct (key_eq k x).
      auto.
      destruct H.
      + congruence.
      + eapply IHl ; eauto.
  Qed.


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

  Lemma fold_left_eq : forall {A: Type}  (f : A -> key -> V -> A) (l:t V) (acc:A),
      fold_left _ f l acc = List.fold_left (fun acc x => f acc (fst x) (snd x)) l acc.
  Proof.
    induction l; simpl;auto.
    intros. destruct a.
    auto.
  Qed.

  Lemma mem_find_err : forall x l,
      mem x l = false <-> Option.find_err key_eq x l = None.
  Proof.
    induction l; simpl.
    -  tauto.
    - destruct a. destruct (key_eq k x).
      subst. unfold ret. intuition congruence.
      tauto.
  Qed.

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

  Lemma map_map_err :
    forall {K A B C: Type} (fe : A -> res B) (f: B -> C) (l:@t K A) (l1: @t K B),
      map_err fe l = OK l1 ->
      map_err (fun x => do x1 <- fe x ; OK (f x1)) l = OK (map f l1).
  Proof.
    induction l ; simpl; auto.
    - intros. inv H. reflexivity.
    - intros. monadInv H.
      destruct a as (k,v). monadInv EQ.
      inv EQ2.
      rewrite EQ0. simpl.
      apply IHl in EQ1.
      rewrite EQ1. reflexivity.
  Qed.


  Lemma mmap_map : forall  {K A B C: Type} (F1 : A -> B) (F2 : B -> option C) (l:t A),
      mmap F2 (map F1 l) = mmap (key:=K) (fun x => F2 (F1 x)) l.
  Proof.
    induction l ;simpl; auto.
    rewrite IHl. reflexivity.
  Qed.


  Lemma mem_fst : forall K (eq_dec : forall (k1 k2:K), {k1 = k2} + {k1 <> k2})
                         V1 V2 (l1 : @t K V1) (l2:@t K V2),
      List.map fst l1 = List.map fst l2 ->
      forall x,
        mem eq_dec x l1 = mem  eq_dec x l2.
  Proof.
    induction l1 ; simpl.
    -  destruct l2 ; simpl; auto.
       discriminate.
    - destruct l2 ; simpl;try discriminate.
      intros. destruct a, p.
      simpl in H.
      inversion H ; subst ; clear H.
      destruct (eq_dec0 k0 x); auto.
  Qed.

  Lemma nodup_fst : forall K (eq_dec : forall (k1 k2:K), {k1 = k2} + {k1 <> k2})
                         V1 V2 (l1 : @t K V1) (l2:@t K V2),
      List.map fst l1 = List.map fst l2 ->
        nodup eq_dec l1 = nodup eq_dec l2.
  Proof.
    induction l1 ; simpl.
    -  destruct l2 ; simpl; auto.
       discriminate.
    - destruct l2 ; simpl;try discriminate.
      intros. destruct a, p.
      simpl in H.
      inversion H ; subst ; clear H.
      assert (mem  eq_dec0 k0 l1 = mem  eq_dec0 k0 l2).
      { apply mem_fst. auto. }
      rewrite H.
      apply IHl1 in H2.
      destruct (mem  eq_dec0 k0 l2); auto.
  Qed.




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
  Arguments mmap {key V}.

End MapList.

Definition smaplist (A:Type) := @MapList.t string A.
