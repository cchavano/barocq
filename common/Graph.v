(** minimal theory of directed, labelled graphs.
    The representation is using maps from nodes to successors. *)
From compcert Require Import Coqlib.
Require Import Lia ZifyBool ZifyUint63.
Require Import FMapInterface  ZArith Int.
Require Import FMapAVL.
Require FSetAVL.
Require Import List String.
Import ListNotations.
Require Import Unsigned63.

From BarocqComp Require Import Error Maps2 Utils Draw.

Inductive cedge :=
| MUST
| MAY
| NOTMAY.

Definition eqb_of_dec {A: Type} (eq_dec:forall (x y:A), {x = y}+{x <> y}) : A -> A -> bool :=
  fun x y => if eq_dec x y then true else false.


Fixpoint In_eq {A : Type} (eq : A -> A -> Prop) (e:A) (l:list A) :=
  match l with
  | nil => False
    | e'::l => eq e e' \/ In_eq eq e l
  end.

Inductive NoDup_eq {A : Type} (eq: A -> A -> Prop) : list A -> Prop :=
| NoDup_nil : NoDup_eq eq []
| NoDup_cons : forall (x : A) (l : list A), ~ In_eq eq  x l -> NoDup_eq eq l -> NoDup_eq eq (x :: l).

Lemma In_eq_In : forall {A:Type} (x:A) l,
    In_eq eq x l <->  In x l.
Proof.
  induction l ; simpl.
  - tauto.
  - intuition congruence.
Qed.

Definition eq_pair {A B:Type} (eqA:A -> A -> Prop) (eqB: B -> B -> Prop) (x y: A * B) : Prop :=
  eqA (fst x) (fst y) /\ eqB (snd x) (snd y).


Lemma In_eq_map : forall {A B:Type} (eqA: A -> A -> Prop) (eqB: B -> B -> Prop) (f: A -> B)
                         (EQ : forall x y, eqA x y -> eqB (f x) (f y))
                         l x,
    In_eq eqA x l -> In_eq eqB (f x) (map f l).
Proof.
  induction l;simpl.
  - auto.
  - intros.
    destruct H;[left|right];auto.
Qed.

Section S.
  Context {A: Type}.
  Variable eqA : A -> A -> Prop.
  Variable eq_refl : forall a, eqA a a.
  Variable eq_sym : forall a b, eqA a b -> eqA b a.
  Variable eq_trans : forall a b c, eqA a b -> eqA b c -> eqA a c.

  Lemma In_In_eq : forall e l, In e l -> In_eq eqA e l.
  Proof.
    induction l; simpl; auto.
    intuition subst.
    left ; apply eq_refl.
  Qed.

  Lemma In_eq_iff : forall e l, In_eq eqA e l <-> exists e', eqA e e' /\ In e' l.
  Proof.
    induction l; simpl.
    - split. tauto.
      intro. destruct H;tauto.
    - rewrite IHl.
      split; intros.
      +  destruct H.
         exists a. tauto.
         destruct H as (e' & IN).
         exists e'. tauto.
      + destruct H as (e' & EQ & IN).
        destruct IN. left.
        congruence.
        right. exists e'. tauto.
  Qed.

  
  Lemma In_eq_eq : forall l e1 e2, eqA e1 e2 -> In_eq eqA e1 l -> In_eq eqA e2 l.
  Proof.
    induction l; simpl;auto.
    intros.
    destruct H0.
    - left.
      apply eq_sym in H.
      eapply eq_trans;eauto.
    - right;eauto.
  Qed.


  Lemma NoDup_map : forall {B:Type} (l:list (A * B)),
    NoDup_eq eqA (map fst l) ->
    forall e d1 d2,
    In_eq (eq_pair eqA eq) (e, d1) l ->
    In_eq (eq_pair eqA eq) (e, d2) l ->
  d1 = d2.
Proof.
  induction l.
  - simpl. tauto.
  - simpl.
    intros.
    inv H.
    destruct a as (e1,d).
    simpl in *.
    destruct H0,H1; subst.
    +  inv H; inv H0.
       simpl in *.
       congruence.
    + inv H.
      apply In_eq_map with (f:=fst) (eqB:=eqA) in H0.
      simpl in H0. simpl in H1.
      apply In_eq_eq with (e2:=e1) in H0; auto.
      tauto.
      intros.
      unfold eq_pair in H. tauto.
    + inv H0.
      apply In_eq_map with (f:=fst) (eqB:=eqA) in H.
      simpl in H. simpl in H1.
      apply In_eq_eq with (e2:=e1) in H; auto.
      tauto.
      intros.
      unfold eq_pair in H0. tauto.
    +  eapply IHl;eauto.
Qed.

Lemma NoDup_map_snd : forall {B:Type}  (l:list (A * B)),
    NoDup (map snd l) ->
    forall e1 e2 d,
    In_eq (eq_pair eqA eq) (e1, d) l ->
    In_eq (eq_pair eqA eq) (e2, d) l ->
    eqA e1 e2.
Proof.
  induction l.
  - simpl. tauto.
  - simpl. intros.
    inv H.
    destruct a as (e3,d1).
    simpl in *.
    destruct H0,H1; subst.
    +  inv H; inv H0.
       simpl in *.
       eapply eq_trans ; eauto.
    + inv H.
      apply In_eq_map with (f:=snd) (eqB:=eq) in H0.
      simpl in H0.
      simpl in *. subst.
      rewrite In_eq_In in H0.
      tauto.
      unfold eq_pair. tauto.
    + inv H0.
      apply In_eq_map with (f:=snd) (eqB:=eq) in H.
      simpl in H.
      simpl in *. subst.
      rewrite In_eq_In in H.
      tauto.
      unfold eq_pair. tauto.
    +  eapply IHl;eauto.
Qed.



End S.




Section ListREMOVE.
  Context {A: Type}.
  Variable eqb : A -> A -> bool.

  Fixpoint List_remove (e:A) (l:list A) : list A :=
    match l with
    | nil => nil
    | e1 :: l => if eqb e e1 then List_remove e l
                 else e1 :: List_remove e l
    end.

  Fixpoint List_in (e:A) (l:list A) :=
    match l with
    | nil => False
    | e1::l => eqb e e1 = true \/ List_in e l
    end.

End ListREMOVE.



Module Int <: OrderedType.
  Definition t := int.

  Definition eq : t -> t -> Prop := @eq t.
  Definition lt : t -> t -> Prop := fun x y => ltb x y = true.

  Lemma eq_refl : forall (x:t), x = x.
  Proof. reflexivity. Qed.

  Lemma eq_sym : forall (x y:t), x = y -> y = x.
  Proof. congruence. Qed.

  Lemma eq_trans : forall (x y z:t), x = y -> y = z -> x = z.
  Proof. congruence. Qed.

  Lemma lt_trans : forall (x y z:t), lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt. intros. rewrite ltb_spec in *.
    lia.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> eq x y -> False.
  Proof.
    unfold lt. intros. rewrite ltb_spec in *.
    unfold eq in H0.
    apply (f_equal to_Z) in H0.
    lia.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    destruct (ltb x y) eqn:LTB.
    - apply LT. apply LTB.
    - destruct (eqb x y) eqn:EQB.
      apply EQ. rewrite eqb_spec in EQB. apply EQB.
      apply GT. unfold lt. rewrite ltb_spec.
      rewrite <- not_true_iff_false in LTB.
      rewrite <- not_true_iff_false in EQB.
      rewrite ltb_spec in LTB.
      rewrite eqb_spec in EQB.
      assert (to_Z x <> to_Z y).
      { intro.
        apply to_Z_inj in H. congruence. }
      lia.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {x <> y}.
  Proof.
    destruct (eqb x y) eqn:EQB.
    - left. rewrite eqb_spec in EQB. auto.
    - right. intro.
      subst. rewrite eqb_refl in EQB. discriminate.
  Qed.

  
End Int.

Module IntSet := FSetAVL.Make(Int).

Require FMapFacts.

Module Map(O:OrderedType).
  Module M := Make(O).
  Module Facts := FMapFacts.Facts(M).
  Include M.


  Definition merge {A: Type} (f : A -> A -> A) (e1 e2:option A) :=
    match e1 , e2 with
    | None , e | e , None => e
    | Some e1, Some e2    => Some (f e1 e2)
    end.

  Definition findl {A: Type} (k:key) (m: t (list A))  :=
    match find k m with
    | None => nil
    | Some l => l
    end.

  Lemma findl_empty : forall {A: Type} k, findl k (empty (list A)) = nil.
  Proof. reflexivity. Qed.


  Definition union {A: Type} (f : A -> A -> A) (m1 m2 : t A) := map2 (merge f) m1 m2.

  Definition remove_from_list
    {elt:Type} (eqb:elt -> elt -> bool)  (k:key) (e:elt) (m : t (list elt)) : t (list elt) :=
    match find k m with
    | None => m
    | Some l => add k (List_remove eqb e l) m
    end.

  Definition add_from_list {elt:Type}   (k:key) (e:elt) (m : t (list elt)) : t (list elt) :=
    add k (e::findl k m) m.


  Lemma find_empty : forall {A: Type} k,
      find k (empty A) = None.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma find_add : forall {A:Type} k1 k2 v (m:t A),
      find k1 (add k2 v m) = if O.eq_dec k1 k2 then Some v
                             else find k1 m.
  Proof.
    intros.
    destruct (O.eq_dec k1 k2).
    - apply find_1.
      apply add_1. apply E.eq_sym. apply e.
    - destruct (find k1 m) eqn:FK1.
      apply find_1.
      apply add_2.
      intro. apply n. apply O.eq_sym. auto.
      apply find_2 in FK1. auto.
      destruct (find k1 (add k2 v m))eqn:FADD;auto.
      apply find_2 in FADD.
      apply add_3 in FADD.
      apply find_1 in FADD.
      congruence.
      intro. apply n. apply O.eq_sym. auto.
  Qed.

  Lemma find_eq : forall {A:Type} k1 k2 (m:t A),
      O.eq k1 k2 ->
      find k1 m = find k2 m.
  Proof.
    intros.
    destruct (find k2 m) eqn:FIND.
    - apply find_1.
      apply find_2 in FIND.
      eapply MapsTo_1;eauto.
      apply E.eq_sym. auto.
    - destruct (find k1 m) eqn:FK1; auto.
      apply find_2 in FK1.
      eapply MapsTo_1 in FK1;eauto.
      apply find_1 in FK1.
      congruence.
  Qed.

  Lemma findl_eq : forall {A: Type} k1 k2 (x:A) m,
      O.eq k1 k2 ->
      findl k1 (add_from_list k2 x m) = x:: (findl k1 m).
  Proof.
    unfold findl,add_from_list.
    intros.
    rewrite find_add.
    destruct (O.eq_dec k1 k2).
    unfold findl.
    rewrite find_eq with (k2:=k1).
    reflexivity.
    apply O.eq_sym; auto.
    tauto.
  Qed.

  Lemma findl_neq : forall {A: Type} k1 k2 (x:A) m,
      ~ O.eq k1 k2 ->
      findl k1 (add_from_list k2 x m) = (findl k1 m).
  Proof.
    unfold findl,add_from_list.
    intros.
    rewrite find_add.
    destruct (O.eq_dec k1 k2).
    tauto. reflexivity.
  Qed.

  Lemma find_map2 : forall {A B C:Type} (f : option A -> option B -> option C)
                           (FN : f None None = None)
                           m1 m2 x,
        f (find x m1) (find x m2) = find x (map2 f m1 m2).
  Proof.
    intros.
    rewrite Facts.map2_1bis.
    reflexivity.
    auto.
  Qed.



    
End Map.  
  
Module IntMap := Map(Int).

Module Type NodeLabelT.
  Axiom t : Type.
  Axiom lt: t -> t -> Prop.
  Axiom eq: t -> t -> Prop.
  Axiom depth : t -> nat.

  Axiom eq_refl  : forall x, eq x x.
  Axiom eq_sym   : forall x y, eq x y -> eq y x.
  Axiom eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y, lt x y -> not (eq x y).

  Axiom compare : forall x y : t, Compare lt eq x y.
  Axiom eq_dec : forall (x y:t),{eq x y} + {not (eq x y)}.

End NodeLabelT.



Module Type EdgeLabelT.
  Axiom t : Type.
  Axiom lt: t -> t -> Prop.
  Axiom eq: t -> t -> Prop.
  Axiom eq_refl  : forall x, eq x x.
  Axiom eq_sym   : forall x y, eq x y -> eq y x.
  Axiom eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y, lt x y -> not (eq x y).

  Axiom compare : forall x y : t, Compare lt eq x y.
  Axiom eq_dec : forall (x y:t),{eq x y} + {not (eq x y)}.

  Axiom pp : t -> box.

End EdgeLabelT.

Module Make(NodeLabel: NodeLabelT)(EdgeLabel:EdgeLabelT).

  (** nodes are identified by an integer [int].
      NodeLabel and EdgeLabel are indexed.
   *)

  Module NLMap := Map(NodeLabel).
  Module ELMap := Map(EdgeLabel).

  Definition Edge := IntMap.t (NodeLabel.t * list (EdgeLabel.t * int)).


  Record t := mk
    {
      root  : int;
      edges : Edge;
      parent : IntMap.t (EdgeLabel.t * int); (* reverse edge - remember we have a tree *)
      nodelabels :  NLMap.t (list int) ; (* nodes with a given label *)
      edgelabels :  ELMap.t (list int) ; (* nodes which edges have a given label *)
      fresh      : int; (* fresh node *)
    }.

  Definition get_label (g:t) (n:int) :=
    match IntMap.find n (edges g) with
    | None => fail
    | Some(n,_) => OK n
    end.


  Definition depth (g:t) :=
    let* lb := get_label g (root g)  in
    OK (NodeLabel.depth lb).

  Definition get_successors (g:t) (n:int) :=
    match IntMap.find n (edges g) with
    | None => nil
    | Some(_,l) => l
    end.

  Fixpoint xdraw (fuel:nat) (g:t) (n:int) :=
    match fuel with
    | O => Bstr (string_of_int n)
    | S fuel =>
        Bstack (Bstr (string_of_int n))
          (List.fold_right
             (fun e acc => (Bcat (Bstack (EdgeLabel.pp (fst e))
                                    (xdraw fuel g (snd e)) Middle) acc)) (Bstr "") (get_successors g n)) Middle
    end.

  Definition pp (g:t) :=
    let d := match depth g with
             | OK d => d
             | _    => O
             end in
    xdraw d g (root g).
  

  Definition eqEN (x y : EdgeLabel.t * int) :=
    EdgeLabel.eq (fst x) (fst y) /\ (snd x = snd y).

  Lemma eqEN_refl : forall x, eqEN x x.
  Proof.
    unfold eqEN. split; auto.
    apply EdgeLabel.eq_refl.
  Qed.

  Lemma eqEN_sym : forall x y, eqEN x y -> eqEN y x.
  Proof.
    unfold eqEN. intros.
    destruct H ; split;auto.
    apply EdgeLabel.eq_sym;auto.
  Qed.

  Lemma eqEN_trans : forall x y z, eqEN x y -> eqEN y z -> eqEN x z.
  Proof.
    unfold eqEN. intros.
    destruct H,H0 ; split;auto.
    eapply EdgeLabel.eq_trans;eauto.
    congruence.
  Qed.


  Definition has_edge (o:int) (e:EdgeLabel.t) (d:int) (E:Edge) :=
    exists nl l, IntMap.find o E = Some (nl,l)
                 /\ In_eq eqEN (e,d) l.

  Definition has_edge_rev (o:int) (e:EdgeLabel.t) (d:int) (m:IntMap.t (EdgeLabel.t * int)) :=
    exists e', IntMap.find d m = Some (e', o) /\ EdgeLabel.eq e e'.


  Definition has_node_label (o:int) (nl:NodeLabel.t) (E:Edge) :=
    exists l nl', IntMap.find o E = Some (nl',l) /\ NodeLabel.eq nl nl'.

  Definition has_node_label_rev (o:int) (nl:NodeLabel.t) (lbs:NLMap.t (list int)) :=
    In o (NLMap.findl nl lbs).

  Record wf (g:t) :=
    {
      wf_nodup  : forall o e d1 d2, has_edge o e d1 (edges g) -> has_edge o e d2 (edges g) -> d1 = d2;
      wf_tree  : forall o1 o2 e1 e2 d, has_edge o1 e1 d (edges g) -> has_edge o2 e2 d (edges g) -> o1 = o2 /\ EdgeLabel.eq e1 e2;
      wf_parent : forall o e d, has_edge o e d (edges g) <-> has_edge_rev o e d (parent g);
      wf_nl     : forall o nl, has_node_label o nl (edges g) <-> has_node_label_rev o nl (nodelabels g);
      wf_el     : forall o e, In o (ELMap.findl e (edgelabels g)) <-> exists d, has_edge o e d (edges g);
      wf_fresh  : forall o  lb, has_node_label o lb (edges g) -> (ltb o (fresh g) = true)%int63
    }.


  Fixpoint find_label (lb:EdgeLabel.t) (l:list (EdgeLabel.t * int)) :=
    match l with
    | nil => None
    | (el,n)::l => if EdgeLabel.eq_dec lb el then Some n else find_label lb l
    end.

  Lemma find_label_eq : forall lb lb' (EQ: EdgeLabel.eq lb lb') l,
      find_label lb l = find_label lb' l.
  Proof.
    induction l; simpl;auto.
    destruct a. destruct (EdgeLabel.eq_dec lb t0);
      destruct (EdgeLabel.eq_dec lb' t0);auto.
    apply EdgeLabel.eq_sym in EQ.
    exfalso ;apply n.
    eapply EdgeLabel.eq_trans;eauto.
    exfalso ;apply n.
    eapply EdgeLabel.eq_trans;eauto.
  Qed.

  Lemma find_label_not_In : forall lb l,
      ~ In_eq EdgeLabel.eq lb (map fst l) ->
      find_label lb l = None.
  Proof.
    induction l; simpl;auto.
    destruct a. simpl.
    destruct (EdgeLabel.eq_dec lb t0);auto.
    tauto.
  Qed.


  
  Fixpoint find_node (n:int) (l:list (EdgeLabel.t * int)) :=
    match l with
    | nil => None
    | (e,n')::l => if Int.eq_dec n  n'  then Some e else find_node n l
    end.


  Fixpoint partition_label (lb:EdgeLabel.t) (l:list (EdgeLabel.t * int)) :=
    match l with
    | nil => None
    | (el,n)::l => if EdgeLabel.eq_dec lb el
                   then Some (n,l)
                   else match partition_label lb l with
                        | None => None
                        | Some (n',l') => Some (n', (el,n) :: l')
                        end
    end.

  Definition mkroot (lb:NodeLabel.t) :=
    mk 0
      (IntMap.add 0%int63 (lb,nil) (IntMap.empty _))
      (IntMap.empty _) (NLMap.add lb (0::nil)%int63 (NLMap.empty _)) (ELMap.empty _) 1.

  Lemma has_edge_empty : forall o e d, has_edge o e d (IntMap.empty _)  <-> False.
  Proof.
    split ; [| tauto].
    unfold has_edge.
    intros.
    simpl in H.
    destruct H as (nl & l & (FIND & _)).
    simpl in FIND.
    rewrite IntMap.find_empty in FIND.
    discriminate.
  Qed.

  Lemma has_edge_rev_empty : forall o e d, has_edge_rev o e d (IntMap.empty _) <-> False.
  Proof.
    split ; [| tauto].
    unfold has_edge_rev.
    simpl.
    rewrite IntMap.find_empty.
    intros. destruct H.
    intuition congruence.
  Qed.


  Lemma has_node_label_empty : forall o nl, has_node_label o nl (IntMap.empty _) <-> False.
  Proof.
    split ; [| tauto].
    unfold has_node_label.
    intros.
    simpl in H.
    destruct H as (l & FIND).
    rewrite IntMap.find_empty in FIND.
    destruct FIND ; intuition congruence.
  Qed.

  Lemma has_node_label_rev_empty : forall o nl, has_node_label_rev o nl (NLMap.empty _) <-> False.
  Proof.
    split ; [| tauto].
    unfold has_node_label_rev.
    simpl.
    auto.
  Qed.

    Lemma has_edge_label : forall o e d E,
      has_edge o e d E -> exists lb, has_node_label o lb E.
  Proof.
    intros.
    destruct H.
    exists x. destruct H as (l & H & IN); do 2 eexists ;eauto.
    split. apply H.
    apply NodeLabel.eq_refl.
  Qed.

  Lemma has_edge_add :
    forall o e d1 g nl l
           (WF : wf g),
      has_edge o e d1 (IntMap.add (fresh g) (nl, l) (edges g)) <->
        has_edge o e d1 (edges g) \/
          (o = fresh g /\ In_eq eqEN (e,d1) l).
  Proof.
    unfold has_edge ; intros.
    split; intros.
    - destruct H as (nl1 & l1 & FIND & IN).
    rewrite IntMap.find_add in FIND.
    destruct (Int.eq_dec o (fresh g)).
    * inv FIND.
      tauto.
    * left.
      do 2 eexists; split; eauto.
    - destruct H as [FIND| IN].
      +
      destruct FIND as (nl1 & l1 & FIND & IN).
      rewrite IntMap.find_add.
      destruct (Int.eq_dec o (fresh g)).
      * subst.
      assert (E : has_edge (fresh g) e d1 (edges g)).
      {
        do 2 eexists. split; eauto.
      }
      apply has_edge_label in E.
      destruct E as (lb & LB).
      apply wf_fresh in LB;auto.
      lia.
      * do 2 eexists; split;eauto.
      + destruct IN ; subst.
        rewrite IntMap.find_add.
        destruct (Int.eq_dec (fresh g) (fresh g)); try congruence.
        do 2 eexists ; split ; eauto.
  Qed.

  Lemma has_edge_mkroot : forall o e d1 lb,
      has_edge o e d1 (edges (mkroot lb)) <-> False.
  Proof.
    intros.
    unfold mkroot.
    simpl.
    unfold has_edge.
    split ; try tauto.
    intros (nl & l & FIND).
    rewrite IntMap.find_add in FIND.
    rewrite IntMap.find_empty in FIND.
    destruct (Int.eq_dec o 0).
    destruct FIND. inv H.
    simpl in H0. tauto.
    intuition congruence.
  Qed.

  Lemma has_edge_rev_mkroot : forall o e d lb,
      has_edge_rev o e d (parent (mkroot lb)) <-> False.
  Proof.
    intros.
    unfold mkroot.
    simpl.
    unfold has_edge_rev.
    split ; try tauto.
    intros (nl & FIND).
    rewrite IntMap.find_empty in FIND.
    intuition congruence.
  Qed.

  Lemma has_node_label_mkroot : forall o nl lb,
      has_node_label o nl (edges (mkroot lb)) <-> o = 0%int63 /\ NodeLabel.eq nl lb.
  Proof.
    unfold has_node_label.
    split ; intros.
    - destruct H as (ed & nl1 & FIND & EQ).
      unfold mkroot in FIND.
      simpl in FIND.
      rewrite IntMap.find_add in FIND.
      destruct (Int.eq_dec o 0).
      + subst. inv FIND.
        tauto.
      + rewrite IntMap.find_empty in FIND.
        discriminate.
    - destruct H ; subst.
      exists nil,lb.
      unfold mkroot ; simpl.
      rewrite IntMap.find_add.
      destruct (Int.eq_dec 0 0); try congruence.
      intuition congruence.
  Qed.

  Lemma has_node_label_rev_mkroot : forall o nl lb,
      has_node_label_rev o nl (nodelabels (mkroot lb)) <-> o = 0%int63 /\ NodeLabel.eq nl lb.
  Proof.
    unfold has_node_label_rev.
    intros.
    unfold mkroot;simpl.
    unfold NLMap.findl.
    rewrite NLMap.find_add.
    destruct (NodeLabel.eq_dec nl lb).
    - simpl. intuition congruence.
    - rewrite NLMap.find_empty.
      simpl. intuition congruence.
  Qed.


  Lemma wf_mkroot : forall lb, wf (mkroot lb).
  Proof.
    constructor; intros.
    - rewrite has_edge_mkroot in H.
      tauto.
    - rewrite has_edge_mkroot in H.
      tauto.
    - rewrite has_edge_mkroot.
      rewrite has_edge_rev_mkroot.
      tauto.
    - rewrite has_node_label_mkroot.
      rewrite has_node_label_rev_mkroot.
      tauto.
    -  split; [simpl; tauto|].
      intro H. destruct H.
      rewrite has_edge_mkroot in H.
      tauto.
    - rewrite has_node_label_mkroot in H.
      unfold mkroot. simpl.
      lia.
  Qed.




  Definition int_overflow {A: Type} := Error (A:= A) (cons (MSG "fresh has reached max_int"%string) nil).

  Fixpoint register_edgelabels (n:int) (l:list (EdgeLabel.t * int)) (m:ELMap.t (list int))  :=
    match l with
    | nil => m
    | cons (e,_) l => ELMap.add_from_list  e n  (register_edgelabels n l m)
    end.

  Definition register_parents (n:int) (l:list (EdgeLabel.t * int)) (m: IntMap.t (EdgeLabel.t * int)) :=
    List.fold_right (fun '(e,n') m => IntMap.add n' (e,n) m) m l.

  Definition remove_parents (n:int) (l:list (EdgeLabel.t * int)) (m: IntMap.t (EdgeLabel.t * int)) :=
    List.fold_right (fun '(e,n') m => IntMap.remove n'  m) m l.


  (* [create_node n l g] creates a fresh node with label [n] and successors [l] *)

  Definition create_node (n:NodeLabel.t) (l:list (EdgeLabel.t * int)) (g:t) : res (t* int) :=
    let fr := fresh g in
    if eqb fr max_int
    then int_overflow
    else
      OK (mk
            (root g)
            (* add the node - no successor *)
            (IntMap.add fr (n,l) (edges g))
            (register_parents fr l (parent g))
            (* register the label *)
            (NLMap.add_from_list n fr (nodelabels g))
            (register_edgelabels fr l (edgelabels g))
            (fr + 1),fr).

  Definition swap_pair {A B:Type} (e : A * B) := (snd e, fst e).

  Lemma find_register_parents :
    forall n l m,
      forall n',
        IntMap.find n' (register_parents n l m) = match find_node n' l with
                                                  | None => IntMap.find n' m
                                                  | Some e => Some (e,n)
                                                  end.
  Proof.
    unfold register_parents.
    induction l.
    - simpl. auto.
    -  simpl.
       destruct a as (e1,n1).
       intros.
       rewrite IntMap.find_add.
       destruct (Int.eq_dec n' n1).
       + subst. reflexivity.
       + rewrite IHl.
         reflexivity.
  Qed.





  Lemma find_node_Some : forall n l e,
      find_node n l = Some e -> In (e,n) l.
  Proof.
    induction l; simpl.
    - discriminate.
    - destruct a.
      destruct (Int.eq_dec n i).
      intuition congruence.
      intros.
      apply IHl in H. intuition congruence.
  Qed.


 Lemma find_node_None : forall n l e,
      find_node n l = None ->
      In (e, n) l -> False.
  Proof.
    induction l; simpl; intros; auto.
    destruct a.
    destruct (Int.eq_dec n i);try discriminate.
    destruct H0. congruence.
    eapply IHl;eauto.
  Qed.


  
  Lemma has_edge_rev_add :
    forall  g l
            (WF : wf g)
            (NODUP2 : forall e1 e2 d, In (e1,d) l -> In (e2,d) l -> e1 = e2)
            (NOPARENT : forall o e1 e2 n, In (e1,n) l -> has_edge o e2 n (edges g) -> False)
           o e d,
    has_edge_rev o e d (register_parents (fresh g) l (parent g)) <->
      (has_edge_rev o e d (parent g) \/ (o = fresh g /\ In_eq eqEN (e,d) l)).
  Proof.
    unfold has_edge_rev at 1.
    intros.
    rewrite find_register_parents.
    destruct (find_node d l) eqn:FIND.
    - apply find_node_Some in FIND.
      split ; intros.
      + inv H.
        destruct H0. inv H.
        right; split;auto.
        apply In_eq_eq with (e1:=(x,d)).
        apply eqEN_sym.
        apply eqEN_trans.
        unfold eqEN; simpl; auto.
        split;auto. apply EdgeLabel.eq_sym ;auto.
        apply In_In_eq;auto.
        apply eqEN_refl;auto.
      + destruct H.
        rewrite <- wf_parent in H; auto.
        exfalso. eapply NOPARENT;eauto.
        destruct H. exists t0.
        split.
        congruence.
        rewrite In_eq_iff in H0.
        destruct H0 as (e' & EQ & IN).
        destruct e' as (e',d1).
        unfold eqEN in EQ. simpl in EQ.
        destruct EQ ; subst.
        assert (e' = t0).
        eapply NODUP2;eauto.
        subst. auto.
    -  split; intros.
       unfold has_edge_rev.
       tauto.
       destruct H.
       apply H.
       destruct H.
       exfalso.
       apply In_eq_iff in H0.
       destruct H0 as (e' & EQ & IN).
       destruct e'. unfold eqEN in EQ.
       simpl in *. destruct EQ; subst.
       eapply find_node_None;eauto.
  Qed.



  Lemma has_node_label_add : forall o lb lb' l g
                                    (WF : wf g),
      has_node_label o lb (IntMap.add (fresh g) (lb', l) (edges g))  <->
        (has_node_label o lb (edges g) \/ o = fresh g /\ NodeLabel.eq lb  lb').
  Proof.
    intros.
    unfold has_node_label at 1.
    rewrite IntMap.find_add.
    destruct (Int.eq_dec o (fresh g)).
    - split;intros.
      destruct H as (l1 & nl & FIND & EQ).
      inv FIND. tauto.
      destruct H.
      apply wf_fresh in H ; auto.
      lia.
      exists l, lb'. intuition congruence.
    - split; intros.
      left; auto.
      destruct H; auto.
      intuition congruence.
  Qed.

  Lemma has_node_label_rev_add :
    forall o lb lb' g
           (WF: wf g)
    ,
      has_node_label_rev o lb (NLMap.add_from_list lb' (fresh g) (nodelabels g)) <->
        (has_node_label_rev o lb (nodelabels g) \/ (o = fresh g /\ NodeLabel.eq lb lb')).
  Proof.
    intros.
    unfold has_node_label_rev at 1.
    unfold NLMap.findl.
    unfold NLMap.add_from_list.
    rewrite NLMap.find_add.
    destruct (NodeLabel.eq_dec lb lb').
    - unfold has_node_label_rev.
      unfold NLMap.findl.
      rewrite NLMap.find_eq with (k2:= lb).
      destruct (NLMap.find (elt:=list int) lb (nodelabels g)) eqn:FIND.
      + simpl.
        intuition congruence.
      + simpl.
        intuition congruence.
      + apply NodeLabel.eq_sym;auto.
    - unfold has_node_label_rev.
      unfold NLMap.findl.
      destruct (NLMap.find (elt:=list int) lb (nodelabels g)) eqn:FIND.
      intuition.
      simpl. tauto.
  Qed.

  Lemma find_label_None : forall  e l, find_label e l = None ->
                                       In_eq EdgeLabel.eq e (map fst l) -> False.
  Proof.
    induction l ; simpl; auto.
    destruct a.
    destruct (EdgeLabel.eq_dec e t0).
    discriminate.
    simpl.
    intros.
    destruct H0.
    tauto.
    tauto.
  Qed.

  Lemma find_label_Some : forall  e d l, find_label e l = Some d ->
                                      exists e', In (e',d) l /\ EdgeLabel.eq e e'.
  Proof.
    induction l ; simpl; auto.
    - congruence.
    - destruct a.
      destruct (EdgeLabel.eq_dec e t0).
      intros.
      inv H.
      exists t0. tauto.
      intros. apply IHl in H.
      destruct H. exists x. tauto.
  Qed.


  Lemma findl_register_edgelabels :
    forall g l e
           (NODUP1 : NoDup_eq EdgeLabel.eq (map fst l))
           (NODUP2 : NoDup (map snd l)),
      (ELMap.findl e (register_edgelabels (fresh g) l (edgelabels g))) =
        match find_label e l with
        | None => ELMap.findl e (edgelabels g)
        | Some n => fresh g :: ELMap.findl e (edgelabels g)
        end.
  Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl in *.
      inv NODUP1.
      inv NODUP2.
      destruct a as (e1,n1).
      simpl in *.
      destruct (EdgeLabel.eq_dec e e1).
      + specialize (IHl H2 H4).
      rewrite ELMap.findl_eq by auto.
      rewrite find_label_eq with (lb' := e1) in IHl by auto.
      rewrite find_label_not_In in IHl by auto.
      congruence.
      + rewrite ELMap.findl_neq by auto.
        auto.
  Qed.

    
  Lemma wf_create_node :
    forall nl l g g1 n
           (NODUP1 : NoDup_eq EdgeLabel.eq (map fst l))
           (NODUP2 : NoDup (map snd l))
           (NODUP2 : forall e1 e2 d, In (e1,d) l -> In (e2,d) l -> e1 = e2)
           (NOEDGE : forall e1 e2 o d, has_edge o e1 d (edges g) -> In_eq eqEN (e2,d) l -> False)
           (WF : wf g)
    ,
      create_node nl l g = OK(g1,n) ->
      wf g1 /\ n = fresh g /\
        (forall o e d,
          has_edge o e d (edges g) -> has_edge o e d (edges g1))
      /\
        has_node_label n nl (edges g1) /\
        forall e d, In (e,d) l -> has_edge n e d (edges g1).
  Proof.
    unfold create_node.
    intros.
    destruct ((fresh g =? max_int)%uint63) eqn:FR ; try discriminate.
    inv H.
    split.
    - constructor.
      + simpl; intros; simpl in *.
        rewrite has_edge_add in H; auto.
        rewrite has_edge_add in H0;auto.
        destruct H ; destruct H0.
        * eapply WF; eauto.
        * destruct H0.
          apply has_edge_label in H.
          destruct H.
          apply wf_fresh in H; auto.
          lia.
        * destruct H.
          apply has_edge_label in H0.
          destruct H0.
          apply wf_fresh in H0; auto.
          lia.
        *
          destruct H; destruct H0.
          eapply NoDup_map; eauto.
          apply EdgeLabel.eq_sym.
          apply EdgeLabel.eq_trans.
      + simpl.
        intros.
        rewrite has_edge_add in H; auto.
        rewrite has_edge_add in H0;auto.
        destruct H; destruct H0.
        * eapply WF;eauto.
        * destruct H0; subst.
          exfalso.
          eapply NOEDGE;eauto.
        * destruct H.  exfalso.
          eapply NOEDGE;eauto.
        * destruct H,H0; split; auto.
          congruence.
          eapply NoDup_map_snd ;eauto.
          apply EdgeLabel.eq_sym.
          apply EdgeLabel.eq_trans.
      + simpl.
        intros.
        rewrite has_edge_add;auto.
        rewrite has_edge_rev_add;auto.
        rewrite wf_parent by auto.
        tauto.
        intros.
        eapply NOEDGE;eauto.
        apply In_In_eq.
        apply eqEN_refl.
        apply H.
      + simpl.
        intros.
        rewrite has_node_label_add by auto.
        rewrite has_node_label_rev_add by auto.
        rewrite wf_nl by auto.
        tauto.
      +  simpl.
         intros.
         rewrite findl_register_edgelabels.
         destruct (find_label  e l) eqn:FIND.
         * simpl.
           rewrite wf_el.
           apply find_label_Some in FIND.
           split; intros.
           destruct H.
           destruct FIND as (e' & IN & EQ).
           exists i.
           rewrite has_edge_add by auto.
           right.
           split;try congruence.
           rewrite In_eq_iff.
           exists (e',i).
           split;auto.
           split. simpl;auto.
           reflexivity.
           destruct H as (d & EDGE).
           exists d.
           rewrite has_edge_add by auto.
           tauto.
           destruct H as ( d & ADD).
           rewrite has_edge_add in ADD by auto.
           destruct ADD. right. exists d ; auto.
           left ; intuition congruence.
           auto.
           * rewrite wf_el by auto.
             split ; intros.
             destruct H. exists x.
             rewrite has_edge_add by auto.
             tauto.
             destruct H.
             rewrite has_edge_add in H by auto.
             destruct H. exists x; auto.
             exfalso.
             eapply find_label_None;eauto.
             change e with (fst (e,x)).
             eapply In_eq_map  with (eqA := eqEN).
             unfold eqEN. tauto.
             tauto.
           * auto.
           * auto.
      + simpl.
        intros.
        rewrite has_node_label_add in H by auto.
        destruct H.
        apply wf_fresh in H;auto. lia.
        lia.
    -  simpl.
       repeat split;auto.
       + intros.
         rewrite has_edge_add by auto.
         tauto.
       + rewrite has_node_label_add by auto.
         right.
         split;auto. apply NodeLabel.eq_refl.
       + intros.
         rewrite has_edge_add by auto.
         right;auto.
         split;auto.
         apply In_In_eq.
         apply eqEN_refl. auto.
  Qed.

  (* [add_edge n1 el n2 g] add a new edge beteeen 2 existing nodes n1 and n2 *)
  Definition add_edge (n1:int) (el:EdgeLabel.t) (n2:int) (g:t) : res t :=
    match IntMap.find n1 (edges g) with
    | None => Error (cons (MSG "add_edge: origin node does not exist") nil)
    | Some (nl,l) =>
        let ns := cons n1 (match ELMap.find el (edgelabels g) with
                           | None => nil
                           | Some l => l
                           end) in
        OK (mk (root g) (IntMap.add n1 (nl,cons (el,n2) l) (edges g))
               (register_parents n1 ((el,n2)::nil) (parent g))
              (nodelabels g)
                             (ELMap.add el ns (edgelabels g))
                             (fresh g))
    end.

  (** [create_path nlabel n nl [e1,...,en] g] creates a path n -> e1 -> ... -> en in the graph g.
      nodes are created if needed.
      This is a generalised get_field.
   *)

  Fixpoint create_path (next_label : NodeLabel.t -> EdgeLabel.t -> res NodeLabel.t)
    (n:int)  (l:list EdgeLabel.t) (g:t) : res (t * (int * NodeLabel.t)) :=
    match IntMap.find n (edges g) with
    | None => Error (MSG "create_path: origin node " ::  MSG (string_of_int n) :: MSG " does not exist" :: nil)
    | Some(nl,succs) => match l with
                        | nil => OK (g,(n,nl))
                        | e::l =>
                            match find_label e succs with
                            | Some n' => create_path next_label n' l g (* following path *)
                            | None    =>
                                (* the edge does not exists *)
                                let* lb :=  next_label nl e in
                                let* (g',nn) := create_node lb nil g in
                                let* g2      := add_edge n e nn g' in
                                create_path next_label nn l g2
                            end
                        end
    end.

  Fixpoint remove_edges (n:int) (l:list (EdgeLabel.t * int)) (lb:ELMap.t (list int) ) : ELMap.t (list int) :=
    match l with
    | nil => lb
    | (el,_)::l => ELMap.remove_from_list (eqb_of_dec Int.eq_dec) el n (remove_edges n l lb)
    end.

  Definition remove_node (n:int) (g:t) : t:=
    match IntMap.find n (edges g) with
    | None => g
    | Some(nl,l) => mk (root g) (IntMap.remove n (edges g))
                       (remove_parents n l (parent g))
                      (NLMap.remove_from_list (eqb_of_dec Int.eq_dec) nl n (nodelabels g))
                      (remove_edges n l (edgelabels g)) (fresh g)
    end.

  Definition eqb_edge_node (e1_n1 e2_n2:EdgeLabel.t * int) : bool :=
    if EdgeLabel.eq_dec (fst e1_n1) (fst e2_n2)
    then eqb_of_dec Int.eq_dec (snd e1_n1) (snd e2_n2)
    else false.

  Definition remove_edge_from_list (o:int)  (e:EdgeLabel.t) (d:int) (m:IntMap.t (NodeLabel.t * list (EdgeLabel.t * int))) :=
    match IntMap.find o m with
    | None => m
    | Some(nl,l) => IntMap.add o (nl,List_remove eqb_edge_node (e,d) l) m
    end.

  Definition remove_edge (o:int) (e:EdgeLabel.t) (d:int) (g:t) :=
    mk (root g) (remove_edge_from_list o e d (edges g))
       (IntMap.remove d (parent g))
      (nodelabels g)
       (remove_edges o ((e,d)::nil) (edgelabels g))
       (fresh g).


  Section REMOVETREE.
    Variable remove_tree_rec : int -> t -> res (t * list int).

    Definition remove_trees_rec (l : list (EdgeLabel.t * int)) (g:t) :=
      List.fold_right (fun e acc =>
                         let* (g,l) := acc in
                         let* (g,l1) := remove_tree_rec (snd e) g in
                         OK (g, app l l1)) (OK (g,nil)) l.
  End REMOVETREE.

  Fixpoint remove_tree_aux (fuel: nat) (n:int) (g:t) : res (t * list int)  :=
    match fuel with
    | O => Error (cons (MSG "remove_tree: not enough fuel") nil)
    | S fuel =>
        match IntMap.find n (edges g) with
        | None => Error (cons (MSG "remove_tree: unbound node") nil)
        | Some(nl,l) => let* (t,lr) := remove_trees_rec (remove_tree_aux fuel) l g in

                        OK(remove_node n t,n::lr)
        end
    end.

  Definition remove_successor (n:int) (e:EdgeLabel.t) (n':int) (g:t) :=
    match IntMap.find n (edges g) with
    | None => OK (g,nil)
    | Some(nl,_) =>
        let g := remove_edge n e n' g in
        remove_tree_aux (NodeLabel.depth nl)  n' g
    end.



  Fixpoint remove_successors  (n:int) (l : list (EdgeLabel.t * int)) (g:t) :=
    match l with
    | nil => OK (g,nil)
    | cons (e,n1) l =>
        let* (g1,l1) := remove_successors n l g in
        let* (g2,l2) := remove_successor n e n1 g1 in
        OK (g2, List.app l1 l2)
    end.

  Section UPDATE.
    Variable classify_edge : EdgeLabel.t -> EdgeLabel.t -> cedge.

    Fixpoint partition_edges (e: EdgeLabel.t) (l: list (EdgeLabel.t * int)) :
      (list (EdgeLabel.t * int) * list (EdgeLabel.t * int) * list (EdgeLabel.t * int)) :=
      match l with
      | nil => (nil,nil,nil)
      | cons e' l' =>
          let '((mst,may),nmay) := partition_edges e l' in
          match classify_edge e (fst e') with
          | MUST => (cons e' mst,may,nmay)
          | MAY  => (mst,cons e' may, nmay)
          | NOTMAY => (mst, may,nmay)
          end
      end.

    Fixpoint find_edge (e:EdgeLabel.t) (l:list (EdgeLabel.t * int)) : option int :=
      match l with
      | nil => None
      | (e1,i) ::l1 => if EdgeLabel.eq_dec e e1 then Some i else find_edge e l1
      end.

    

    Fixpoint check_must_alias (fuel:nat) (o:int) (l:list EdgeLabel.t) (n:int) (g:t) : res unit :=
      match l with
      | nil => if eqb o n then OK tt
               else Error (cons (MSG "check_must_alias: cannot check must alias") nil)
      | cons e l =>
          match IntMap.find o (edges g) with
          | None => Error (cons (MSG "check_must_alias: invalid node") nil)
          | Some (nl,edges) =>
              match find_edge e edges with
              | Some o' => check_must_alias fuel o' l n g
              | _     =>
                  let g := Draw.pp (Bcat (Bstr (string_of_int o)) (Bcat (pp g) (Bstr (string_of_int n))))in
                  Error (cons (MSG "check_must_alias: cannot find must alias") (cons (MSG Draw.nl) (cons (MSG g) nil)))
              end
          end
      end.

  End UPDATE.

  Definition merge_edge (e1 e2: NodeLabel.t * list (EdgeLabel.t * int)) :=
    (fst e1, List.app (snd e1) (snd e2)).

  Definition merge_parent (e1 e2:EdgeLabel.t * int) := e1.

  Definition union (g1:t) (g2:t) :=
    mk (root g1) (IntMap.union merge_edge (edges g1) (edges g2))
       (IntMap.union merge_parent (parent g1) (parent g2))
      (NLMap.union (@List.app _) (nodelabels g1) (nodelabels g2))
      (ELMap.union (@List.app _) (edgelabels g1) (edgelabels g2))
      (max (fresh g1) (fresh g2)).

  Definition interT := (t * (IntMap.t int * IntMap.t int))%type.

  Definition rootI (x:interT) : int :=
    let '(g,_) := x in root g.

  Section INTER.
    Variable inter : int -> t -> int -> t -> interT -> res interT.

    Fixpoint inter_list  (l1 :list (EdgeLabel.t * int)) (g1:t) (l2: list (EdgeLabel.t * int)) (g2:t) (acc:interT) :
      res ((list (EdgeLabel.t * int)) * interT) :=
      match l1 with
      | nil => OK (nil, acc)
      | cons (e,n) l1' =>
          match find_label e l2 with
          | None => inter_list l1' g1 l2 g2 acc
          | Some n' =>
              let* ga := inter n g1 n' g2 acc in
              let* (l,g) := inter_list l1' g1 l2 g2 ga in
              OK ((e, rootI ga) :: l,g)
          end
      end.

  End INTER.

  Definition set_root (n:int) (g:t) :=
    mk n (edges g) (parent g) (nodelabels g) (edgelabels g) (fresh g).

  Definition create_root (n1:int) (n2:int) (lb:NodeLabel.t) (l:list (EdgeLabel.t * int)) (g:interT) :=
    let '(g,(m1,m2)) := g in
    let* (g,n') := create_node lb l g in
    OK (set_root n' g, (IntMap.add n1 n' m1, IntMap.add n2 n' m2)).


  Fixpoint inter (fuel:nat) (o1:int) (g1:t) (o2:int) (g2:t) (acc:interT) : res interT :=
    match fuel with
    | O => fail
    | S fuel => match IntMap.find o1 (edges g1), IntMap.find o2 (edges g2) with
                | None , _ | _ , None => fail
                | Some(lb1,l1) , Some(lb2,l2) =>
                    if NodeLabel.eq_dec lb1 lb2
                    then
                      let* (l,g) := inter_list (inter fuel) l1 g1 l2 g2 acc in
                      create_root o1 o2 lb1 l g
                    else fail
                end
    end.

  Definition subst_edge (e:EdgeLabel.t) (e': EdgeLabel.t) (l: list (EdgeLabel.t * int)) : list (EdgeLabel.t * int) :=
    List.map (fun x => if EdgeLabel.eq_dec e (fst x) then (e',snd x) else x) l.

  (* We assume the there is an edge (o -[e]-> d) in g *)
  Definition update_edge (o:int) (e:EdgeLabel.t) (e':EdgeLabel.t) (g:t) :=
    if EdgeLabel.eq_dec e e'
    then g (* Nothing to do *)
    else
      match IntMap.find o (edges g) with
      | None => g
      | Some (nl,el) =>
          let el' := subst_edge e e' el in
          mk (root g) (IntMap.add o (nl,el') (edges g))
             (register_parents o el' (parent g))
            (nodelabels g)
            (ELMap.add_from_list  e' o
               (ELMap.remove_from_list (eqb_of_dec Int.eq_dec) e o (edgelabels g)))
            (fresh g)
      end.


  Definition update_edges (l:list int) (e:EdgeLabel.t) (e': EdgeLabel.t) (g:t) :=
    List.fold_right (fun o g => update_edge o e e' g) g l.


  Definition update_edgelabel (e e':EdgeLabel.t) (g:t) : t :=
    match ELMap.find e (edgelabels g) with
    | None => g
    | Some l => update_edges l e e' g
    end.

  Fixpoint nodes (fuel:nat) (o:int) (g:t) : res IntSet.t :=
    match fuel with
    | O => fail
    | S fuel =>
        match IntMap.find o (edges g) with
        | None => OK IntSet.empty
        | Some (_,l) => List.fold_right (fun en s =>
                                           let* s   := s in
                                           let* s1 := (nodes fuel (snd en) g) in
                                                     OK (IntSet.union s1  s)) (OK (IntSet.singleton o)) l
        end
    end.

  Definition non_alias (fuel:nat) (n1 n2:int) (g:t) :=
    match nodes fuel n1 g , nodes fuel n2 g with
    | OK s1   , OK s2 => IntSet.is_empty (IntSet.inter s1 s2)
    |  _      , _     => false
    end.

  Fixpoint is_parent_rec (g:t) (fuel:nat) (p:int) (n:int)  :=
    if eqb p n then OK true
    else
    match fuel with
    | O => fail
    | S fuel' =>
        match IntMap.find n (parent g) with
        | None => OK false
        | Some(_,n1) => is_parent_rec g fuel' p n1
        end
    end.

  Definition is_parent (g:t) (p:int) (n:int) :=
    let* d:= depth g in
    is_parent_rec g d p n.


  Fixpoint get_upward_path_rec (fuel:nat) (g:t) (n:int) :=
    if Int.eq_dec n (root g) then OK nil
    else match fuel with
         | O => fail
         | S fuel =>
             match IntMap.find n (parent g) with
             | None => fail (* Should not happen *)
             | Some(e,p) => let* path := get_upward_path_rec fuel g p in
                            OK (e::path)
             end
         end.

  Definition get_path (g:t) (n:int) :=
    let* lb := get_label g (root g) in
    let* path := get_upward_path_rec (NodeLabel.depth lb) g n in
    OK (List.rev path).

  Inductive is_tree_node (g:t) : int -> Prop :=
  | Leaf : forall n,
    (forall e n', In (e,n') (get_successors g n) -> is_tree_node g n') -> is_tree_node g n.

  Definition is_tree (g:t) :=
    forall n, is_tree_node g n.

End Make.
