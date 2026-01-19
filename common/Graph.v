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

From BarocqComp Require Import Error Maps2 Utils Pp.

Inductive classify_edge :=
| MUST
| MAY
| NOTMAY.

Definition eqb_of_dec {A: Type} (eq_dec:forall (x y:A), {x = y}+{x <> y}) : A -> A -> bool :=
  fun x y => if eq_dec x y then true else false.


(*Fixpoint In_eq {A : Type} (eq : A -> A -> Prop) (e:A) (l:list A) :=
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
 *)
(*
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
*)

Lemma NoDup_map : forall {A B:Type} (l:list (A * B)),
    NoDup (map fst l) ->
    forall e d1 d2,
    In (e, d1) l ->
    In (e, d2) l ->
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
      apply in_map with (f:=fst) in H0.
      simpl in H0.
      tauto.
    + inv H0.
      apply in_map with (f:=fst)  in H.
      simpl in H. tauto.
    +  eapply IHl;eauto.
Qed.

Lemma NoDup_map_snd : forall {A B:Type}  (l:list (A * B)),
    NoDup (map snd l) ->
    forall e1 e2 d,
    In (e1, d) l ->
    In (e2, d) l ->
    e1 = e2.
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
      apply in_map with (f:=snd)  in H0.
      simpl in H0. tauto.
    + inv H0.
      apply in_map with (f:=snd) in H.
      simpl in H.
      tauto.
    +  eapply IHl;eauto.
Qed.


Section FORALL.
  Context {A: Type}.
  Variable P : A -> Prop.

  Fixpoint Forall (l:list A) : Prop :=
    match l with
    | nil => True
    | e::l => P e /\ Forall l
    end.

End FORALL.




Section ListREMOVE.
  Context {A: Type}.
  Variable eqb : A -> A -> bool.

  Fixpoint List_remove (e:A) (l:list A) : list A :=
    match l with
    | nil => nil
    | e1 :: l => if eqb e e1 then List_remove e l
                 else e1 :: List_remove e l
    end.

  Fixpoint List_remove_assoc {B:Type} (e:A) (l:list (A *B)) : list (A*B) :=
    match l with
    | nil => nil
    | (e1,v1) :: l => if eqb e e1 then l
                 else (e1,v1) :: List_remove_assoc e l
    end.

  Lemma In_remove_assoc_In : forall {B:Type} e e' (v:B) l ,
    In (e, v) (List_remove_assoc e'  l) -> In (e,v) l.
  Proof.
    induction l; simpl; auto.
    destruct a. destruct (eqb e' a).
    tauto.
    simpl ; intros.
    tauto.
  Qed.



  Fixpoint List_in (e:A) (l:list A) :=
    match l with
    | nil => False
    | e1::l => eqb e e1 = true \/ List_in e l
    end.

  Lemma List_remove_not_In : forall  (k:A) l,
    (forall x, eqb k x = false -> k <> x) ->
      In k (List_remove k l) <-> False.
  Proof.
    induction l ; simpl.
    -  tauto.
    -  destruct (eqb k a) eqn:EQ.
       intros.
       rewrite IHl. tauto. auto.
       simpl. intros.
       apply H in EQ.
       rewrite IHl by auto.
       intuition congruence.
  Qed.

  Lemma List_remove_neq : forall
      (EQ : forall x x', eqb x x' = true -> x = x')
      (k k':A)  (NEQ : k <> k') l,

      In k (List_remove k' l) <-> In k l.
  Proof.
    induction l ; simpl.
    -  tauto.
    -  destruct (eqb k' a) eqn:EQ1.
       + apply EQ in EQ1. subst.
       intuition congruence.
       + simpl.
         intuition congruence.
  Qed.


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

  Definition addl {elt:Type}   (k:key) (e:elt) (m : t (list elt)) : t (list elt) :=
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
      findl k1 (addl k2 x m) = x:: (findl k1 m).
  Proof.
    unfold findl,addl.
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
      findl k1 (addl k2 x m) = (findl k1 m).
  Proof.
    unfold findl,addl.
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

  Lemma findl_remove : forall {A: Type} (eqb: A -> A -> bool) n n' k m,
      findl n (remove_from_list eqb n' k m) =
        if O.eq_dec n n'
        then List_remove eqb k (findl n m)
        else findl n m.
  Proof.
    intros.
    unfold remove_from_list.
    destruct (find  n' m) eqn:FIND.
    unfold findl.
    rewrite find_add.
    destruct (O.eq_dec n n').
    rewrite Facts.find_o with (y:= n') by auto.
    rewrite FIND. reflexivity.
    reflexivity.
    destruct (O.eq_dec n n').
    unfold findl.
    rewrite Facts.find_o with (y:= n') by auto.
    rewrite FIND. reflexivity.
    auto.
  Qed.


End Map.

Module IntMap := Map(Int).

Module Type NodeLabelT.
  Axiom t : Type.
  Axiom lt: t -> t -> Prop.
  Definition eq:= @eq t.
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
  Definition eq:= @eq t.
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
      nodelabels : NLMap.t (list int) ; (* nodes with a given label *)
      edgelabels : ELMap.t (list int) ; (* nodes which edges have a given label *)
      fresh      : int; (* fresh node *)
    }.

  Definition path := list (EdgeLabel.t).

  Definition is_prefix (pre:path) (p:path) :=
    exists post, pre ++ post = p.

  Lemma is_prefix_nil_l : forall p, is_prefix [] p <-> True.
  Proof.
    intros.
    split; auto.
    exists p. reflexivity.
  Qed.

  Lemma is_prefix_nil_r : forall p, is_prefix p [] <-> p = nil.
  Proof.
    intros.
    split; intros.
    destruct H.
    apply app_eq_nil in H.
    tauto.
    subst.
    apply is_prefix_nil_l.
    tauto.
  Qed.

  Lemma is_prefix_cons : forall e1 l1 e2 l2,
      is_prefix (e1 :: l1) (e2 :: l2) <-> (e1 = e2 /\ is_prefix l1 l2).
  Proof.
    unfold is_prefix ; split; intros.
    destruct H. simpl in H.
    inv H.
    split; auto. exists x;auto.
    destruct H; subst.
    destruct H0. subst.
    exists x;auto.
  Qed.

  Fixpoint find_edge {A: Type} (e:EdgeLabel.t) (l:list (EdgeLabel.t * A)) : option A :=
    match l with
    | nil => None
    | (e1,i) ::l1 => if EdgeLabel.eq_dec e e1 then Some i else find_edge e l1
    end.

  Module PathTree.
    (** Tree representing invalid paths in the abstract memory.
        A path is a list of EdgeLabel.t.
     *)

    Inductive t :=
    | Node : list (EdgeLabel.t * t) -> t.


    Fixpoint pp (tr:t) : box :=
      match tr with
      | Node l =>
          Bstack (Bstr "o")
            (pp_list (Bstr " ") (fun x => Bstack (EdgeLabel.pp (fst x)) (pp (snd x)) Middle) l) Middle
      end.


    Section IND.

      Fixpoint depth (tr:t) :=
        match tr with
          Node l =>
            match l with
            | nil => O
            | _   => S (List.fold_right (fun x acc => Nat.max (depth (snd x)) acc) O l)
            end
        end.

      Variable P : t -> Prop.

      Variable Pemp : P (Node nil).

      Variable Pin : forall lt, lt <> nil -> (forall x tr, In (x,tr) lt -> P tr) -> P (Node lt).

      Lemma tree_ind : forall (tr:t), P tr.
      Proof.
        intro.
        remember (depth tr) as n.
        revert tr Heqn.
        induction n using Wf_nat.lt_wf_ind.
        destruct n.
        - destruct tr.
          destruct l.
          auto.
          simpl. discriminate.
        - destruct tr.
          induction l.
          +  auto.
          + intros.
            apply Pin.
            congruence.
            intros.
            eapply H with (m:= depth tr).
            { assert (depth tr < depth (Node (a::l)))%nat.
              revert H0.
              generalize (a::l) as l1.
              clear.
              induction l1; simpl.
              tauto.
              intros.
              destruct H0. subst.
              unfold snd at 1.
              lia.
              apply IHl1 in H.
              simpl in H.
              destruct l1.
              lia.
              lia.
              lia.
            }
            reflexivity.
      Qed.
    End IND.

    Section S.
      Variable may_edge : EdgeLabel.t -> EdgeLabel.t -> bool.



    Section FLATTEN.
      Variable flatten : t -> list path.

      Fixpoint flatten_list (ln: list (EdgeLabel.t * t)) : list path :=
        match ln with
        | nil => nil
        | (f,tr) :: ln' => List.app (List.map (fun p => f :: p) (flatten tr)) (flatten_list ln')
        end.

    End FLATTEN.

    Fixpoint flatten (tr:t) :=
      match tr with
      | Node l => match l with
                  | nil => nil::nil
                  |  _  => flatten_list flatten l
                  end
      end.


    (*    Definition has_path (p:path) (tr:t) :=
      exists pre, In pre (flatten tr) /\ is_prefix pre p. *)

    Inductive has_dpath : path -> t -> Prop :=
    | HASP_NIL  : has_dpath nil (Node nil)
    | HASP_CONS : forall p f tr lt1 lt2, has_dpath p tr -> has_dpath (f::p) (Node (lt1 ++ ((f,tr):: lt2))).

    Lemma flatten_order : forall p l1 l2 e tr,
        In p (flatten_list flatten (l1++(e,tr) :: l2)) <-> In p (flatten_list flatten ((e,tr)::(l1 ++ l2))).
    Proof.
      induction l1.
      - simpl. tauto.
      - simpl.
        intros.
        destruct a.
        rewrite! in_app_iff.
        rewrite IHl1.
        simpl.
        rewrite! in_app_iff.
        tauto.
    Qed.

    Lemma has_dpath_flatten : forall p tr,
        has_dpath p tr -> In p (flatten tr).
    Proof.
      intros.
      induction H.
      - simpl. tauto.
      - destruct (lt1 ++ (f, tr) :: lt2) eqn:EQ.
        + apply app_eq_nil in EQ.
          intuition congruence.
        + change (flatten (Node (p0 ::l))) with
            (flatten_list flatten (p0 ::l)).
          rewrite <- EQ.
          rewrite flatten_order.
          simpl.
          rewrite in_app_iff.
          left.
          rewrite in_map_iff.
          exists p. split; auto.
    Qed.

    Definition is_empty (tr:t) :=
      match tr with
      | Node l => l = nil
      end.


    Lemma in_nil_flatten : forall tr,
        In [] (flatten tr) -> is_empty tr.
    Proof.
      destruct tr.
      destruct l.
      + simpl. auto.
      +  unfold flatten at 1.
         fold flatten.
         generalize (p :: l) as l1.
         intros. exfalso.
         induction l1.
         simpl in H. tauto.
         simpl in H.
         destruct a.
         rewrite in_app_iff in H.
         destruct H. rewrite in_map_iff in H. destruct H. intuition congruence.
         auto.
    Qed.

    Lemma in_cons_flatten_list :forall f p l,
        In (f :: p) (flatten_list flatten l) -> exists tr, In (f,tr) l /\ In p (flatten tr).
    Proof.
      induction l.
      - simpl. tauto.
      - simpl.
        destruct a as (f1,tr1).
        intros.
        rewrite in_app_iff in H.
        destruct H.
        rewrite in_map_iff in H. destruct H as (p1 & EQ & IN).
        inv EQ. exists tr1.
        tauto.
        apply IHl in H.
        destruct H as (tr & IN1 & IN2).
        exists tr. tauto.
    Qed.


    Lemma find_edge_some : forall {A: Type} e l (v:A),
        find_edge e l = Some v ->
        exists l1 l2, l = l1++(e,v)::l2.
    Proof.
      induction l; simpl;auto.
      - discriminate.
      - destruct a as (e1,v).
        intros. destruct (EdgeLabel.eq_dec e e1).
        + inv H. exists nil. exists l. unfold EdgeLabel.eq in e0. subst.
        reflexivity.
        + apply IHl in H.
          destruct H as (l1 & l2 & EQ).
          subst.
          exists ((e1,v) ::l1).
          exists l2.
          reflexivity.
    Qed.

    Lemma find_edge_some_in : forall {A: Type} e l (v:A),
        find_edge e l = Some v -> In (e,v) l.
    Proof.
      intros.
      apply find_edge_some in H.
      destruct H as (l1 & l2 & EQ).
      subst.
      rewrite in_app_iff. simpl. tauto.
    Qed.



    Lemma in_exists : forall {A: Type} (x:A) l, In x l -> exists l1 l2, l = l1 ++ x::l2.
    Proof.
      induction l; simpl.
      - tauto.
      - intros. destruct H; subst.
        exists nil,l. reflexivity.
        apply IHl in H as (l1 & l2 & EQ).
        subst. exists (a::l1),l2.
        reflexivity.
    Qed.

    Lemma has_dpath_flatten' : forall (tr:t) p ,
        In p (flatten tr) -> has_dpath p tr.
    Proof.
      induction tr using tree_ind.
      - simpl.
        intros. destruct H; try tauto.
        subst. constructor.
      - intros.
        destruct lt.
        + congruence.
        + destruct p.
          apply in_nil_flatten in H1.
          simpl in H1. discriminate.
          change (flatten (Node (p0 ::lt))) with (flatten_list flatten (p0 ::lt)) in H1.
          apply in_cons_flatten_list in H1.
          destruct H1 as (tr & IN1 & IN2).
          specialize (H0 _ _  IN1 p IN2).
          apply in_exists in IN1.
          destruct IN1 as (l1 & l2 & EQ).
          rewrite EQ. econstructor.
          auto.
    Qed.

    Definition has_path (p:path) (tr:t) :=
      exists pre, has_dpath pre tr /\ is_prefix pre p.

    Inductive has_path' : path -> t -> Prop :=
    | HASP_NIL'  : forall p, has_path' p (Node nil)
    | HASP_CONS' : forall p f tr l, has_path' p tr ->
                                          In (f,tr) l ->
                                          has_path' (f::p) (Node l).

    Lemma has_path_eq : forall p tr, has_path p tr <-> has_path' p tr.
    Proof.
      split; intros.
      - destruct H as (pre & P & PRE).
      revert p PRE.
      induction P.
      + intros. constructor.
      + intros.
        destruct p0.
        rewrite is_prefix_nil_r in PRE. discriminate.
        rewrite is_prefix_cons in PRE.
        destruct PRE ; subst.
        econstructor; eauto.
        rewrite in_app_iff; simpl; tauto.
      - induction H.
        exists nil.  split. constructor.
        rewrite is_prefix_nil_l. auto.
        destruct IHhas_path' as (pre & DP & PRE).
        apply in_exists in H0.
        destruct H0 as (l1 & l2 & EQ); subst.
        eexists.
        split.
        econstructor. apply DP.
        rewrite is_prefix_cons. split;auto.
    Qed.


    Definition get_subtree (tr:t) : list (EdgeLabel.t * t) :=
      match tr with
      | Node l => l
      end.

    Fixpoint wf (tr:t) :=
      match tr with
      | Node l => NoDup (List.map fst l) /\ Forall (fun x => wf (snd x)) l
      end.



    Lemma wf_tail : forall {a l},
        wf (Node (a :: l)) -> wf (Node l).
    Proof.
      simpl.
      intros.
      destruct H.
      inv H. tauto.
    Qed.

    Fixpoint create (p:path) : t :=
      match p with
      | nil => Node nil
      | x :: p' => Node (cons (x, create p') nil)
      end.

    Fixpoint create_with (p:path) (sp:t) : t :=
      match p with
      | nil => sp
      | x :: p' => Node (cons (x,create_with p' sp) nil)
      end.


    Lemma has_path_nil_r : forall p, has_path p (Node nil) <-> True.
    Proof.
      unfold has_path.
      split; intros;auto.
      exists nil.
      split. constructor.
      apply is_prefix_nil_l.
      auto.
    Qed.

    Lemma has_path_nil_l : forall tr, has_path nil tr <-> is_empty tr.
    Proof.
      unfold has_path.
      split; intros.
      destruct H. destruct H. rewrite is_prefix_nil_r in H0. subst.
      inv H. reflexivity.
      unfold is_empty in H.
      destruct tr. subst.
      exists nil.
      split. constructor.
      apply is_prefix_nil_r.
      reflexivity.
    Qed.

    Lemma app_elt_app : forall {A: Type} l1 (x y:A) l2, l1 ++ x :: l2 = y::nil ->
                                                        x = y/\ l1 = nil /\ l2 = nil.
    Proof.
      induction l1.
      - simpl. intros. inv H. tauto.
      -  simpl.
         intros.
         inv H.
         apply (f_equal (@List.length _)) in H2.
         simpl in H2. rewrite length_app in H2.
         simpl in H2. lia.
    Qed.




    Lemma create_correct : forall c p, has_path p (create c) <-> is_prefix c p.
    Proof.
      induction c; simpl.
      - intros.
        rewrite is_prefix_nil_l.
        split; auto.
        intro. apply has_path_nil_r;auto.
      - intro.
        destruct p.
        rewrite is_prefix_nil_r.
        rewrite has_path_nil_l.
        intuition congruence.
        rewrite is_prefix_cons.
        rewrite <- IHc. clear IHc.
        unfold has_path.
        split; intros.
        + destruct H as (pre & IN & PRE).
          inv IN.
          rewrite is_prefix_cons in PRE.
          destruct PRE as (EQ & PRE).
          subst.
          apply app_elt_app in H.
          destruct H  as ( E1 & E2 & E3).
          subst.
          split. congruence.
          inv E1.
          exists p0. tauto.
        +  destruct H; subst.
           destruct H0 as (pre & HP & PRE).
           exists (t0::pre).
           split.
           change ([(t0,create c)]) with (nil++(t0,create c) ::nil).
           constructor; auto.
           rewrite is_prefix_cons. tauto.
    Qed.


    Section UNION.
      Variable union : t -> t -> t.

      Fixpoint union_list (ln1: list (EdgeLabel.t * t)) (ln2: list (EdgeLabel.t * t)) :=
        match ln1 with
        | nil => ln2
        | (f1,t1) ::ln1' => match find_edge f1 ln2 with
                            | Some t2 => (f1, union t1 t2) ::
                                           union_list ln1' (List_remove_assoc (eqb_of_dec EdgeLabel.eq_dec) f1 ln2)
                            | None    => (f1,t1) :: union_list ln1' ln2
                            end
        end.
    End UNION.

    Fixpoint union (t1 : t) (t2 : t) : t :=
    match t1, t2 with
    | Node [], _ | _, Node [] => Node []
    | Node l1, Node l2 => Node (union_list union l1 l2)
    end.

    Fixpoint find_may_edge (e:EdgeLabel.t) (l:list (EdgeLabel.t * t)) : option t :=
      match l with
      | nil => None
      | (e1,p1) ::l1 => if may_edge e e1
                        then match find_may_edge e l1 with
                             | None => Some p1
                             | Some p2 => Some (union p1 p2)
                             end
                        else find_may_edge e l1
      end.

    Definition follow_path (p: t) (e:EdgeLabel.t) : option t :=
      match p with
      | Node nil => Some (Node nil)
      | Node l   => find_may_edge e l
      end.

    Fixpoint split_edge (fd:EdgeLabel.t) (l:list (EdgeLabel.t * t)) :=
      match l with
      | nil => (None , l)
      | (fd1,t1)::l => if EdgeLabel.eq_dec fd fd1
                       then (Some t1,l)
                       else let (v1,l1) := split_edge fd l in
                            (v1,(fd1,t1)::l1)
      end.

    Definition set_path (p:t) (fd:EdgeLabel.t) (v: option t) :=
      match p with
      | Node nil  => Some (Node nil)(* Whatever, we cannot represent this *)
      | Node l    => (* There are some valid paths *)
          let (pfd,l') := split_edge fd l in
          match v with
          | Some p => Some(Node ((fd,p)::l')) (* Strong update over the invalid paths *)
          | None   => match l' with
                      | nil => None (* We are totally valid now *)
                      |  _  => Some (Node l')
                      end
          end
      end.


    Lemma union_list_empty : forall l1 l2,
        union_list union l1 l2 = [] ->  l1 = [] /\ l2 = nil.
    Proof.
      induction l1; simpl.
      - tauto.
      - destruct a. intros.
        destruct (find_edge t0 l2) eqn:FIND.
        congruence.
        congruence.
    Qed.


    Lemma union_empty : forall t1 t2, is_empty (union t1 t2) -> is_empty t1 \/ is_empty t2.
    Proof.
      induction t1 using tree_ind.
      - simpl.  tauto.
      - destruct lt. congruence.
        destruct t2. destruct l.
        simpl. tauto.
        intros.
        exfalso.
        change (union (Node (p :: lt)) (Node (p0 :: l))) with (Node (union_list union (p::lt) (p0::l))) in H1.
        unfold is_empty in H1.
        apply union_list_empty in H1. destruct H1 ; congruence.
    Qed.

    Lemma union_union_list : forall l1 l2,
        (List.length l1 >= 1)%nat ->
        (List.length l2 >= 1)%nat ->
        union (Node l1) (Node l2) = Node (union_list union l1 l2).
    Proof.
      destruct l1,l2 ; simpl; try lia.
      reflexivity.
    Qed.

    Ltac list :=
      repeat rewrite length_app ;
      simpl.


    Lemma union_list_decomp_left :
      forall f tr l1,
        In (f,tr) l1 ->
        forall l2,
        exists tr', In (f,tr') (union_list union l1 l2) /\
                      (tr' = tr \/
                         exists tr2, In (f,tr2) l2 /\
                                       tr' = union tr tr2).
    Proof.
      induction l1.
      - simpl.
        intros. tauto.
      - simpl; intros.
        destruct H; subst.
        +
        exists (match find_edge f l2 with
                | Some t2 => union tr t2
                | None    => tr
                end).
        destruct (find_edge f l2) eqn:FIND;
        repeat eexists.
        simpl. tauto.
        apply find_edge_some_in in FIND.
        right. exists t0; tauto.
        simpl. tauto.
        tauto.
        +
          destruct a as (f1,t1).
          destruct (find_edge f1 l2).
          *
            destruct (IHl1 H (List_remove_assoc (eqb_of_dec EdgeLabel.eq_dec) f1 l2)) as (tr'& EQ & OR).
            exists tr'.
            simpl. split. tauto.
            destruct OR.
            tauto.
            destruct H0 as (tr2 & IN & EQU).
            apply In_remove_assoc_In in IN.
            right. eexists. split;eauto.
          * destruct (IHl1 H l2) as (tr'& EQ & OR).
            exists tr'.
            split. simpl. tauto.
            tauto.
    Qed.

    Lemma find_edge_app : forall {B:Type} f (l1 l2: list (EdgeLabel.t * B)),
        find_edge f (l1 ++ l2) = match find_edge f l1 with
                                 | None => find_edge f l2
                                 | Some v => Some v
                                 end.
    Proof.
      induction l1; simpl.
      - reflexivity.
      - destruct a as (e1,v).
        intros. destruct (EdgeLabel.eq_dec f e1); auto.
    Qed.

    Lemma find_remove_Some : forall {B:Type} (l1 l2:list (EdgeLabel.t * B)) x v,
        find_edge x l1 = Some v ->
        List_remove_assoc (eqb_of_dec EdgeLabel.eq_dec) x (l1 ++ l2) =
          (List_remove_assoc (eqb_of_dec EdgeLabel.eq_dec) x l1) ++ l2.
    Proof.
      induction l1;simpl;auto.
      - discriminate.
      - destruct a as( e1,v1).
        unfold eqb_of_dec.
        intros.
        destruct (EdgeLabel.eq_dec x e1);auto.
        erewrite IHl1;eauto.
    Qed.

    Lemma find_remove_None : forall {B:Type} (l1 l2:list (EdgeLabel.t * B)) x,
        find_edge x l1 = None ->
        List_remove_assoc (eqb_of_dec EdgeLabel.eq_dec) x (l1 ++ l2) =
          l1 ++ (List_remove_assoc (eqb_of_dec EdgeLabel.eq_dec) x l2).
    Proof.
      induction l1;simpl;auto.
      - destruct a. intros.
        unfold eqb_of_dec at 1.
        destruct (EdgeLabel.eq_dec x t0); try discriminate.
        rewrite IHl1; auto.
    Qed.


    Lemma union_list_decomp_right :
      forall l1 l2 f tr,
        In (f,tr) l2 ->
        exists tr',
          In (f,tr') (union_list union l1 l2) /\
            (tr' = tr \/ exists tr2, In (f,tr2) l1 /\
                                       tr' = union tr2 tr).
    Proof.
      induction l1.
      - simpl.
        intros.
        exists tr. tauto.
      - intros.
        simpl.
        destruct a as (f1,t1).
        destruct (find_edge f1 l2) eqn:FIND.
        assert (IN := H).
        apply in_exists in H.
        destruct H as (l1' & l3' & EQ).
        rewrite EQ in FIND.
        rewrite find_edge_app in FIND.
        destruct (find_edge f1 l1') eqn:FIND1.
        inv FIND.
        erewrite find_remove_Some by eauto.
        assert (IN2 : In (f,tr) (List_remove_assoc (eqb_of_dec EdgeLabel.eq_dec) f1 l1' ++ (f, tr) :: l3')).
        {
          rewrite in_app_iff.
          simpl. tauto.
        }
        destruct (IHl1 _ _ _ IN2) as (tr' & EQ & EX).
        exists tr'.
        split;auto.
        simpl. tauto.
        destruct EX. tauto.
        destruct H as (tr2 & IN3 & EQ2).
        right. exists tr2. tauto.
        simpl in FIND.
        destruct (EdgeLabel.eq_dec f1 f).
        + inv FIND.
          unfold EdgeLabel.eq in e.
          subst.
          exists (union t1 t0).
          split.
          simpl. tauto.
          right. exists t1. tauto.
        + subst.
          rewrite find_remove_None by auto.
          simpl.
          unfold eqb_of_dec at 1.
          destruct (EdgeLabel.eq_dec f1 f); try tauto.
          assert (IN2 : In (f,tr) (l1' ++ (f, tr) :: List_remove_assoc (eqb_of_dec EdgeLabel.eq_dec) f1 l3')).
        {
          rewrite in_app_iff.
          simpl. tauto.
        }
        destruct (IHl1 _ _ _ IN2) as (tr' & EQ & EX).
        exists tr'.
        split;auto.
        destruct EX. tauto.
        destruct H as (tr2 & IN3 & EQ2).
        right. exists tr2. tauto.
        + destruct (IHl1 _ _ _ H) as (tr' & EQ & EX).
          exists tr'.
          simpl. split; try tauto.
          destruct EX ; try tauto.
          right.
          destruct H0 as (tr2 & IN & EQ1).
          exists tr2. tauto.
    Qed.

    Lemma in_length : forall {A: Type} {x:A} {l},
        In x l -> (List.length l >= 1)%nat.
    Proof.
      destruct l ; simpl.
      tauto.
      lia.
    Qed.


    Lemma union_left : forall t1 t2 p,
        has_path' p t1 -> has_path' p (union t1 t2).
    Proof.
      intros.
      revert t2.
      induction H.
      - simpl. constructor.
      - intro t2. destruct t2 as [l2].
        destruct l2.
        + simpl.
          destruct l; constructor.
        + assert (LEN := in_length H0).
          rewrite union_union_list by (list ; lia).
          destruct (union_list_decomp_left f tr l H0 (p0::l2)).
          destruct H1.
          destruct H2. subst.
          econstructor ; eauto.
          destruct H2 as (tr2 & IN & EQ).
          subst.
          econstructor.  apply IHhas_path'.
          eauto.
    Qed.

    Lemma union_right : forall t1 t2 p,
        has_path' p t2 -> has_path' p (union t1 t2).
    Proof.
      intros.
      revert t1.
      induction H; intro t1.
      - destruct t1 as [l] ; destruct l; simpl; constructor.
      - destruct t1 as [l1].
        destruct l1.
        + simpl. constructor.
        + assert (LEN := in_length H0).
          rewrite union_union_list by (list ; lia).
          destruct (union_list_decomp_right (p0::l1) l _ _ H0) as (tr' & EQ & TR).
          destruct TR.
          subst. econstructor ;eauto.
          destruct H1 as (tr2 & IN & EQTR).
          subst.
          econstructor. apply IHhas_path'.
          apply EQ.
    Qed.


    Lemma has_path_cons : forall p e l,
        l <> nil ->
        has_path' p (Node l) ->
        has_path' p (Node (e :: l)).
    Proof.
      intros. inv H0.
      congruence.
      econstructor;eauto.
      simpl. tauto.
    Qed.

    Lemma union_list_decomp : forall l1 l2 f tr,
        In (f,tr) (union_list union l1 l2) ->
        In (f,tr) l1 \/ In (f,tr) l2 \/
          exists tr1 tr2, In (f,tr1) l1 /\ In (f,tr2) l2 /\
                            tr = union tr1 tr2.
    Proof.
      induction l1;simpl.
      - intros. tauto.
      - destruct a as (f1,t1).
        intros.
        destruct (find_edge f1 l2) eqn:FIND.
        simpl in H.
        destruct H.
        + inv H.
          right. right.
          do 2 eexists.
          split.
          left ; reflexivity.
          apply find_edge_some_in in FIND.
          split ; eauto.
        + apply IHl1 in H.
          destruct H as [H| [ H | H]].
          * tauto.
          * apply In_remove_assoc_In in H.
            tauto.
          * destruct H as (tr1 & tr2 & IN1 & IN2 & EQ).
            right. right.
            exists tr1,tr2.
            apply In_remove_assoc_In in IN2.
            tauto.
        + simpl in H.
          destruct H.
          inv H. tauto.
          destruct (IHl1 _ _ _ H) as [H1 | [H1 | H1]];
            try tauto.
          destruct H1 as (tr1 & tr2 & IN1 & IN2 & EQ).
          right. right.
          exists tr1,tr2.
          tauto.
    Qed.


    Lemma union_correct : forall p t1 t2,
        has_path' p (union t1 t2) -> (has_path' p t1 \/ has_path' p t2).
    Proof.
      intros.
      remember (union t1 t2) as u.
      revert t1 t2 Hequ.
      induction H.
      - intros.
        assert (EMP : is_empty (union t1 t2)).
        { rewrite <- Hequ.
          simpl. reflexivity.
        }
        apply union_empty in EMP.
        unfold is_empty in EMP.
        destruct t1,t2 ; destruct EMP ; subst.
        left ; constructor.
        right; constructor.
      - intros.
        destruct t1 as [l1].
        destruct t2 as [l2].
        assert (CL1 : (List.length l1 = O \/ List.length l1 >= 1)%nat) by lia.
        assert (CL2 : (List.length l2 = O \/ List.length l2 >= 1)%nat) by lia.
        destruct CL1.
        destruct l1 ; simpl; try discriminate.
        left ; constructor.
        destruct CL2.
        destruct l2 ; simpl; try discriminate.
        right ; constructor.
        rewrite union_union_list in Hequ by auto.
        inv Hequ.
        apply union_list_decomp in H0.
        destruct H0 as [H0 | [H0 | H0]].
        left.
        econstructor ; eauto.
        right.
        econstructor ; eauto.
        destruct H0 as (tr1 & tr2 & IN1 & IN2 & U).
        subst.
        destruct (IHhas_path' _ _ eq_refl).
        left ; econstructor;eauto.
        right ; econstructor;eauto.
    Qed.

    Fixpoint is_completely_valid_path (tr:t) (p:path) : bool :=
      match p with
      | nil => false
      | f1::p' => match tr with
                  | Node l =>
                      match l with
                      | nil => false
                      | _   =>
                          match find_edge f1 l with
                          | Some t1 => is_completely_valid_path t1 p'
                          | None    => true
                          end
                      end
                  end
      end.

    Lemma wf_find_In : forall l,
        wf (Node l) ->
        forall f tr,
        In (f, tr) l ->
        find_edge f l = Some tr.
    Proof.
      intros.
      inv H.
      clear H2.
      induction l ; simpl in *.
      - tauto.
      - destruct a as (e1,i).
        simpl in *. inv H1.
        destruct (EdgeLabel.eq_dec f e1).
        +  unfold EdgeLabel.eq in e.
           subst.
           destruct H0. congruence.
           exfalso.
           apply H3. rewrite in_map_iff.
           exists (e1,tr).
           simpl. split; auto.
        +  eapply IHl;eauto.
           unfold EdgeLabel.eq in n ; intuition congruence.
    Qed.

    Lemma Forall_forall : forall {A: Type} P (l:list A),
        Forall P l <-> (forall x, In x l -> P x).
    Proof.
      induction l;simpl.
      - tauto.
      - rewrite IHl.
        intuition.
        congruence.
    Qed.



    Lemma is_completely_valid_path_correct :
      forall p q tr
             (WF: wf tr),
        is_completely_valid_path tr p = true ->
        has_path' (p++q) tr -> False.
    Proof.
      induction p.
      - simpl. congruence.
      - intros.
        simpl in H.
        destruct tr. destruct l. congruence.
        inv H0.
        apply wf_find_In in H5;auto.
        rewrite H5 in H.
        eapply IHp with (tr:=tr);auto.
        destruct WF.
        rewrite Forall_forall in H1.
        apply find_edge_some_in in H5.
        apply H1 in H5.
        apply H5.
        apply H4.
    Qed.

    Fixpoint prefixed_by (tr:t) (p:path) :=
      match p with
      | nil => Some tr
      | f :: p' =>
          match tr with
          | Node nil => Some (Node nil)
          | Node l   => match find_edge f l with
                        | None => None
                        | Some tf => prefixed_by tf p'
                        end
          end
      end.

    Lemma prefixed_by_Some :
      forall p tr q tr'
             (WF : wf tr),
        prefixed_by tr p = Some tr' -> has_path' (p ++ q) tr -> has_path' q tr'.
    Proof.
      induction p.
      - simpl. intros. inv H. auto.
      - simpl. destruct tr. destruct l.
        + intros. inv H.
          constructor.
        + intros.
          inv H0.
          apply wf_find_In in H5; auto.
          rewrite H5 in H.
          eapply IHp with (tr:=tr);auto.
          destruct WF.
          rewrite Forall_forall in H1.
          apply find_edge_some_in in H5.
          apply H1 in H5.
          apply H5.
    Qed.

    Lemma In_NoDup_same : forall {A B:Type} x v1 v2 (l:list (A * B)),
        In (x,v1) l ->
        In (x,v2) l ->
        NoDup (List.map fst l) ->
        v1 = v2.
    Proof.
      induction l; simpl; intros.
      - tauto.
      - destruct H;destruct H0; subst.
        + congruence.
        +  simpl in H1.
           inv H1.
           exfalso.
           apply H3.
           rewrite in_map_iff.
           exists (x,v2).
           simpl. tauto.
        +  simpl in H1.
           inv H1.
           exfalso.
           apply H3.
           rewrite in_map_iff.
           exists (x,v1).
           simpl. tauto.
        +  eapply IHl;eauto. inv H1; tauto.
    Qed.

    Lemma find_edge_None : forall {A:Type} x (l:list (EdgeLabel.t * A)),
        find_edge x l = None -> forall v, In (x,v) l -> False.
    Proof.
      induction l; simpl; auto.
      destruct a as (e1,i).
      destruct (EdgeLabel.eq_dec x e1).
      discriminate.
      intros.
      destruct H0 ; subst.
      unfold EdgeLabel.eq in n. intuition congruence.
      eapply IHl; eauto.
    Qed.



    Lemma prefixed_by_None :
      forall p tr
             (WF : wf tr),
        prefixed_by tr p = None -> forall q, has_path' (p++q) tr -> False.
    Proof.
      induction p.
      - simpl. discriminate.
      - simpl. destruct tr. destruct l.
        + intros. discriminate.
        + intros.
          destruct (find_edge a (p0 :: l)) eqn:FIND.
          apply find_edge_some_in in FIND.
          assert (WFT0 : wf t0).
          {  destruct WF.
             rewrite Forall_forall in H2.
             apply H2 in FIND.
             apply FIND.
          }
          inv H0.
          assert (t0 = tr).
          { eapply In_NoDup_same; eauto.
            inv WF; auto.
          }
          subst.
          eapply (IHp _ WFT0 H).
          eauto.
          inv H0.
          eapply find_edge_None in FIND ; eauto.
    Qed.

                End  S.

  End PathTree.

  Definition get_label (E:Edge) (n:int) :=
    match IntMap.find n E with
    | None => fail
    | Some(n,_) => OK n
    end.

  Definition get_node_label (g:t) (n:int) := get_label (edges g) n.


  Definition depth (g:t) :=
    let* lb := get_label (edges g) (root g)  in
    OK (NodeLabel.depth lb).

  Definition get_successors (g:t) (n:int) :=
    match IntMap.find n (edges g) with
    | None => nil
    | Some(_,l) => l
    end.

  Fixpoint xpp (fuel:nat) (g:t) (n:int) :=
    match fuel with
    | O => Bstr (string_of_int n)
    | S fuel =>
        Bstack (Bstr (string_of_int n))
          (List.fold_right
             (fun e acc => (Bcat (Bstack (EdgeLabel.pp (fst e))
                                    (xpp fuel g (snd e)) Middle) acc)) (Bstr "") (get_successors g n)) Middle
    end.

  Definition pp (g:t) :=
    let d := match depth g with
             | OK d => d
             | _    => O
             end in
    xpp d g (root g).


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

  Definition eqEN_dec (e1 e2: EdgeLabel.t * int) : { e1 = e2 } + {e1 <> e2}.
  Proof.
    decide equality.
    apply eqs.
    apply EdgeLabel.eq_dec.
  Qed.


  Definition has_edge (o:int) (e:EdgeLabel.t) (d:int) (E:Edge) :=
    exists nl l, IntMap.find o E = Some (nl,l)
                 /\ In (e,d) l.


  Definition has_edge_rev (o:int) (e:EdgeLabel.t) (d:int) (m:IntMap.t (EdgeLabel.t * int)) :=
    IntMap.find d m = Some (e, o).

  Definition has_node_label (o:int) (nl:NodeLabel.t) (E:Edge) :=
    get_label E o = OK nl.

  Definition has_node (o:int) (E:Edge) :=
    exists nl, has_node_label o nl E.

  Lemma has_node_label_has_node : forall o nl E, has_node_label o nl E -> has_node o E.
  Proof.
    intros. eexists; eauto.
  Qed.

  
  Definition has_node_label_rev (o:int) (nl:NodeLabel.t) (lbs:NLMap.t (list int)) :=
    In o (NLMap.findl nl lbs).

  Record le_graph (g1 g2:t) := mk_le
      {
        le_node : forall n lb, has_node_label n lb (edges g1) -> has_node_label n lb (edges g2);
        le_edge : forall o e d, has_edge o e d (edges g1) -> has_edge o e d (edges g2);
        le_fresh : (fresh g1 <=? fresh g2)%uint63 = true
      }.

  Lemma le_graph_refl : forall g, le_graph  g g.
  Proof.
    intros.
    constructor; auto.
    lia.
  Qed.

  Lemma le_graph_trans : forall g1 g2 g3, le_graph g1 g2 -> le_graph g2 g3 -> le_graph g1 g3.
  Proof.
    intros.
    destruct H,H0;constructor;auto.
    lia.
  Qed.

  Definition has_edge_dec : forall o e d E,
      {has_edge o e d E} + { ~has_edge o e d E }.
  Proof.
    unfold has_edge.
    intros.
    destruct (IntMap.find (elt:=NodeLabel.t * list (EdgeLabel.t * int)) o E) as [(lb,lst)|] eqn:FIND.
    destruct (In_dec eqEN_dec (e,d) lst).
    - left. exists lb,lst.
      split;auto.
    - right.
      intro.
      destruct H as (nl&l& EQ1&EQ2).
      congruence.
    - right.
      intro.
      destruct H as (nl&l& EQ1&EQ2).
      congruence.
  Qed.

  Definition gpath := (int * list (EdgeLabel.t * int))%type.

  Definition edge (E: Edge) (o:int) (d:int) :=
    exists e, has_edge o e d E.



  Record is_tree (E : Edge) := {
    tree_no_loop : forall n, Relation_Operators.clos_trans _ (edge E) n n -> False;
    tree_parent  : forall o1 o2 e1 e2 d, has_edge o1 e1 d E -> has_edge o2 e2 d E -> o1 = o2 /\  e1 = e2;
    }.


  Section S.

    Variable next_label : NodeLabel.t -> EdgeLabel.t -> res NodeLabel.t.


    Record wf  (g:t) :=
    {
      wf_nodup  : forall o e d1 d2, has_edge o e d1 (edges g) -> has_edge o e d2 (edges g) -> d1 = d2;
      wf_tree   : is_tree (edges g);
      wf_nxt    : forall o e d lbo lbd, has_edge o e d (edges g)  ->
                                        has_node_label o lbo (edges g) ->
                                        has_node_label d lbd (edges g) ->
                                        next_label lbo e = OK lbd;
      wf_parent : forall o e d, has_edge o e d (edges g) <-> has_edge_rev o e d (parent g);
      wf_lb     : forall o e d, has_edge o e d (edges g) -> has_node d (edges g);
      wf_nl     : forall o nl, has_node_label o nl (edges g) <-> has_node_label_rev o nl (nodelabels g);
      wf_el     : forall o e, In o (ELMap.findl e (edgelabels g)) <-> exists d, has_edge o e d (edges g);
      wf_fresh  : forall o, has_node o (edges g) -> (ltb o (fresh g) = true)%int63
    }.





  Fixpoint find_edgelabel (lb:EdgeLabel.t) (l:list (EdgeLabel.t * int)) :=
    match l with
    | nil => None
    | (el,n)::l => if EdgeLabel.eq_dec lb el then Some n else find_edgelabel lb l
    end.


(*  Lemma find_label_eq : forall lb lb' (EQ: EdgeLabel.eq lb lb') l,
      find_edgelabel lb l = find_edgelabel lb' l.
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
   *)

  Lemma find_label_not_In : forall lb l,
      ~ In lb (map fst l) ->
      find_edgelabel lb l = None.
  Proof.
    induction l; simpl;auto.
    destruct a. simpl.
    destruct (EdgeLabel.eq_dec lb t0);auto.
    unfold EdgeLabel.eq in e.
    intuition congruence.
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
    discriminate.
  Qed.


  Lemma has_node_label_empty : forall o nl, has_node_label o nl (IntMap.empty _) <-> False.
  Proof.
    split ; [| tauto].
    unfold has_node_label.
    unfold get_label.
    rewrite IntMap.find_empty.
    unfold efail. discriminate.
  Qed.

  Lemma has_node_label_rev_empty : forall o nl, has_node_label_rev o nl (NLMap.empty _) <-> False.
  Proof.
    split ; [| tauto].
    unfold has_node_label_rev.
    simpl.
    auto.
  Qed.

    Lemma has_edge_node_d : forall o e d E,
      has_edge o e d E -> has_node o E.
  Proof.
    intros.
    destruct H.
    exists x. destruct H as (l & H & IN).
    unfold has_node_label,get_label.
    rewrite H. reflexivity.
  Qed.

  Lemma has_node_label_inj : forall n lb1 lb2 E,
      has_node_label n lb1 E ->
      has_node_label n lb2 E ->
      lb1 = lb2.
  Proof.
    unfold has_node_label.
    congruence.
  Qed.

  Lemma has_edge_node_label_le  :
    forall n ty el n' ty' g g'
           (LE  : le_graph g g')
           (E2 :has_edge n el n' (edges g))
           (WFG : wf g)
           (N1 :has_node_label n ty (edges g'))
           (N2 :has_node_label n' ty' (edges g')),
      has_node_label n ty (edges g) /\ has_node_label n' ty' (edges g).
  Proof.
    intros.
    split.
    exploit has_edge_node_d.
    apply E2. intros (lb & N1').
    assert (lb = ty).
    { destruct LE.
      apply le_node0 in N1'.
      eapply has_node_label_inj;eauto.
    }
    subst. auto.
    eapply wf_lb  in E2 ; eauto.
    destruct E2 as (lb & N2').
    assert (lb = ty').
    { destruct LE.
      apply le_node0 in N2'.
      eapply has_node_label_inj;eauto.
    }
    congruence.
  Qed.

  Lemma has_edge_next_label :
    forall g
           (WF: wf g) n ty ed n' ty'
           (EDGE : has_edge n ed n' (edges g))
           (ND    : has_node_label n ty (edges g))
           (NXT : next_label ty ed = OK ty'),
      has_node_label n' ty' (edges g).
  Proof.
      intros.
      exploit wf_lb ; eauto.
      intros.
      destruct H.
      eapply wf_nxt in EDGE; eauto.
      congruence.
  Qed.


  Lemma has_edge_add :
    forall  o e d1 g nl l
           (WF : wf  g),
      has_edge o e d1 (IntMap.add (fresh g) (nl, l) (edges g)) <->
        has_edge o e d1 (edges g) \/
          (o = fresh g /\ In (e,d1) l).
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
      apply has_edge_node_d in E.
      eapply wf_fresh in E;eauto.
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
    rewrite IntMap.find_empty.
    intuition congruence.
  Qed.

  Lemma has_node_label_mkroot : forall o nl lb,
      has_node_label o nl (edges (mkroot lb)) <-> o = 0%int63 /\ nl = lb.
  Proof.
    unfold has_node_label.
    intros. unfold get_label,mkroot; simpl.
    rewrite IntMap.find_add.
    destruct (Int.eq_dec o 0).
    - intuition congruence.
    - simpl. unfold efail ; intuition congruence.
  Qed.

  Lemma has_node_label_rev_mkroot : forall o nl lb,
      has_node_label_rev o nl (nodelabels (mkroot lb)) <-> o = 0%int63 /\ nl = lb.
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
    - constructor.
      +  intros.
         induction H.
         * unfold edge in H.
           destruct H.
           rewrite has_edge_mkroot in H.
           auto.
         *  tauto.
      + intros. rewrite has_edge_mkroot in H.
        tauto.
    - rewrite has_edge_mkroot in H. tauto.
    - rewrite has_edge_mkroot.
      rewrite has_edge_rev_mkroot.
      tauto.
    - rewrite has_edge_mkroot in H.
      tauto.
    - rewrite has_node_label_mkroot.
      rewrite has_node_label_rev_mkroot.
      tauto.
    -  split; [simpl; tauto|].
      intro H. destruct H.
      rewrite has_edge_mkroot in H.
      tauto.
    - destruct H.
      rewrite has_node_label_mkroot in H.
      unfold mkroot. simpl.
      lia.
  Qed.

  Definition int_overflow {A: Type} := Error (A:= A) (cons (MSG "fresh has reached max_int"%string) nil).

  Fixpoint register_edgelabels (n:int) (l:list (EdgeLabel.t * int)) (m:ELMap.t (list int))  :=
    match l with
    | nil => m
    | cons (e,_) l => ELMap.addl  e n  (register_edgelabels n l m)
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
            (NLMap.addl n fr (nodelabels g))
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
    forall g l
            (WF : wf g)
            (NODUP2 : forall e1 e2 d, In (e1,d) l -> In (e2,d) l -> e1 = e2)
            (NOPARENT : forall o e1 e2 n, In (e1,n) l -> has_edge o e2 n (edges g) -> False)
           o e d,
    has_edge_rev o e d (register_parents (fresh g) l (parent g)) <->
      (has_edge_rev o e d (parent g) \/ (o = fresh g /\ In (e,d) l)).
  Proof.
    unfold has_edge_rev at 1.
    intros.
    rewrite find_register_parents.
    destruct (find_node d l) eqn:FIND.
    - apply find_node_Some in FIND.
      split ; intros.
      + inv H.
        tauto.
      + destruct H.
        rewrite <- wf_parent in H; eauto.
        exfalso. eapply NOPARENT;eauto.
        destruct H.
        repeat f_equal.
        eapply NODUP2;eauto.
        congruence.
    -  split; intros.
       unfold has_edge_rev.
       tauto.
       destruct H.
       apply H.
       destruct H.
       exfalso.
       eapply find_node_None;eauto.
  Qed.

  Lemma has_node_label_add : forall o o' lb lb' l g,
      has_node_label o lb (IntMap.add o' (lb', l) (edges g))  <->
        (o <> o' /\ has_node_label o lb (edges g) \/ (o = o' /\ lb = lb')).
  Proof.
    intros.
    unfold has_node_label at 1.
    unfold get_label.
    rewrite IntMap.find_add.
    unfold has_node_label, get_label.
    destruct (Int.eq_dec o o');
    intuition congruence.
  Qed.


(*  Lemma has_node_label_add : forall o lb lb' l g
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
 *)

  Lemma has_node_label_rev_add :
    forall o lb lb' g
           (WF: wf g)
    ,
      has_node_label_rev o lb (NLMap.addl lb' (fresh g) (nodelabels g)) <->
        (has_node_label_rev o lb (nodelabels g) \/ (o = fresh g /\ NodeLabel.eq lb lb')).
  Proof.
    intros.
    unfold has_node_label_rev at 1.
    unfold NLMap.findl.
    unfold NLMap.addl.
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

  Lemma find_label_None : forall  e l, find_edgelabel e l = None ->
                                       In e (map fst l) -> False.
  Proof.
    induction l ; simpl; auto.
    destruct a.
    destruct (EdgeLabel.eq_dec e t0);
    unfold EdgeLabel.eq in *.
    discriminate.
    simpl. intuition congruence.
  Qed.

  Lemma find_label_Some : forall  e d l, find_edgelabel e l = Some d ->
                                      In (e,d) l.
  Proof.
    induction l ; simpl; auto.
    - congruence.
    - destruct a.
      destruct (EdgeLabel.eq_dec e t0);
        unfold EdgeLabel.eq in *.
      intuition congruence.
      intuition congruence.
  Qed.


  Lemma findl_register_edgelabels :
    forall g l e
           (NODUP1 : NoDup (map fst l))
           (NODUP2 : NoDup (map snd l)),
      (ELMap.findl e (register_edgelabels (fresh g) l (edgelabels g))) =
        match find_edgelabel e l with
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
      unfold EdgeLabel.eq in e0; subst.
      rewrite find_label_not_In in IHl by auto.
      congruence.
      + rewrite ELMap.findl_neq by auto.
        auto.
  Qed.

  Import Relation_Operators.

  Lemma clos_trans_refl_trans : forall (A: Type) R x y,
    clos_trans A R x y ->
    clos_refl_trans A R x y.
  Proof.
    intros.
    apply Operators_Properties.clos_trans_t1n in H.
    induction H.
    econstructor ; eauto.
    eapply rt_trans; eauto.
    econstructor.
    auto.
  Qed.

  Lemma clos_refl_trans_has_node : forall g,
      wf g ->
      forall n m, clos_refl_trans int (edge (edges g)) n m ->
                (has_node n (edges g) /\ has_node  m (edges g)) \/ (n = m).
  Proof.
    intros.
    induction H0.
    - unfold edge in H0. destruct H0 ; subst.
      left ; split.
      apply has_edge_node_d in H0.
      destruct H0. eexists ; eauto.
      apply wf_lb in H0; auto.
    - tauto.
    - intuition congruence.
  Qed.


  Lemma clos_refl_trans_fresh : forall g,
      wf g ->
      forall n m,
        (n = fresh g \/ m = fresh g) ->
        clos_refl_trans int (edge (edges g)) n m ->
        n = fresh g /\ m = fresh g.
  Proof.
    intros.
    apply clos_refl_trans_has_node in H1; auto.
    destruct H0; destruct H1; try (intuition congruence).
    subst.
    destruct H1.
    apply wf_fresh in H0 ; auto. lia.
    destruct H1 ; subst.
    apply wf_fresh in H2; auto. lia.
  Qed.


  Lemma clos_trans_has_node : forall g,
      wf g ->
      forall n m, clos_trans int (edge (edges g)) n m -> has_node n (edges g) /\ has_node m (edges g).
  Proof.
    intros.
    induction H0.
    - unfold edge in H0. destruct H0.
      split.
      apply has_edge_node_d in H0.
      destruct H0. eexists ; eauto.
      apply wf_lb in H0; auto.
    - tauto.
  Qed.

  Lemma clos_trans_has_node_fresh :
    forall g,
      wf g ->
      forall n m, n = fresh g \/ m = fresh g ->
                  clos_trans int (edge (edges g)) n m -> False.
  Proof.
    intros.
    apply clos_trans_has_node in  H1; auto.
    destruct H0 ; subst.
    destruct H1.
    apply wf_fresh in H0. lia. auto.
    destruct H1.
    apply wf_fresh in H1. lia. auto.
  Qed.

  Lemma wf_create_node :
    forall nl l g g1 n
           (CREATE : create_node nl l g = OK(g1,n))
           (NODUP1 : NoDup (map fst l))
           (NODUP2 : NoDup (map snd l))
           (NODUP2 : forall e1 e2 d, In (e1,d) l -> In (e2,d) l -> e1 = e2)
           (NOEDGE : forall e1 e2 o d, has_edge o e1 d (edges g) -> In (e2,d) l -> False)
           (DEDGE  : forall e d, In (e,d) l -> exists lb, has_node_label d lb (edges g) /\ next_label nl e = OK lb)
           (WF : wf g)
    ,
      wf g1 /\ n = fresh g /\
        (forall o e d,
            has_edge o e d (edges g1) <->
              (has_edge o e d (edges g)
               \/
                 (o = n /\ In (e,d) l)))
      /\
        (forall o lb, has_node_label o lb (edges g1) <->
           (has_node_label o lb (edges g)
            \/
              o = n /\  lb =  nl))
      /\ (fresh g <> max_int /\ fresh g1 =  fresh g + 1)%uint63
  .
  Proof.
    unfold create_node.
    intros.
    destruct ((fresh g =? max_int)%uint63) eqn:FR ; try discriminate.
    inv CREATE.
    split.
    - constructor.
      + simpl; intros; simpl in *.
        rewrite has_edge_add in H by auto.
        rewrite has_edge_add in H0 by auto.
        destruct H ; destruct H0.
        * eapply WF; eauto.
        * destruct H0.
          apply has_edge_node_d in H.
          apply wf_fresh  in H; auto.
          lia.
        * destruct H.
          apply has_edge_node_d in H0.
          apply wf_fresh in H0; auto.
          lia.
        *
          destruct H; destruct H0.
          eapply NoDup_map; eauto.
      + simpl.
        assert (wfT : is_tree (edges g)) by (destruct WF; auto  ).
        constructor.
        assert (forall n n',
                   clos_trans int (edge (IntMap.add (fresh g) (nl, l) (edges g))) n n' ->
                   clos_trans int (edge (edges g)) n n' \/
                     (n = fresh g /\ exists e n1, In (e,n1) l /\
                                                    clos_refl_trans _ (edge (edges g)) n1 n')).
        {
          intros.
          apply Operators_Properties.clos_trans_t1n in H.
          induction H.
          - unfold edge in H.
            destruct H.
            rewrite has_edge_add in H.
            destruct H.
            + left.
              constructor.
              eexists. eauto.
            + right.
              destruct H.
              split;auto.
              do 2 eexists; split; eauto.
              apply rt_refl.
            + auto.
          - destruct IHclos_trans_1n.
            +
              unfold edge in H.
              destruct H.
              rewrite has_edge_add in H.
              destruct H.
              left.
              eapply t_trans.
              eapply t_step.
              eexists. eauto. auto.
              right.
              destruct H. split; auto.
              do 2 eexists.
              split; eauto.
              apply clos_trans_refl_trans. auto.
              auto.
            +  unfold edge in H.
               destruct H as (e & HAS).
               rewrite has_edge_add in HAS; auto.
               destruct HAS.
               destruct H1; subst.
               apply wf_lb in H; auto.
               apply wf_fresh in H ; auto.
               lia.
               destruct H; subst.
               destruct H1 ; subst.
               destruct H1 as (e1 & n1 & IN & CLO).
               right.
               split ; auto.
               do 2 eexists ; split; eauto.
        }
        intros.
        apply H in H0.
        destruct H0.
        * destruct wfT.
          eauto.
        * destruct H0. subst.
          destruct H1 as (e1 & n1 & IN & CLO).
          apply clos_refl_trans_fresh in CLO.
          destruct CLO; subst.
          apply DEDGE in IN.
          destruct IN as (lb & HAS & _).
          apply has_node_label_has_node  in HAS.
          apply wf_fresh in HAS; auto.
          lia. auto.
          tauto.
        * { intros.
        rewrite has_edge_add in H; eauto.
        rewrite has_edge_add in H0;eauto.
        destruct H; destruct H0.
        destruct wfT.
        * eapply tree_parent0;eauto.
        * destruct H0; subst.
          exfalso.
          eapply NOEDGE;eauto.
        * destruct H.  exfalso.
          eapply NOEDGE;eauto.
        * destruct H,H0; split; auto.
          congruence.
          eapply NoDup_map_snd ;eauto.
          }
      + simpl. intros.
        rewrite has_edge_add in H by eauto.
        rewrite has_node_label_add in H0 by eauto.
        rewrite has_node_label_add in H1 by eauto.
        destruct H.
        destruct H0 as [(_ & NLO) | (FO & NLO)];
          destruct H1 as [(_ & NL1) | (FD & NLD)].
        * eapply wf_nxt; eauto.
        * subst.
          eapply wf_lb in H;eauto.
          eapply wf_fresh in H ; eauto.
          lia.
        * subst.
          apply has_edge_node_d in H.
          eapply wf_fresh in H ; eauto.
          lia.
        * subst.
          apply has_edge_node_d in H.
          eapply wf_fresh in H ; eauto.
          lia.
        * destruct H ; subst.
          apply DEDGE in H2. destruct H2 as (lb & ND & NXT).
          destruct H0 ; try tauto.
          destruct H ; subst.
          intuition subst.
          assert (lb = lbd).
          eapply has_node_label_inj; eauto.
          congruence.
          apply has_node_label_has_node in ND.
          apply wf_fresh in ND ; auto. lia.
      + simpl.
        intros.
        rewrite has_edge_add;auto.
        rewrite has_edge_rev_add;auto.
        rewrite wf_parent by auto.
        tauto.
        intros.
        eapply NOEDGE;eauto.
      + simpl.
        intros.
        rewrite has_edge_add in H by auto.
        destruct (eq_dec d (fresh g)).
        { exists nl.
          rewrite has_node_label_add by auto.
          intuition congruence.
        }
        destruct H.
        * apply wf_lb in H; auto.
        { destruct H as (lb & NL).
          exists lb.
          rewrite has_node_label_add by auto.
          tauto.
        }
        * destruct H ; subst.
          apply DEDGE in H1.
          destruct H1 as (lb & H1).
          exists lb.
          rewrite has_node_label_add by auto. tauto.
      + simpl.
        intros.
        rewrite has_node_label_add by auto.
        rewrite has_node_label_rev_add by auto.
        rewrite <- wf_nl by auto.
        assert (has_node_label o nl0 (edges g) -> o <> fresh g).
        { intros. apply has_node_label_has_node in H.
          apply wf_fresh in H;auto. lia. }
        tauto.
      +  simpl.
         intros.
         rewrite findl_register_edgelabels.
         destruct (find_edgelabel  e l) eqn:FIND.
         * simpl.
           rewrite wf_el.
           apply find_label_Some in FIND.
           split; intros.
           destruct H.
           exists i.
           rewrite has_edge_add by auto.
           right.
           split;try congruence.
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
             eapply in_map. tauto.
           * auto.
           * auto.
      + simpl.
        intros.
        destruct H.
        rewrite has_node_label_add in H by auto.
        destruct H.
        destruct H as [_ H].
        apply has_node_label_has_node in H.
        apply wf_fresh in H;auto. lia.
        lia.
    -  simpl.
       repeat apply conj; auto.
       + intros.
         rewrite has_edge_add  by auto.
         tauto.
       + intros.
         rewrite has_node_label_add.
         split; intros.
         tauto.
         destruct H.
         assert (o <> fresh g).
         { intro ; subst.
           apply has_node_label_has_node in H.
           apply wf_fresh in H ; auto.
           lia.
         }
         tauto.
         tauto.
       + lia.
  Qed.

  (* [add_edge n1 el n2 g] add a new edge beteeen 2 existing nodes n1 and n2 *)
  Definition add_edge (n1:int) (el:EdgeLabel.t) (n2:int) (g:t) : res t :=
    match IntMap.find n1 (edges g) with
    | None => Error (cons (MSG "add_edge: origin node does not exist") nil)
    | Some (nl,l) =>
        OK (mk (root g) (IntMap.add n1 (nl,cons (el,n2) l) (edges g))
               (register_parents n1 ((el,n2)::nil) (parent g))
              (nodelabels g)
                             (ELMap.addl el n1 (edgelabels g))
                             (fresh g))
    end.

  (** [create_path nlabel n nl [e1,...,en] g] creates a path n -> e1 -> ... -> en in the graph g.
      nodes are created if needed.
      This is a generalised get_field.
   *)

  Fixpoint create_path
    (n:int)  (l:list EdgeLabel.t) (g:t) : res (t * (int * NodeLabel.t)) :=
    match IntMap.find n (edges g) with
    | None => Error (MSG "create_path: origin node " ::  MSG (string_of_int n) :: MSG " does not exist" :: nil)
    | Some(nl,succs) => match l with
                        | nil => OK (g,(n,nl))
                        | e::l =>
                            match find_edgelabel e succs with
                            | Some n' => create_path  n' l g (* following path *)
                            | None    =>
                                (* the edge does not exists *)
                                let* lb :=  next_label nl e in
                                let* (g',nn) := create_node lb nil g in
                                let* g2      := add_edge n e nn g' in
                                create_path  nn l g2
                            end
                        end
    end.

  Definition create_edge (n:int) (e:EdgeLabel.t) (g:t) : res (t * (int * NodeLabel.t)) :=
    match IntMap.find n (edges g) with
    | None => Error (MSG "create_edge: origin node " ::  MSG (string_of_int n) :: MSG " does not exist" :: nil)
    | Some(nl,succs) =>
        match find_edgelabel e succs with
        | Some n' =>
            let* lb := get_label (edges g) n' in
                         OK (g,(n',lb))
        | None    =>
            (* the edge does not exists *)
            let* lb :=  next_label nl e in
            let* (g',nn) := create_node lb nil g in
            let* g2      := add_edge n e nn g' in
            OK(g2,(nn,lb))
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
    Variable classify_edge : EdgeLabel.t -> EdgeLabel.t -> classify_edge.

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
                  let g := Pp.pp (Bcat (Bstr (string_of_int o)) (Bcat (pp g) (Bstr (string_of_int n))))in
                  Error (cons (MSG "check_must_alias: cannot find must alias") (cons (MSG Pp.nl) (cons (MSG g) nil)))
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
          match find_edgelabel e l2 with
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
            (ELMap.addl  e' o
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

  Definition get_parent (n:int) (g:t) :=
    IntMap.find n (parent g).

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
    let* lb := get_label (edges g) (root g) in
    let* path := get_upward_path_rec (NodeLabel.depth lb) g n in
    OK (List.rev path).

(*  Inductive is_tree_node (g:t) : int -> Prop :=
  | Leaf : forall n,
    (forall e n', In (e,n') (get_successors g n) -> is_tree_node g n') -> is_tree_node g n.

  Definition is_tree (g:t) :=
    forall n, is_tree_node g n.
 *)


  Lemma find_create_node : forall lb g g1 n n' nl succs,
      create_node lb [] g = OK (g1, n') ->
      wf g ->
      IntMap.find n (edges g) = Some (nl, succs) ->
      IntMap.find n (edges g1) = Some (nl, succs).
  Proof.
    intros.
    unfold create_node in H.
    destruct (fresh g =? max_int)%uint63 eqn:FR;
      try discriminate.
    inv H. simpl.
    rewrite IntMap.Facts.add_o.
    destruct (IntMap.M.E.eq_dec (fresh g) n).
    - assert (has_node_label n nl (edges g)).
      { unfold has_node_label.
        unfold get_label.
        rewrite H1. reflexivity.
      }
      subst. apply has_node_label_has_node in H.
      apply wf_fresh in H; auto.
      lia.
    - auto.
  Qed.

  Lemma has_edge_add_gen :
    forall o e d1 g n nl l
           (WF : wf g),
      has_edge o e d1 (IntMap.add n (nl, l) (edges g)) <->
        ( (o <> n /\ has_edge o e d1 (edges g))
          \/
          (o =  n /\ In (e,d1) l)).
  Proof.
    unfold has_edge ; intros.
    split; intros.
    - destruct H as (nl1 & l1 & FIND & IN).
    rewrite IntMap.find_add in FIND.
    destruct (Int.eq_dec o n).
    * inv FIND.
      tauto.
    * left. split;auto.
      do 2 eexists; split; eauto.
    - destruct H as [FIND| IN].
      +
      destruct FIND as (NEQ & nl1 & l1 & FIND & IN).
      rewrite IntMap.find_add.
      destruct (Int.eq_dec o n); try tauto.
      do 2 eexists ; split; eauto.
      + destruct IN as (EQ & IN); subst.
        subst.
        rewrite IntMap.find_add.
        destruct (Int.eq_dec n n); try congruence.
        do 2 eexists ; split ; eauto.
  Qed.

  Lemma and_False_r : forall (P:Prop) , (P /\ False) <-> False.
  Proof.
    tauto.
  Qed.

  Lemma or_False_r : forall (P:Prop) , (P \/ False) <-> P.
  Proof.
    tauto.
  Qed.

  Lemma has_edge_rev_add_gen : forall o e d o1 e1 d1 g,
      has_edge_rev o e d
        (IntMap.add d1 (e1, o1) (parent g))
      <->
        ((d <> d1 /\
            has_edge_rev o e d (parent g)) \/
           ( o = o1 /\ e = e1 /\ d = d1)).
  Proof.
    intros.
    unfold has_edge_rev.
    rewrite IntMap.find_add.
    destruct (Int.eq_dec d d1);
    intuition congruence.
  Qed.

  Lemma le_create_node :
    forall lb succs g g' n'
           (WF : wf g),
      create_node lb succs g = OK (g',n') ->
      le_graph g g'.
  Proof.
    unfold create_node.
    intros.
    destruct ((fresh g =? max_int)%uint63) eqn:F; try discriminate.
    inv H.
    constructor ; simpl; auto.
    - intros.
      rewrite has_node_label_add.
      destruct (eq_dec n (fresh g)); try tauto.
      { subst.
        apply has_node_label_has_node in H.
        apply wf_fresh in H; auto. lia. }
    - intros.
      rewrite has_edge_add_gen by auto.
      destruct (eq_dec o (fresh g)).
      { subst. apply has_edge_node_d in H.
        apply wf_fresh in H; auto. lia.
      }
      tauto.
    - lia.
  Qed.

  Lemma clos_refl_trans_morph : forall (A:Type) (E1 E2: A -> A -> Prop),
      inclusion _ E1 E2 ->
      inclusion _ (clos_refl_trans _ E1) (clos_refl_trans _ E2).
  Proof.
    unfold inclusion.
    intros.
    induction H0.
    -  apply rt_step.
       auto.
    - apply rt_refl.
    -  eapply rt_trans ; eauto.
  Qed.

  Lemma wf_create_edge : forall  n e g g' n' lb,
      wf g ->
      create_edge n e g = OK (g',(n',lb)) ->
      wf g'.
  Proof.
    intros.
    unfold create_edge in H0.
    destruct (IntMap.find
        (elt:=NodeLabel.t * list (EdgeLabel.t * int)) n
        (edges g)
             ) eqn:FIND ; try discriminate.
    destruct p as (nl, succs).
    destruct (find_edgelabel e succs) eqn:FLABEL; try discriminate.
    - (* The edge already exists - nothing to do *)
      destruct (get_label (edges g) i) eqn:GL ; try discriminate.
      simpl in H0. inv H0;auto.
    - (* Add the edge *)
      destruct (next_label nl e) as [lb'|] eqn:NXT ; try discriminate.
      simpl in H0.
      destruct (create_node lb' [] g) eqn:CNODE ; try discriminate.
      simpl in H0. destruct p as (g1,n1).
      destruct (add_edge n e n1 g1) as [g2|] eqn:ADD;
        try discriminate.
      simpl in H0.
      inv H0.
      exploit  wf_create_node; eauto.
      { simpl ; constructor. }
      { simpl ; constructor. }
      { simpl ; tauto. }
      { simpl ; tauto. }
      intros (WF1 & FR & HAS & NL & FRG).
      exploit find_create_node; eauto.
      intro FINDG1.
      unfold add_edge in ADD.
      rewrite FINDG1 in ADD.
      inv ADD.
      assert (En : forall e d, In (e,d) succs <-> has_edge n e d (edges g)).
      {
        split;intros.
        do 2 eexists.
        rewrite FIND.
        split; eauto.
        destruct H0 as (lb1 & l & FIND2).
        intuition congruence.
      }
      assert (NLB : has_node_label n nl (edges g)).
      {
        unfold has_node_label.
        unfold get_label. rewrite FIND.
        reflexivity.
      }
      assert (FRD : forall o e, has_edge o e (fresh g) (edges g) -> False).
      {
        intros.
        apply wf_lb in H0; auto.
        apply wf_fresh in H0;auto.
        lia.
      }
      assert (FRO : forall d e, has_edge (fresh g) e d (edges g) -> False).
      {
        intros.
        apply has_edge_node_d in H0.
        apply wf_fresh in H0;auto.
        lia.
      }
      constructor.
      + (* NODUP *) simpl.
        intros.
        rewrite has_edge_add_gen in H0,H1;auto.
        rewrite HAS in H0,H1.
        simpl in H0,H1.
        rewrite En in H0,H1.
        unfold eqEN in H0,H1.
        simpl in H0,H1.
        intuition try congruence.
        * eapply wf_nodup with (g:=g) ;eauto.
        * subst.
          exfalso.
          eapply find_label_None; eauto.
          change e with (fst (e,d2)).
          apply in_map.
          rewrite En.
          congruence.
        * subst.
          exfalso.
          eapply find_label_None; eauto.
          change e with (fst (e,d1)).
          apply in_map.
          rewrite En.
          congruence.
        * eapply wf_nodup with (g:= g) ; eauto.
      + (* wf_tree *)
        simpl.
        constructor.
        {
          assert (CLO : forall n1 n2,
                     clos_trans int (edge (IntMap.add n (nl, (e,fresh g):: succs) (edges g1)))  n1 n2 ->
                     clos_trans int (edge (edges g1)) n1 n2 \/
                     clos_refl_trans int (edge (edges g1)) n1 n /\ n2 = fresh g).
          {
            intros.
            apply Operators_Properties.clos_trans_t1n in H0.
            induction H0.
            destruct H0 as (e1 & E).
            rewrite has_edge_add_gen in E; auto.
            destruct E. destruct H0.
            left.
            constructor. eexists;eauto.
            destruct H0; subst.
            simpl in H1.
            destruct H1. inv H0.
            right; split; auto.
            apply rt_refl.
            rewrite En in H0.
            left. eapply t_step.
            eexists.
            rewrite HAS.
            left; eauto.
            destruct IHclos_trans_1n.
            clear H1.
            unfold edge in H0.
            destruct H0 as (e1 & ED).
            rewrite has_edge_add_gen in ED;auto.
            destruct ED.
            destruct H0.
            left.
            eapply t_trans; eauto.
            eapply t_step.
            eexists ; eauto.
            destruct H0 ; subst.
            simpl in H1.
            destruct H1 ; subst.
            inv H0.
            { exfalso.
              remember (fresh g) as n1.
              rename H into WFG.
              clear - HAS NL H2 Heqn1 WFG.
              induction H2.
              - subst.
                destruct H.
                rewrite HAS in H.
                destruct H.
                apply has_edge_node_d in H.
                apply wf_fresh in H; auto.
                lia.
                simpl in H; tauto.
              - subst.
                eapply IHclos_trans1; eauto.
            }
            { rewrite En in H0.
              left.
              eapply t_trans;eauto.
              eapply t_step;eauto.
              eexists ; eauto.
              rewrite HAS. left; eauto.
            }
            destruct H2 ; subst.
            right.
            split; auto.
            destruct H0.
            rewrite has_edge_add_gen in H0 ; auto.
            destruct H0.
            destruct H0.
            eapply rt_trans; eauto.
            eapply rt_step. eexists ; eauto.
            simpl in H0.
            destruct H0.
            subst.
            apply rt_refl.
        }
        intros.
        apply CLO in H0.
        destruct H0.
        eapply tree_no_loop;eauto.
        eapply wf_tree;eauto.
        destruct H0 ; subst.
        apply clos_refl_trans_morph with (E2 :=  (edge (edges g))) in H0.
        apply clos_refl_trans_fresh in H0; auto.
        destruct H0; subst.
        apply has_node_label_has_node in NLB.
        apply wf_fresh in NLB; eauto.
        lia.
        repeat intro.
        destruct H1.
        rewrite HAS in H1.
        simpl in H1 ; destruct H1 ; try tauto.
        eexists ; eauto.
        }

        intros.
        rewrite has_edge_add_gen in H0,H1;auto.
        rewrite HAS in *.
        simpl in H0,H1.
        rewrite and_False_r in *.
        rewrite or_False_r in *.
        rewrite En in H0,H1.
        destruct H0 as [(EQ1 & H0) | (EQ1 & [H0| H0])];
        destruct H1 as [(EQ2 & H1) | (EQ2 & [H1| H1])]; try intuition congruence.
        { eapply wf_tree with (g:=g) ;eauto. }
        { inv H1 ; subst.
          exfalso;eauto.
        }
        { eapply wf_tree with (g:=g) ;eauto.
          congruence.
        }
        { inv H0 ;
          exfalso ; eauto.
        }
        {
          inv H0.
          exfalso ; eauto.
        }
        { eapply wf_tree with (g:=g) ;eauto.
          congruence.
        }
        { inv H1.
          exfalso ; eauto.
        }
        { subst.
          eapply wf_tree with (g:=g) ;eauto.
        }
      + simpl.
        intros o e0 d lbo lbd.
        rewrite has_edge_add_gen by auto.
        rewrite! has_node_label_add by auto.
        simpl. rewrite En.
        rewrite! NL. rewrite HAS.
        simpl.
        intros.
        intuition subst; try congruence;
          try (eapply wf_nxt with (g:=g) ; eauto;fail);
          try (exfalso ; eapply  FRD; eauto;fail);
          try (exfalso ; eapply  FRO; eauto;fail).
        * inv H5.
          apply has_node_label_has_node in H6.
          apply wf_fresh in H6; auto.
          lia.
        * inv H5.
          apply has_node_label_has_node in NLB.
          apply wf_fresh in NLB;auto.
          lia.
      + intros.
        simpl.
        rewrite has_edge_add_gen by auto.
        simpl.
        rewrite has_edge_rev_add_gen.
        rewrite <- wf_parent by auto.
        simpl.
        rewrite HAS.
        simpl.
        rewrite! and_False_r.
        rewrite! or_False_r.
        rewrite En.
        unfold eqEN. simpl.
        assert (has_edge o e0 d (edges g) -> d <> fresh g).
        { repeat intro ; subst; eauto. }
        destruct (eq_dec o n); intuition try congruence.
        destruct (eq_dec d (fresh g));
          intuition try congruence.
        subst; tauto.
      + simpl.
        intros.
        rewrite has_edge_add_gen in H0 by auto.
        rewrite HAS in H0.
        simpl in H0.
        rewrite En in H0.
        rewrite and_False_r in H0.
        rewrite or_False_r in H0.
        assert (exists lb1,
                   d <> n /\ (has_node_label d lb1 (edges g) \/ d = fresh g /\ lb1 = lb) \/
                     d = n /\  lb1 = nl).
        {
          intuition subst.
          - apply wf_lb in H4 ; auto.
            destruct H4 as (lb1 & HASL).
            destruct (eq_dec d n).
            + exists nl. right. split;auto.
            + exists lb1. tauto.
          -  destruct (eq_dec (fresh g) n).
             exists nl. intuition congruence.
             exists lb. intuition congruence.
          - apply wf_lb in H3 ; auto.
            destruct H3 as (lb1 & HASL).
            destruct (eq_dec d n).
            + exists nl. right. split;auto.
            + exists lb1. tauto.
        }
        destruct H1 as (lb1 & H1).
        exists lb1.
        rewrite has_node_label_add.
        rewrite NL.
        tauto.
      + simpl.
        intros.
        rewrite has_node_label_add; auto.
        rewrite NL.
        rewrite <- wf_nl by auto.
        rewrite NL.
        intuition subst.
        { left; auto.
        }
        { destruct (eq_dec o n); [right|left].
          - split; auto.
            subst.
            eapply has_node_label_inj; eauto.
          - split; auto.
        }
        {
          destruct (eq_dec (fresh g) n).
          subst.
          apply has_node_label_has_node in NLB.
          apply wf_fresh in NLB;auto.
          lia.
          left ; split; auto.
        }
      + simpl.
        intros.
        destruct (EdgeLabel.eq_dec e0 e).
        { unfold EdgeLabel.eq in e1.
          subst.
          rewrite ELMap.findl_eq by auto.
          split; intros.
          - simpl in H0.
            destruct H0; subst.
            + exists (fresh g).
            rewrite has_edge_add_gen by auto.
            right; split; auto. simpl. left.
            split; simpl; auto.
            +
              rewrite wf_el in H0 by auto.
              destruct H0 as (d1 & EDGE).
              rewrite HAS in EDGE.
              simpl in EDGE. rewrite and_False_r in EDGE.
              rewrite or_False_r in EDGE.
              destruct (eq_dec o n).
              subst.
              eexists d1.
              rewrite has_edge_add_gen by auto.
              simpl.
              rewrite En.
              tauto.
              eexists d1.
              rewrite has_edge_add_gen by auto.
              left.
              rewrite HAS.
              tauto.
          - simpl.
            rewrite wf_el.
            destruct (eq_dec n o); try tauto.
            right.
            destruct H0 as (d & EDGE).
            rewrite has_edge_add_gen in EDGE by auto.
            destruct EDGE.
            exists d; tauto.
            intuition congruence.
            auto.
        }
        {
          rewrite ELMap.findl_neq by auto.
          rewrite wf_el by auto.
          split ; intros (d & EDGE).
          - rewrite HAS in EDGE.
          simpl in EDGE.
          rewrite and_False_r in EDGE.
          rewrite or_False_r in EDGE.
          eexists d.
          rewrite has_edge_add_gen by auto.
          simpl. rewrite! En.
          rewrite HAS.
          simpl.
          rewrite and_False_r.
          rewrite or_False_r.
          destruct (eq_dec o n); intuition congruence.
          - rewrite has_edge_add_gen in EDGE by auto.
            rewrite HAS in EDGE.
            simpl in EDGE.
            rewrite En in EDGE.
            unfold eqEN in EDGE.
            simpl in EDGE.
            exists d.
            rewrite HAS.
            simpl. intuition congruence.
        }
      + simpl.
        intros.
        destruct H0.
        rewrite has_node_label_add in H0 by auto.
        destruct H0. destruct H0.
        apply has_node_label_has_node in H1.
        apply wf_fresh in H1 ; auto.
        destruct H0 ; subst.
        apply has_node_label_has_node in NLB.
        apply wf_fresh in NLB;auto.
        lia.
  Qed.

  Lemma create_edge_spec : forall n e g g' n' lb',
      wf g ->
      create_edge n e g = OK (g',(n',lb')) ->
      (has_edge n e n' (edges g'))
      /\
        ( has_node_label n' lb' (edges g'))
      /\
        (forall o e1 d,
            has_edge o e1 d (edges g') <->
              (has_edge o e1 d (edges g) \/
                 (~ has_edge o e1 d (edges g) /\ ~ has_node d (edges g) /\ d = fresh g /\ o = n /\  e1 = e /\ d = n')))
      /\
        (forall nd lb1, has_node_label nd lb1 (edges g') <->
                          (has_node_label nd lb1 (edges g) \/
                             nd = n' /\ lb' = lb1))
      /\ ((fresh g <=? fresh g' = true)%uint63).
  Proof.
    intros.
    exploit wf_create_edge; eauto.
    intro WF.
    unfold create_edge in H0.
    destruct (IntMap.find
        (elt:=NodeLabel.t * list (EdgeLabel.t * int)) n
        (edges g)
             ) eqn:FIND ; try discriminate.
    destruct p as (nl, succs).
    destruct (find_edgelabel e succs) eqn:FLABEL; try discriminate.
    - (* The edge already exists *)
      destruct (get_label (edges g) i) eqn:GL ; try discriminate.
      simpl in H0. inv H0;auto.
      repeat apply conj.
      + do 2 eexists ; repeat split; eauto.
        apply find_label_Some in FLABEL.
        auto.
      + unfold has_node_label. auto.
      + intuition subst.
        apply find_label_Some in FLABEL.
        do 2 eexists. split; eauto.
      + intuition subst.
        unfold has_node_label.
        auto.
      + lia.
    - (* Add the edge *)
      destruct (next_label nl e) as [lb|] eqn:NXT ; try discriminate.
      simpl in H0.
      destruct (create_node lb [] g) eqn:CNODE ; try discriminate.
      simpl in H0. destruct p as (g1,n1).
      destruct (add_edge n e n1 g1) as [g2|] eqn:ADD;
        try discriminate.
      simpl in H0.
      inv H0.
      exploit  wf_create_node; eauto.
      { simpl ; constructor. }
      { simpl ; constructor. }
      { simpl ; tauto. }
      { simpl ; tauto. }
      intros (WF1 & FR & HAS & NL & FRG).
      exploit find_create_node; eauto.
      intro FINDG1.
      unfold add_edge in ADD.
      rewrite FINDG1 in ADD.
      inv ADD.
      assert (En : forall e d, In (e,d) succs <-> has_edge n e d (edges g)).
      {
        split;intros.
        do 2 eexists.
        split; eauto.
        destruct H0 as (lb1 & l & FIND2).
        rewrite FIND in FIND2.
        intuition congruence.
      }
      assert (NLB : has_node_label n nl (edges g)).
      {
        unfold has_node_label,get_label.
        rewrite FIND. reflexivity.
      }
      assert (FRD : forall o e, has_edge o e (fresh g) (edges g) -> False).
      {
        intros.
        apply wf_lb in H0; auto.
        apply wf_fresh in H0;auto.
        lia.
      }
      assert (FRO : forall d e, has_edge (fresh g) e d (edges g) -> False).
      {
        intros.
        apply has_edge_node_d in H0.
        apply wf_fresh in H0;auto.
        lia.
      }
      simpl.
      repeat apply conj.
      + rewrite has_edge_add_gen by auto.
        simpl. tauto.
      + rewrite has_node_label_add.
        rewrite NL.
        destruct (eqs (fresh g) n).
        subst. apply has_node_label_has_node in NLB.
        apply wf_fresh in NLB ; auto. lia.
        tauto.
      + intros.
        rewrite has_edge_add_gen by auto.
        rewrite HAS.
        simpl. rewrite and_False_r. rewrite or_False_r.
        rewrite En.
        intuition try congruence.
        inv H3.
        right. repeat split;eauto.
        intro ND.
        apply wf_fresh in ND ; auto. lia.
        destruct (eq_dec o n); intuition congruence.
      + intros.
        rewrite has_node_label_add.
        rewrite NL.
        intuition subst; try tauto.
        destruct (eq_dec nd n).
        subst.
        right. split; auto.
        eapply has_node_label_inj; eauto.
        tauto.
        *  destruct (eq_dec (fresh g) n).
           subst.
           apply has_node_label_has_node in NLB.
           apply wf_fresh in NLB; auto.
           lia.
           left;split; auto.
      + lia.
  Qed.

  Lemma create_edge_le :
    forall  n e g g' n' lb'
      (WF : wf g),
      create_edge n e g = OK (g',(n',lb')) ->
      le_graph g g'.
  Proof.
    intros.
    exploit create_edge_spec;eauto.
    intros (E & N & S1 & S2 & S3).
    constructor; auto.
    - intros.
      rewrite S2. tauto.
    - intros.
      rewrite S1. tauto.
  Qed.


  End S.

End Make.
