(** Dependent list indexed by [typ] *)
From BarocqComp Require Import Error Utils.
From compcert Require Import Coqlib.
Import List Notations.

Section S.

  Context {A: Type}.

  Variable Ftyp : A -> Type.

  Inductive dlist : list A -> Type :=
  | DNIL : dlist nil
  | DCONS : forall {ty:A} (e: Ftyp ty) {l:list A} (dl : dlist l) , dlist (ty::l).

  Lemma inj_list_hd : forall {A:Type} {e1 e2:A} {l1 l2:list A},
      e1::l1 = e2::l2 ->  e1 = e2.
  Proof.
    congruence.
  Defined.

  Lemma inj_list_tl : forall {A:Type} {e1 e2:A} {l1 l2:list A},
      e1::l1 = e2::l2 ->  l1 = l2.
  Proof.
    congruence.
  Defined.

  Definition cast {ty ty': A} (EQ: ty = ty') (v: Ftyp ty) : Ftyp ty' :=
    cast (f_equal Ftyp EQ) v.

  Definition car {ty:A} {lt:list A} (dl : dlist (ty::lt)) : Ftyp ty.
  Proof.
    remember (ty::lt) as l.
    destruct dl.
    -  exfalso. discriminate.
    - eapply cast. apply (inj_list_hd Heql).
      exact e.
  Defined.

  Definition cdr {ty:A} {lt:list A} (dl : dlist (ty::lt)) : dlist lt.
  Proof.
    remember (ty::lt) as l.
    destruct dl.
    -  exfalso. discriminate.
    - apply inj_list_tl in Heql.
      rewrite Heql in dl.
      exact dl.
  Defined.

  Fixpoint seq (l:list A) : forall (x:dlist l), dlist l:=
    match l with
    | nil  => fun _ => DNIL
    | ty ::tl  => fun x => DCONS (car x) (seq _ (cdr x))
    end.

  Lemma seq_id : forall l x, seq l x = x.
  Proof.
    induction x; simpl;auto.
    - rewrite IHx.
      reflexivity.
  Qed.

  Lemma dlist_nil : forall (x:dlist nil), x = DNIL.
  Proof.
    intros.
    rewrite <- (seq_id _  x).
    reflexivity.
  Qed.

  Lemma car_cdr : forall (t:A) (lt:list A) (dl :dlist (t::lt)),
      dl = DCONS (car dl) (cdr dl).
  Proof.
    intros.
    rewrite <- (seq_id _ dl) at 1.
    simpl.
    rewrite seq_id.
    reflexivity.
  Qed.

  Variable eq_dec : forall (t1 t2:A),{t1 = t2} + {t1 <> t2}.


  Definition equal {t1:A} (v1 : Ftyp t1) {t2:A} (v2:Ftyp t2) : Prop :=
    match eq_dec t1 t2 with
    | left EQ => cast EQ v1 = v2
    | _       => False
    end.


  
  Context {B: Type}.

  Section MMAP.

  Variable F : forall (ty:A), B -> res (Ftyp ty).

  Fixpoint mmap  (l:list B) (lt:list A) : res (dlist lt) :=
    match l with
    | nil =>  match lt with
              | nil => OK DNIL
              | _   => fail
              end
    | cons e l' => match lt with
                   | nil =>  fail
                   | ty::lt' =>
                       let* v := F ty e in
                       let* m := mmap l' lt' in
                       eret (DCONS v m)
                   end
    end.

  End MMAP.

  Lemma mmap_ext:
    forall (f g: forall ty, B -> res (Ftyp ty)),
      (forall b ty, f ty b = g ty b) ->
      (forall l lt, mmap f l lt = mmap g l lt).
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl. destruct lt.
      + reflexivity.
      + rewrite H. rewrite IHl. reflexivity.
  Qed.

  Lemma mmap_ext_In:
    forall (f g: forall ty, B -> res (Ftyp ty)) (l: list B),
      (forall b ty, List.In b l -> f ty b = g ty b) ->
      (forall lt, mmap f l lt = mmap g l lt).
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl. destruct lt.
      + reflexivity.
      + rewrite H.
        destruct (g a0 a); simpl; try reflexivity.
        erewrite IHl; eauto.
        intros. specialize (H b ty).
        simpl in H. pose proof (@or_intror (a = b) (In b l) H0).
        apply H in H1. exact H1. apply List.in_eq. 
  Qed.

  Lemma mmap_ext_OK:
    forall (f g: forall ty, B -> res (Ftyp ty)),
      (forall b ty v, f ty b = OK v -> g ty b = OK v) ->
      (forall l lt l',
        mmap f l lt = OK l' ->
        mmap g l lt = OK l').
  Proof.
    induction l; intros.
    - simpl in H0. destruct lt; exact H0.
    - simpl in H0. destruct lt; try discriminate.
      monadInv H0. inv EQ2. simpl.
      specialize (H a a0 x EQ). rewrite H; simpl.
      erewrite IHl; eauto. reflexivity.
  Qed.

  Lemma mmap_ext_In_OK:
    forall (f g: forall ty, B -> res (Ftyp ty)) (l: list B),
      (forall b ty v, List.In b l -> f ty b = OK v -> g ty b = OK v) ->
      (forall lt l',
        mmap f l lt = OK l' ->
        mmap g l lt = OK l').
  Proof.
    induction l; intros.
    - simpl in H0. destruct lt; simpl; exact H0.
    - simpl in H0. destruct lt; try discriminate.
      monadInv H0. inv EQ2. simpl.
      pose proof (H a a0 x (in_eq a l) EQ). rewrite H0; simpl.
      erewrite IHl; eauto. simpl. reflexivity.
      intros. specialize (H b ty v).
      pose proof (in_cons a b l H1).
      apply (H H3 H2). 
  Qed.

  Lemma mmap_ext_In_Error:
    forall (f g: forall ty, B -> res (Ftyp ty)) (l: list B),
      (forall b ty v, List.In b l -> f ty b = OK v -> g ty b = OK v) ->
      (forall b ty e, List.In b l -> f ty b = Error e -> g ty b = Error e) ->
      (forall lt e,
        mmap f l lt = Error e ->
        mmap g l lt = Error e).
  Proof.
    induction l; intros.
    - simpl in H. destruct lt; simpl; exact H1.
    - simpl in H1. destruct lt.
      + unfold efail in H1. inv H1. reflexivity.
      + simpl. destruct (f a0 a) eqn:Efta.
        * simpl in H1. eapply H in Efta; try (apply List.in_eq).
          rewrite Efta; simpl.
          destruct (mmap f l lt) eqn:Emmap; simpl in H1; simpl.
          -- inv H1.
          -- inv H1. eapply IHl in Emmap; eauto.
             rewrite Emmap. simpl. reflexivity.
             intros. specialize (H b ty v).
             destruct H. simpl. right. exact H1.
             exact H2. reflexivity.
             intros. specialize (H0 b ty e0).
             destruct H0. simpl. right. exact H1.
             exact H2. reflexivity.
        * simpl in H1. inv H1. eapply H0 in Efta; try (apply List.in_eq).
          rewrite Efta. simpl. reflexivity.
  Qed.

  Variable P : forall (ty:A) (v1 v2: Ftyp ty), Prop.

  Inductive Forall2 : forall (lt:list A) (d1 d2: dlist lt), Prop :=
  | ForallDNIL : Forall2 nil DNIL DNIL
  | ForallDCONS : forall ty v1 v2, P ty v1 v2 -> forall lt d1 d2, Forall2 lt d1 d2 -> Forall2 (ty::lt) (DCONS v1 d1) (DCONS v2 d2).

  Lemma  Forall2_mmap : forall F G l lt,
      List.Forall2 (fun x  ty =>  res_rel (P ty) (F ty x) (G ty x)) l lt ->
      res_rel  (Forall2 lt) (mmap F l lt) (mmap G l lt).
  Proof.
    intros. induction H.
    - simpl. constructor.
      constructor.
    - simpl.
      inv H.
      constructor.
      simpl.
      inv IHForall2.
      constructor.
      constructor. constructor;auto.
  Qed.


End S.

Section MAP.

  Context {A B: Type}.
  Variable Ftyp : A -> Type.
  Variable F : forall (ty:A), B -> res (Ftyp ty).

  Definition resFtyp (ty:A) := res (Ftyp ty).

  Fixpoint map2  (l:list B) (lt:list A) : res (dlist resFtyp lt) :=
    match lt as l0 return (res (dlist resFtyp l0)) with
    | nil => match l with
             | nil => OK (DNIL resFtyp)
             | _ => efail
             end
    | ty :: lt' =>
           match l with
           | nil => efail
           | e :: l' =>
               let* m := map2 l' lt'
               in OK (DCONS resFtyp (F ty e) m)
           end
    end.

End MAP.

Lemma map2_eq : forall {A B:Type} (Ftyp : A -> Type) (F G: forall (ty:A), B -> res (Ftyp ty)),
    forall lt l,
      List.Forall (fun v => forall ty, F ty v = G ty v) lt ->
      map2 Ftyp F lt l = map2 Ftyp G lt l.
Proof.
  induction lt ; simpl.
  - destruct l;reflexivity.
  - destruct l; try reflexivity.
    intros.
    rewrite IHlt.
    destruct (map2 Ftyp G lt l).
    + simpl. inv H.
      rewrite H2.
      reflexivity.
    +  reflexivity.
    + inv H; auto.
Qed.

Section OFERR.
  Context {A: Type}.
  Context  {Ftyp : A -> Type}.

  Fixpoint of_err {lt :list A} (dl : dlist (resFtyp Ftyp) lt) :  res (dlist Ftyp lt) :=
    match dl in (dlist _ l) return (res (dlist Ftyp l)) with
   | DNIL _ => OK (DNIL Ftyp)
   | @DCONS _ _ ty e l dl1 => let* X := e in let* TL := of_err dl1 in OK (DCONS Ftyp X TL)
   end.

End OFERR.

Lemma map2_mmap_err : forall {A B:Type} (Ftyp : A -> Type) (F: forall (ty:A), B -> res (Ftyp ty)),
    forall lt l dl,
    map2 Ftyp F lt l = OK dl ->
    isError(mmap Ftyp F lt l) \/ exists vargs', of_err dl = OK vargs' /\ mmap Ftyp F lt l = OK vargs'.
Proof.
  induction lt; simpl.
  - destruct l; simpl; try discriminate.
    intros. inv H.
    right. eexists.
    split; reflexivity.
  - destruct l; try discriminate.
    intros.
    destruct (map2 Ftyp F lt l) eqn:MMAP2; try discriminate.
    simpl in H.
    inv H.
    destruct (F a0 a) eqn:FA.
    simpl.
    apply IHlt in MMAP2.
    destruct MMAP2 as [MMAP2 | MMAP2].
    destruct MMAP2. rewrite H. simpl. left.
    eexists x;auto.
    destruct MMAP2 as (vargs' & OF & MMAP).
    rewrite MMAP.
    simpl.
    right.
    rewrite OF.
    simpl. eexists. split. reflexivity.
    reflexivity.
    simpl.
    left ; eexists e;auto.
Qed.



Section IN.
  Context {A: Type}.
  Context {F1 : A -> Type}.
  Variable eq_dec : forall (t1 t2:A),{t1 = t2} + {t1 <> t2}.

  Fixpoint In {ty:A} (v:F1 ty) {lt:list A} (dl : dlist F1 lt) : Prop :=
    match dl with
    | DNIL _ => False
    | DCONS _ e1 dl1 => equal F1 eq_dec v e1 \/ In v dl1
    end.

  Fixpoint nth_error {lt:list A} (dl :dlist F1 lt) (n:nat) : res {a:A & F1 a} :=
    match n with
    | O%nat => match dl with
               | DNIL _ => fail
               | DCONS _ e1 _ =>  OK (existT _ _ e1)
               end
    | S n'  => match dl with
               | DNIL _ => fail
               | DCONS _ _ dl1 => nth_error dl1 n'
               end
    end.

  
End IN.



Section Forall2Rec.
  Context {A : Type}.
  Context {F1 : A -> Type}.
  Context {F2 : A -> Type}.
  Variable R : forall (ty:A), F1 ty -> F2 ty -> Prop.

  Fixpoint forall2  (lt:list A) : dlist F1 lt -> dlist F2 lt -> Prop  :=
    match lt  with
    | nil => fun _ _ => True
    | ty :: lt' => fun dl1 dl2 => R ty (car F1 dl1) (car F2 dl2)
                                  /\
                                    forall2 lt' (cdr F1 dl1) (cdr F2 dl2)
    end.

End Forall2Rec.

