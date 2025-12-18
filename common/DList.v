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

