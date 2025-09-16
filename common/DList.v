(** Dependent list indexed by [typ] *)
From BarocqComp Require Import Types.
From BarocqComp Require Import Error.
From compcert Require Import Coqlib.
Import List Notations.

Section S.

  Variable abs_typ_impl : Maps.PMap.t Type.

  Notation eval_typ := (eval_typ abs_typ_impl).

  Inductive dlist : list typ -> Type :=
  | DNIL : dlist nil
  | DCONS : forall {ty:typ} (e: eval_typ ty) {l:list typ} (dl : dlist l) , dlist (ty::l).

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

  Definition car {ty:typ} {lt:list typ} (dl : dlist (ty::lt)) : eval_typ ty.
  Proof.
    remember (ty::lt) as l.
    destruct dl.
    -  exfalso. discriminate.
    - eapply Types.typ_cast.
      apply (inj_list_hd Heql).
      exact e.
  Defined.

  Definition cdr {ty:typ} {lt:list typ} (dl : dlist (ty::lt)) : dlist lt.
  Proof.
    remember (ty::lt) as l.
    destruct dl.
    -  exfalso. discriminate.
    - apply inj_list_tl in Heql.
      rewrite Heql in dl.
      exact dl.
  Defined.

  (*Fixpoint map (l:list typ) (x:dlist l): dlist l:=
    match x with
    | DNIL  => DNIL
    | DCONS e tl  => DCONS e (map _ tl)
    end. *)

  Fixpoint map (l:list typ) : forall (x:dlist l), dlist l:=
    match l with
    | nil  => fun _ => DNIL
    | ty ::tl  => fun x => DCONS (car x) (map _ (cdr x))
    end.

  Lemma map_id : forall l x, map l x = x.
  Proof.
    induction x; simpl;auto.
    - rewrite IHx.
      reflexivity.
  Qed.

  Lemma dlist_nil : forall (x:dlist nil), x = DNIL.
  Proof.
    intros.
    rewrite <- (map_id _  x).
    reflexivity.
  Qed.

  
  Context {A: Type}.

  Section MMAP.

  Variable F : forall (ty:typ), A -> res (eval_typ ty).

  Fixpoint mmap  (l:list A) (lt:list typ) : res (dlist lt) :=
    match l with
    | nil =>  match lt with
              | nil => OK DNIL
              | _   => fail
              end
    | cons e l' => match lt with
                   | nil =>  fail
                   | ty::lt' =>
                       match F ty e , mmap l' lt' with
                       | OK v , OK dl => OK (DCONS v dl)
                       | _   , _      => fail
                       end
                   end
    end.

  End MMAP.

  Variable P : forall (ty:typ) (v1 v2: eval_typ ty), Prop.

  Inductive Forall2 : forall (lt:list typ) (d1 d2: dlist lt), Prop :=
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
      inv IHForall2.
      constructor.
      constructor. constructor;auto.
  Qed.


End S.
