From Coq Require Import List Bool BinNums.
From compcert Require Import Coqlib Integers.
From VST Require Import Zlist.
From BarocqComp Require Import Ident Intop Utils ZlistPlus.
From BarocqComp Require Import OptionMonad.
Open Scope option_monad_scope.

Import ListNotations.

Inductive constr : ident -> Type :=
  Constr : forall (i: ident), constr i.

Lemma constr_eq_dec :
  forall {i: ident} (x y: constr i), {x = y} + {x <> y}.
Proof.
  intros. left. destruct x; destruct y. reflexivity.
Defined.

Polymorphic Fixpoint enum (elems: list ident) : Type :=
  match elems with
  | nil => False
  | ei :: nil => constr ei
  | ei :: elems' => constr ei + (enum elems')
  end.

Lemma enum_eq_dec :
  forall {elems: list ident} (x y: enum elems), {x = y} + {x <> y}.
Proof.
  induction elems as [| e0 elems0]; intros.
  - destruct x.
  - simpl in x; simpl in y. destruct elems0 as [| e1 elems1].
    + apply constr_eq_dec.
    + destruct x; destruct y; try (right; discriminate).
      * decide equality. apply constr_eq_dec.
      * decide equality. apply constr_eq_dec.
Defined.

Definition enum_eq {elems: list ident} (x y: enum elems) :=
  if enum_eq_dec x y then true else false.

Definition enum_neq {elems: list ident} (x y: enum elems) :=
 negb (enum_eq x y).


Fixpoint make_enum (elems: list ident) (i: ident) : option (enum elems) :=
  match elems as l0 return (option (enum l0)) with
  | [] => fail
  | s0 :: l0 =>
      if Ident.eq_dec i s0
      then
       ret match l0 as l2 return enum (s0:: l2) with
         | [] => Constr s0
         | s3 :: l2 => inl (Constr s0)
         end
      else
        let* e :=  make_enum l0 i in
        ret
          (match l0 as l2 return (enum l2 -> enum (s0 :: l2)) with
           | [] => fun e1 : enum [] => False_rect (enum [s0]) e1
           | s3 :: l2 => fun e1 : enum (s3 :: l2) => inr e1
           end e)
  end.


Lemma make_enum_rew : forall (elems: list ident) (i: ident),
    make_enum elems i =
  match elems as l0 return (option (enum l0)) with
  | [] => fail
  | s0 :: l0 =>
      if Ident.eq_dec i s0
      then
       ret match l0 as l2 return enum (s0:: l2) with
         | [] => Constr s0
         | s3 :: l2 => inl (Constr s0)
         end
      else
        let* e :=  make_enum l0 i in
        ret
          (match l0 as l2 return (enum l2 -> enum (s0 :: l2)) with
           | [] => fun e1 : enum [] => False_rect (enum [s0]) e1
           | s3 :: l2 => fun e1 : enum (s3 :: l2) => inr e1
           end e)
  end.
Proof.
  destruct elems; reflexivity.
Qed.

Fixpoint mk_enum (elems:list ident) (s:ident) : forall (H : existsb  (Ident.eqb s) elems = true), enum elems.
Proof.
  destruct elems; intro EX.
  + simpl in EX. discriminate.
  + simpl in EX.
    destruct (Ident.eqb s i).
    { destruct elems.
      apply (Constr i).
      apply (inl (Constr i)). }
    {
      unfold orb in EX.
      specialize (mk_enum elems s EX).
      destruct elems.
      discriminate.
      apply (inr (mk_enum)).
    }
Defined.

Lemma make_enum_mk_enum : forall elems s e,
    make_enum elems s = Some e -> exists H, mk_enum elems s H = e.
Proof.
  induction elems.
  - simpl. discriminate.
  - simpl. intros.
    destruct (eq_dec s a).
    + simpl.
      inversion H; subst; clear H.
      rewrite String.eqb_refl.
      simpl. exists (eq_refl).
      destruct elems; auto.
    + destruct (make_enum elems s) eqn:REC; try discriminate.
      inversion H ; subst; clear H.
      destruct (IHelems  _ _ REC).
      assert (EX : Ident.eqb s a
         || existsb (Ident.eqb s) elems = true).
      { rewrite orb_comm.
        rewrite x. reflexivity.
      }
      destruct (Ident.eqb s a) eqn:EQB.
      *  apply String.eqb_eq in EQB.
         congruence.
      *  destruct elems.
         discriminate.
         exists x.
         congruence.
Qed.

Lemma mk_enum_make_enum : forall elems s  H,
    make_enum elems s = Some (mk_enum elems s H).
Proof.
  induction elems.
  - simpl. discriminate.
  - simpl. intros.
    destruct (eq_dec s a).
    + simpl.
      subst.
      destruct (Ident.eqb a a) eqn:E.
      * destruct elems.
      reflexivity.
      reflexivity.
      * exfalso.
        unfold eqb in E.
        generalize (String.eqb_refl a); congruence.
    + destruct (Ident.eqb s a) eqn:E.
      simpl in H.
      destruct H.
      rewrite String.eqb_eq in E. congruence.
      simpl in H.
      rewrite IHelems with (H:=H).
      destruct elems.
      discriminate.
      reflexivity.
Qed.


Definition ident_of_constr {elems: list ident} (e: enum elems) : ident.
  induction elems as [| e0 elems0].
  - destruct e.
  - destruct elems0.
    + apply e0.
    + destruct e.
      * apply e0.
      * apply (IHelems0 e).
Defined.

Definition to_i32 {elems: list ident} (e: enum elems) : int :=
  let fix aux (elems0: list ident) (ctr: int) : int :=
    match elems0 with
    | nil => Int.mone
    | ei :: elems0' =>
        if Ident.eq_dec ei (ident_of_constr e) then ctr
        else aux elems0' (Int.add ctr Int.one)
    end
  in
  aux elems Int.zero.


Definition of_i32 (elems: list ident) (i: int) : option (enum elems) :=
    let* ei := list_nth_z elems (Int.signed i) in
    make_enum elems ei.

Inductive pattern : Type :=
  | PIdent (i: ident) (z: Z) : pattern
  | PWildcard : pattern.


Fixpoint match_with_err {elems: list ident} {A: Type} (e: enum elems) (cases: list (pattern * option A)) : option A :=
  match cases with
  | nil => fail
  | (pi, ai) :: cases' =>
      match pi with
      | PIdent i _ =>
          let* ei := make_enum elems i in
          if enum_eq ei e then ai
          else match_with_err e cases'
      | PWildcard => ai
      end
  end.



Fixpoint match_with_err2 {elems: list ident} {A E: Type} (e: enum elems) (cases: list (pattern * option A))
  (E_eq_dec: forall (x y: E), {x = y} + {x <> y}) (f: enum elems -> E) : option A :=
  match cases with
  | nil => fail
  | (pi, ai) :: cases' =>
      match pi with
      | PIdent i _ =>
          let* ei := make_enum elems i in
          if E_eq_dec (f ei) (f e) then ai
          else match_with_err2 e cases' E_eq_dec f
      | PWildcard => ai
      end
  end.

Lemma match_with_err_eq_match_with_err2 :
  forall (elems: list ident) (A E: Type) (e: enum elems) (cases: list (pattern * option A))
  (E_eq_dec: forall (x y: E), {x = y} + {x <> y})
  (econv_to: enum elems -> E)
  (econv_from: E -> enum elems)
  (INV1: forall (a: enum elems) (b: E), econv_to (econv_from b) = b)
  (INV2: forall (a: enum elems) (b: E), econv_from (econv_to a) = a),
  match_with_err e cases = match_with_err2 e cases E_eq_dec econv_to.
Proof.
  induction cases as [| (pi, ai) cases']; intros.
  - simpl. reflexivity.
  - simpl. destruct pi.
    + destruct (make_enum elems i); simpl.
      * unfold enum_eq. erewrite <- Utils.bij_eq_iff with (EQB := E_eq_dec); eauto.
        destruct (E_eq_dec (econv_to e0) (econv_to e)).
        reflexivity.
        apply (IHcases' E_eq_dec econv_to econv_from INV1 INV2).
      * reflexivity.
    + reflexivity.
Qed.

(** Brute force proof principle for enumeration types *)

Fixpoint forallb_enum (l: list ident) (P : enum l -> bool) {struct l}: bool.
Proof.
  destruct l.
  - exact false.
  - specialize (forallb_enum l).
    destruct l.
    + simpl in P. apply (P (Constr i)).
    + change (enum (i :: i0 ::l)) with (constr i + enum (i0::l))%type in P.
      apply andb.
      apply (P (inl (Constr i))).
      apply (forallb_enum (fun x => P (inr x))).
Defined.

Fixpoint forallb_enum_correct (l:list ident) : forall P, forallb_enum l P = true->
                                         forall e, P e = true.
Proof.
  destruct l.
  - simpl. discriminate.
  - intros.
    specialize (forallb_enum_correct  l).
    destruct l.
    + simpl in H. destruct e. assumption.
    +
      change (enum (i :: i0 ::l)) with
        (constr i + (enum (i0 ::l)))%type in e.
      specialize (forallb_enum_correct (fun x => P (inr x))).
      unfold forallb_enum in H; fold forallb_enum in H.
      rewrite andb_true_iff in H.
      destruct e.
      * destruct c. tauto.
      *  apply forallb_enum_correct.
         destruct H.
         auto.
Qed.

Lemma enum_eq_sound : forall l (x y: enum l),
    enum_eq x y = true ->
    x = y.
Proof.
  unfold enum_eq. intros.
  destruct (enum_eq_dec x y); auto.
  congruence.
Qed.

Lemma enum_eq_refl : forall l (x:enum l),
    enum_eq x x = true.
Proof.
  unfold enum_eq; intros.
  destruct (enum_eq_dec x x); congruence.
Qed.

Lemma match_with_err_head : forall {elems : list ident} {A: Type} id EQ (cases : list (pattern * option A)) x v1,
    match_with_err (mk_enum elems id EQ) ((PIdent id x, v1) :: cases) = v1.
Proof.
  simpl.
  intros.
  rewrite mk_enum_make_enum with (H:= EQ).
  simpl. rewrite enum_eq_refl.
  reflexivity.
Qed.


Lemma make_enum_inv : forall elems id id' (EQ: existsb (eqb id) elems = true) (EQ':existsb (eqb id') elems = true),
    make_enum elems id = make_enum elems id' ->
    id = id'.
Proof.
  intros.
  induction elems ; simpl in H.
  - simpl in EQ. discriminate.
  - destruct (eq_dec id a);
    destruct (eq_dec id' a).
    + subst.
      reflexivity.
    + subst.
      destruct (make_enum elems id') eqn:MK.
      * simpl in *.
        inv H.
        destruct elems.
        exfalso ; apply e.
        discriminate.
      * simpl in H.
        discriminate.
    + destruct (make_enum elems id) eqn:MK.
      simpl in H.
      inv H.
      destruct elems.
      * exfalso;  apply e0.
      * discriminate.
      * inv H.
    +
      unfold eqb in EQ,EQ'.
      simpl in EQ,EQ'.
      rewrite <- eqb_neq in n.
      rewrite n in EQ.
      rewrite <- eqb_neq in n0.
      rewrite n0 in EQ'.
      simpl in EQ,EQ'.
      rewrite mk_enum_make_enum with (H:= EQ) in H.
      rewrite mk_enum_make_enum with (H:= EQ') in H.
      simpl in *.
      inv H.
      destruct elems.
      discriminate.
      apply IHelems; auto.
      rewrite mk_enum_make_enum with (H:= EQ).
      rewrite mk_enum_make_enum with (H:= EQ').
      congruence.
Qed.



Lemma mk_enum_inv : forall elems id id' EQ EQ',
    mk_enum elems id EQ = mk_enum elems id' EQ' ->
    id = id'.
Proof.
  intros.
  eapply make_enum_inv; eauto.
  rewrite mk_enum_make_enum with (H:= EQ).
  rewrite mk_enum_make_enum with (H:= EQ').
  congruence.
Qed.

Lemma match_with_err_tail : forall {elems : list ident} {A: Type} id id' EQ (cases : list (pattern * option A)) x v1,
    existsb (eqb id') elems = true->
    id <> id' ->
    match_with_err (mk_enum elems id EQ) ((PIdent id' x, v1) :: cases) = match_with_err (mk_enum elems id EQ) cases.
Proof.
  simpl.
  intros.
  destruct (make_enum elems id') eqn:MK.
  - simpl.
    destruct (enum_eq e (mk_enum elems id EQ)) eqn:EQ1.
    apply enum_eq_sound in EQ1. subst.
    apply make_enum_mk_enum in MK.
    destruct MK as (EQ1 & MK).
    apply mk_enum_inv in MK. congruence.
    reflexivity.
  - simpl.
    rewrite mk_enum_make_enum with (H:= H) in MK.
    discriminate.
Qed.

Lemma forallb_enum_equal : forall (l:list ident) (F: enum l -> enum l),
  forallb_enum l (fun e : enum l => enum_eq (F e) e) =
  true ->
  forall e, F e = e.
Proof.
  intros.
  apply enum_eq_sound.
  revert e.
  apply forallb_enum_correct; auto.
Qed.


Definition cast_eqb {A: Type} (l:list ident) (F : A -> enum l) (l1:list ident)  (l2:list A) :=
  forall2b (fun x y => match make_enum l x with
                       | None => false
                       | Some e    => enum_eq e (F y)
                       end) l1 l2.

Lemma cast_eqb_sound : forall {A: Type} (l:list ident) (F: A -> enum l) (l': list A) (n:nat),
    cast_eqb l F l l' = true ->
    (let* ei := nth_error l n
     in make_enum l ei) =
      (let* en := nth_error l' n in Some (F en)).
Proof.
  intros.
  assert (forall l1 l2,
             cast_eqb l F l1 l2 = true ->
             (let* ei := nth_error l1 n in make_enum l ei) = (let* en := nth_error l2 n in Some (F en))).
  { clear H.
    unfold cast_eqb.
    set (G := (fun (x : ident) (y : A) => match make_enum l x with
                                | Some e => enum_eq e (F y)
                                | None => false
                                end)).
    intro l1; revert n.
    induction l1;destruct l2; try discriminate.
    - simpl. rewrite! nth_error_nil.
      reflexivity.
    - simpl.
      intros.
      destruct (G a a0) eqn:EQG; try discriminate.
      destruct n; simpl.
      + unfold G in EQG. destruct (make_enum l a); try discriminate.
        apply enum_eq_sound in EQG. congruence.
      + apply (IHl1 n); auto.
  }
  apply H0;auto.
Qed.

Lemma castZ_eqb_sound : forall {A: Type} (l:list ident) (F: A -> enum l) (l': list A) (n:Z),
    cast_eqb l F l l' = true ->
    (let* ei := list_nth_z l n
     in make_enum l ei) =
      (let* en := list_nth_z l' n in Some (F en)).
Proof.
  intros.
  rewrite! list_nth_z_eq.
  destruct (Z_lt_dec n 0). reflexivity.
  apply cast_eqb_sound; auto.
Qed.
