From Coq Require Import List Bool.
From compcert Require Import Integers.
From BarocqComp Require Import Ident Intop Error Utils.

Import ListNotations.

Inductive constr : ident -> Type :=
  Constr : forall (i: ident), constr i.

Lemma constr_eq_dec :
  forall {i: ident} (x y: constr i), {x = y} + {x <> y}.
Proof.
  intros. left. destruct x; destruct y. reflexivity.
Defined.

Fixpoint enum (elems: list ident) : Type :=
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

Fixpoint make_enum (elems: list ident) (i: ident) : res (enum elems) :=
  match elems as l0 return (res (enum l0)) with
  | [] => fail
  | s0 :: l0 =>
      if Ident.eq_dec i s0
      then
       ret match l0 as l2 return enum (s0:: l2) with
         | [] => Constr s0
         | s3 :: l2 => inl (Constr s0)
         end
      else
        match make_enum l0 i with
        | OK e =>
            ret
              (match l0 as l2 return (enum l2 -> enum (s0 :: l2)) with
               | [] => fun e1 : enum [] => False_rect (enum [s0]) e1
               | s3 :: l2 => fun e1 : enum (s3 :: l2) => inr e1
               end e)
       | Error e => Error e
       end
  end.

Fixpoint mk_enum (elems:list ident) (s:ident) : forall (H : existsb  (String.eqb s) elems = true), enum elems.
Proof.
  destruct elems; intro EX.
  + simpl in EX. discriminate.
  + simpl in EX.
    destruct (String.eqb s i).
    { destruct elems.
      apply (Constr i).
      apply (inl (Constr i)). }
    { unfold orb in EX.
      specialize (mk_enum elems s EX).
      destruct elems.
      discriminate.
      apply (inr (mk_enum)).
    }
Defined.

Lemma make_enum_mk_enum : forall elems s e,
    make_enum elems s = OK e -> exists H, mk_enum elems s H = e.
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
      assert (EX : String.eqb s a
         || existsb (String.eqb s) elems = true).
      { rewrite orb_comm.
        rewrite x. reflexivity.
      }
      destruct (String.eqb s a) eqn:EQB.
      *  apply String.eqb_eq in EQB.
         congruence.
      *  destruct elems.
         discriminate.
         exists x.
         congruence.
Qed.

Lemma mk_enum_make_enum : forall elems s  H,
    make_enum elems s = OK (mk_enum elems s H).
Proof.
  induction elems.
  - simpl. discriminate.
  - simpl. intros.
    destruct (eq_dec s a).
    + simpl.
      subst.
      destruct (String.eqb a a) eqn:E.
      * destruct elems.
      reflexivity.
      reflexivity.
      * exfalso.
        generalize (String.eqb_refl a); congruence.
    + destruct (String.eqb s a) eqn:E.
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

Definition of_i32 (elems: list ident) (i: int) : res (enum elems) :=
  if Int.cmp Clt i Int.zero
     || Nat.leb (List.length elems) (I32.to_nat i) then fail
  else
    let* ei := list_nth_err elems (I32.to_nat i) in
    make_enum elems ei.

Inductive pattern : Type := 
  | PIdent (i: ident) : pattern
  | PWildcard : pattern.
  
Fixpoint match_with {elems: list ident} {A: Type} (e: enum elems) (cases: list (pattern * A)) : res A :=
  match cases with
  | nil => fail
  | (pi, ai) :: cases' =>
      match pi with
      | PIdent i =>
          let* ei := make_enum elems i in
          if enum_eq ei e then ret ai
          else match_with e cases'
      | PWildcard => ret ai
      end
  end.

Fixpoint match_with2 {elems: list ident} {A E: Type} (e: enum elems) (cases: list (pattern * A))
  (E_eq_dec: forall (x y: E), {x = y} + {x <> y}) (f: enum elems -> E) : res A :=
  match cases with
  | nil => fail
  | (pi, ai) :: cases' =>
      match pi with
      | PIdent i =>
          let* ei := make_enum elems i in
          if E_eq_dec (f ei) (f e) then ret ai
          else match_with2 e cases' E_eq_dec f
      | PWildcard => ret ai
      end
  end.

Lemma match_with_eq_match_with2 :
  forall (elems: list ident) (A E: Type) (e: enum elems) (cases: list (pattern * A))
  (E_eq_dec: forall (x y: E), {x = y} + {x <> y})
  (econv_to: enum elems -> E)
  (econv_from: E -> enum elems)
  (INV1: forall (a: enum elems) (b: E), econv_to (econv_from b) = b)
  (INV2: forall (a: enum elems) (b: E), econv_from (econv_to a) = a),
  match_with e cases = match_with2 e cases E_eq_dec econv_to.
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
  
Fixpoint match_with_err {elems: list ident} {A: Type} (e: enum elems) (cases: list (pattern * res A)) : res A :=
  match cases with
  | nil => fail
  | (pi, ai) :: cases' =>
      match pi with
      | PIdent i =>
          let* ei := make_enum elems i in
          if enum_eq ei e then ai
          else match_with_err e cases'
      | PWildcard => ai
      end
  end.

Fixpoint match_with_err2 {elems: list ident} {A E: Type} (e: enum elems) (cases: list (pattern * res A))
  (E_eq_dec: forall (x y: E), {x = y} + {x <> y}) (f: enum elems -> E) : res A :=
  match cases with
  | nil => fail
  | (pi, ai) :: cases' =>
      match pi with
      | PIdent i =>
          let* ei := make_enum elems i in
          if E_eq_dec (f ei) (f e) then ai
          else match_with_err2 e cases' E_eq_dec f
      | PWildcard => ai
      end
  end.

Lemma match_with_err_eq_match_with_err2 :
  forall (elems: list ident) (A E: Type) (e: enum elems) (cases: list (pattern * res A))
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
                       | Error _ => false
                       | OK e    => enum_eq e (F y)
                       end) l1 l2.

Lemma cast_eqb_sound : forall {A: Type} (l:list ident) (F: A -> enum l) (l': list A) (n:nat),
    cast_eqb l F l l' = true ->
    (let* ei := Utils.list_nth_err l n
     in make_enum l ei) =
      (let* en := Utils.list_nth_err l' n in eret (F en)).
Proof.
  intros.
  assert (forall l1 l2,
             cast_eqb l F l1 l2 = true ->
             (let* ei := list_nth_err l1 n in make_enum l ei) = (let* en := list_nth_err l2 n in eret (F en))).
  { clear H.
    unfold cast_eqb.
    set (G := (fun (x : ident) (y : A) => match make_enum l x with
                                | OK e => enum_eq e (F y)
                                | Error _ => false
                                end)).
    unfold list_nth_err.
    intro l1; revert n.
    induction l1;destruct l2; try discriminate.
    - simpl. rewrite! nth_error_nil.
      reflexivity.
    - simpl.
      intros.
      destruct (G a a0) eqn:EQG; try discriminate.
      destruct n; simpl.
      + unfold G in EQG. destruct (make_enum l a); try discriminate.
        apply enum_eq_sound in EQG. unfold eret ; congruence.
      + apply (IHl1 n); auto.
  }
  apply H0;auto.
Qed.
