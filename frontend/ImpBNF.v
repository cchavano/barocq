From Stdlib Require Import List Lia.
From compcert Require Import Maps.
From BarocqComp Require Import Option Utils Maps2 Types Benum Syntax Typing Denot.

Local Open Scope option_monad_scope.

(** * Abstract syntax *)

(** ** Tail computations *)

Inductive tailcomp : Type :=
  | TcBegin : ident -> tailcomp -> tailcomp -> btyp -> tailcomp
  | TcComp : comp -> tailcomp
  | TcIfThenElse : atom -> tailcomp -> tailcomp -> btyp -> tailcomp
  | TcSwitch : atom -> list (pattern * tailcomp) -> btyp -> tailcomp
  | TcAttr : ident -> tailcomp -> tailcomp.

(** ** Functions *)

Definition function : Type := Syntax.function tailcomp btyp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef tailcomp btyp literal.

(** ** Programs *)

Definition program : Type := Syntax.program tailcomp btyp literal.

(** * Induction principle for tailcomp *)

Section TAILCOMP_IND.

  Fixpoint tailcomp_depth (t: ImpBNF.tailcomp) : nat :=
    match t with
    | ImpBNF.TcBegin _ t1 t2 _ =>
        1 + Nat.max (tailcomp_depth t1) (tailcomp_depth t2)
    | ImpBNF.TcComp _ => 0
    | ImpBNF.TcIfThenElse _ t1 t2 _ =>
        let m := Nat.max (tailcomp_depth t1) (tailcomp_depth t2) in
        1 + m
    | ImpBNF.TcSwitch _ cases _ =>
        let cases_depths := List.map (fun c => tailcomp_depth (snd c)) cases in
        let m := List.fold_right (fun d m => Nat.max m d) 0 cases_depths in
        1 + m
    | ImpBNF.TcAttr _ e => 1 + tailcomp_depth e
    end.

  Variable P : tailcomp -> Prop.

  Variable PTcBegin :
    forall x tc1 tc2 ty, P tc1 -> P tc2 -> P (TcBegin x tc1 tc2 ty).

  Hypothesis PTcComp : forall c, P (TcComp c).

  Hypothesis PTcIfThenElse :
    forall a t1 t2 ty, P t1 -> P t2 -> P (TcIfThenElse a t1 t2 ty).

  Hypothesis PTcSwitch :
    forall a cases ty,
      (forall p tc, List.In (p, tc) cases -> P tc) ->
      P (TcSwitch a cases ty).
      
  Hypothesis PTcAttr : forall x tc, P tc -> P (TcAttr x tc).

  Theorem tailcomp_depth_ind : forall tc, P tc.
  Proof.
    intros. remember (tailcomp_depth tc) as n.
    revert tc Heqn.
    induction n using Wf_nat.lt_wf_ind; intros.
    destruct n.
    - destruct tc; try (auto || discriminate).
    - destruct tc; simpl in Heqn; try (auto || discriminate);
      simpl; intros.
      + inv Heqn.
        assert (tailcomp_depth tc1 < S (Nat.max (tailcomp_depth tc1) (tailcomp_depth tc2))). lia.
        assert (tailcomp_depth tc2 < S (Nat.max (tailcomp_depth tc1) (tailcomp_depth tc2))). lia.
        pose proof (H (tailcomp_depth tc1) H0 tc1 eq_refl).
        pose proof (H (tailcomp_depth tc2) H1 tc2 eq_refl).
        apply PTcBegin; auto.
      + inv Heqn. 
        assert (tailcomp_depth tc1 < S (Nat.max (tailcomp_depth tc1) (tailcomp_depth tc2))). lia.
        assert (tailcomp_depth tc2 < S (Nat.max (tailcomp_depth tc1) (tailcomp_depth tc2))). lia.
        apply PTcIfThenElse.
        * exact (H (tailcomp_depth tc1) H0 tc1 eq_refl).
        * exact (H (tailcomp_depth tc2) H1 tc2 eq_refl).
      + inv Heqn. apply PTcSwitch; intros.
        apply H with (m := tailcomp_depth tc).
        clear - H0. revert p tc H0.
        {
          induction l; intros.
          - simpl in H0. destruct H0. 
          - simpl in H0. destruct H0.
            + destruct a. inv H. simpl. lia.
            + simpl. apply IHl in H. lia.
        }
        reflexivity.
      + inv Heqn. apply PTcAttr.
        assert ((tailcomp_depth tc) < (S (tailcomp_depth tc))). lia.
        exact (H (tailcomp_depth tc) H0 tc eq_refl).
  Qed.

End TAILCOMP_IND.

Fixpoint btypof_tailcomp (tc: tailcomp) : btyp :=
  match tc with
  | TcComp c => btypof_comp c
  | TcBegin _ _ _ ty
  | TcIfThenElse _ _ _ ty
  | TcSwitch _ _ ty => ty
  | TcAttr _ tc => btypof_tailcomp tc
  end.

Definition convertible_btyp (te: tenv) (ty: btyp) : bool :=
  match btyp_to_typ te ty with
  | Some _ => true
  | _ => false
  end.

Lemma convertible_btyp_iff:
  forall te bt,
  convertible_btyp te bt = true <->
  (exists ty, btyp_to_typ te bt = Some ty).
Proof.
  intros; split; intros.
  - unfold convertible_btyp in H.
    destruct (btyp_to_typ te bt); try discriminate.
    exists t. reflexivity.
  - destruct H. unfold convertible_btyp.
    rewrite H. reflexivity.
Qed.

Fixpoint wf_tailcomp (te: tenv) (tc: tailcomp) : bool :=
  match tc with
  | TcComp c =>
      convertible_btyp te (btypof_comp c)
  | TcBegin x tc1 tc2 ty =>
      convertible_btyp te ty
      && btyp_eqb (btypof_tailcomp tc2) ty
      && wf_tailcomp te tc1
      && wf_tailcomp te tc2
  | TcIfThenElse _ tc1 tc2 ty =>
      convertible_btyp te ty
      && btyp_eqb (btypof_tailcomp tc1) ty
      && btyp_eqb (btypof_tailcomp tc2) ty
      && wf_tailcomp te tc1
      && wf_tailcomp te tc2
  | TcSwitch _ cases ty =>
      convertible_btyp te ty
      && List.forallb (fun '(_, tci) => btyp_eqb (btypof_tailcomp tci) ty) cases
      && (List.forallb (fun '(_, tci) => wf_tailcomp te tci) cases)
  | TcAttr _ tc1 => wf_tailcomp te tc1
  end.

Lemma wf_tailcomp_btyp_to_typ:
  forall te tc,
    wf_tailcomp te tc = true ->
    exists ty, btyp_to_typ te (btypof_tailcomp tc) = Some ty.
Proof.
  induction tc; simpl; intros; destruct_conj H.
  - rewrite convertible_btyp_iff in C. exact C.
  - rewrite convertible_btyp_iff in H. exact H.
  - rewrite convertible_btyp_iff in C1. exact C1.
  - rewrite convertible_btyp_iff in C1. exact C1.
  - exact (IHtc H). 
Qed.

(** * Denotational semantics *)

Section DENOT.

  Variable tabs : PMap.t Type.

  Notation genv := (@Denot.genv tabs).

  Notation lenv := (@Denot.lenv tabs).

  Notation value := (@Denot.value tabs).

  Notation eval_typ := (@Types.eval_typ tabs).

  Notation eval_atom := (@Denot.eval_atom tabs).

  Notation eval_comp := (@Denot.eval_comp tabs).

  Definition typof_tailcomp (te: tenv) (tc: tailcomp) : option typ :=
    btyp_to_typ te (btypof_tailcomp tc).

  Definition eval_match (tv:typ) (v: eval_typ tv) (tr: typ) (cases: list (pattern * option (eval_typ tr * lenv))) : option (eval_typ tr * lenv) :=
    (match tv as t0 return (eval_typ t0 -> option (eval_typ tr * lenv)) with
    | TEnum _ elems => 
        (fun v0 => ematch_with v0 cases)
    | _ => (fun _ => fail)
    end) v.

  Fixpoint eval_tailcomp_rec (te: tenv) (ge: genv) (le: lenv) (ty: typ) (tc: tailcomp) : option (eval_typ ty * lenv) :=
    match tc with
    | TcBegin x tc1 tc2 _ =>
        let* ty1 := typof_tailcomp te tc1 in
        let* (v1, le1) := eval_tailcomp_rec te ge le ty1 tc1 in
        (* let* le' := eval_statement te ge le s in *)
        let le' := lenv_update tabs le1 x (Val tabs ty1 v1) in
        eval_tailcomp_rec te ge le' ty tc2
    | TcComp c =>
        let* tc := typof_comp te c in
        let* vc := ecast_typ tabs (eval_comp te ge le tc c) ty in
        ret (vc, le)
    | TcIfThenElse a tc1 tc _ =>
        let* va := eval_atom te ge le TBool a in
        if va then eval_tailcomp_rec te ge le ty tc1
        else eval_tailcomp_rec te ge le ty tc
    | TcSwitch a cases _ =>
        let* ta := typof_atom te a in
        let* va := eval_atom te ge le ta a in
        let vcases := MapList.map (eval_tailcomp_rec te ge le ty) cases in
        eval_match ta va ty vcases
    | TcAttr _ tc1 => eval_tailcomp_rec te ge le ty tc1
    end.

  Definition eval_tailcomp (te: tenv) (ge: genv) (le: lenv) (tr: typ) (tc: tailcomp) : option (eval_typ tr) :=
    let* (v, _) :=  (eval_tailcomp_rec te ge le tr tc) in
    ret v.

  Definition eval_prog (impl: genv) (prog: program) : option (tenv * genv) :=
    Denot.eval_prog tabs  eval_tailcomp impl prog.

End DENOT.

