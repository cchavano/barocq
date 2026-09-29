From Stdlib Require Import Bool List Lia.
From compcert Require Import Maps.
From BarocqComp Require Import Option While Utils Maps2 Types Benum Syntax Typing Denot.

Local Open Scope option_monad_scope.

(** * Abstract syntax *)

(** ** Tail computations *)
Inductive tailcomp : Type :=
  | TcBegin : ident -> tailcomp -> tailcomp -> btyp -> tailcomp
  | TcWhile : list (ident * tailcomp) -> atom -> atom -> tailcomp -> tailcomp -> btyp -> tailcomp
  | TcComp : comp -> tailcomp
  | TcActRecord : list (ident * atom) -> btyp -> tailcomp
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
    | ImpBNF.TcWhile init _ _ body  tc _ =>
        S (Nat.max (Nat.max (tailcomp_depth body) (tailcomp_depth tc))
             (List.fold_right (fun d m => Nat.max (tailcomp_depth (snd d)) m) 0 init))
    | ImpBNF.TcActRecord _ _ => 0
    | ImpBNF.TcAttr _ e => 1 + tailcomp_depth e
    end.

  Variable P : tailcomp -> Prop.

  Variable PTcBegin :
    forall x tc1 tc2 ty, P tc1 -> P tc2 -> P (TcBegin x tc1 tc2 ty).

  Variable PTcWhile :
    forall init cond variant body tc ty,
      (forall i v, In (i,v) init -> P v) -> P body -> P tc ->
      P (TcWhile init cond variant body tc ty).


  Hypothesis PTcComp : forall c, P (TcComp c).

  Hypothesis PTcActR : forall r ty, P (TcActRecord r ty).

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
      + apply PTcWhile.
        intros.
        apply (H (tailcomp_depth v)).
        rewrite Heqn.
        assert (tailcomp_depth v <= (fold_right
          (fun (d : ident * tailcomp) (m : nat) =>
           Nat.max (tailcomp_depth (snd d)) m)
          0 l)).
        { clear - H0.
          induction l; simpl.
          - simpl in H0. tauto.
          - simpl in H0.
            destruct H0 ; subst.
            simpl. lia.
            apply IHl in H. lia.
        }
        lia.
        reflexivity.
        apply (H (tailcomp_depth tc1)); auto.
        lia.
        apply (H (tailcomp_depth tc2)); auto.
        lia.
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
  | TcActRecord _ ty => ty
  | TcBegin _ _ _ ty
  | TcIfThenElse _ _ _ ty
  | TcSwitch _ _ ty => ty
  | TcWhile _ _ _ _ _ ty => ty
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

Definition btyp_is_actr (ty:btyp) :=
  match ty with
  | BActR l => true
  | _       => false
  end.

Section BINDINGS.

  Variable updated_vars : tailcomp -> SSet.t.

  Definition updated_by_binding_aux (x_tc: ident * tailcomp) :=
    SSet.union (SSet.singleton  (fst x_tc)) (updated_vars (snd x_tc)).

End BINDINGS.


Fixpoint updated_vars (tc :tailcomp) : SSet.t :=
  match tc with
  | TcComp c => SSet.empty
  | TcActRecord _ _ => SSet.empty
  | TcBegin x tc1 tc2 _ => SSet.add x (SSet.union (updated_vars tc1) (updated_vars tc2))
  | TcWhile l _ _ body tc _ => SSet.union (SSet.union_list (updated_by_binding_aux updated_vars) l)
                               (SSet.union (updated_vars body) (updated_vars tc))
  | TcIfThenElse _ tc1 tc2 _ => SSet.union (updated_vars tc1) (updated_vars tc2)
  | TcSwitch _     l _      => SSet.union_list (fun  '(_,tc) => updated_vars tc) l
  | TcAttr _ tc => updated_vars tc
  end.

Fixpoint no_overwrite (up : SSet.t) (l:list (ident * tailcomp)) :=
  match l with
  | nil => true
  | (x,tc)::l =>
      SSet.is_empty (SSet.inter (updated_vars tc) up)
      && negb (SSet.mem x up) && no_overwrite (SSet.add x up) l
  end.




Fixpoint para_eval (acc:SSet.t)(l :list (ident * atom)) :=
  match l with
  | nil => true
  | (x,a)::l => SSet.is_empty (SSet.inter (AtomOrdered.has_varb a) acc) &&
                  para_eval (SSet.add x acc) l
  end.


Fixpoint wf_tailcomp (te: tenv) (tc: tailcomp) : bool :=
  match tc with
  | TcComp c =>
      convertible_btyp te (btypof_comp c)
      && negb (btyp_is_actr (btypof_comp c))
  | TcActRecord r ty => convertible_btyp te ty
                        && para_eval SSet.empty r
                        && btyp_eqb (BActR (MapList.map btypof_atom r)) ty
  | TcBegin x tc1 tc2 ty =>
      convertible_btyp te ty
      && btyp_eqb (btypof_tailcomp tc2) ty
      && wf_tailcomp te tc1
      && wf_tailcomp te tc2
      && negb (btyp_is_actr (btypof_tailcomp tc1))
  | TcWhile init cond decr body tc ty =>
      convertible_btyp te ty
      &&  no_overwrite SSet.empty init
      &&  btyp_eqb (btypof_tailcomp tc) ty
      &&  List.forallb (fun x => wf_tailcomp te (snd x)) init
      &&  wf_tailcomp te body
      &&  wf_tailcomp te tc
      &&  btyp_eqb (BActR (MapList.map btypof_tailcomp init)) (btypof_tailcomp body)
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
  Ltac convertible :=
    match goal with
    | H : convertible_btyp _ ?B = true |- _ =>
        rewrite convertible_btyp_iff in H; exact H
    end.
  all: try convertible.
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


  Section EVALINIT.
    (** This is NOT  parallel evaluation*)

    Variable eval_tailcomp_rec : lenv -> forall (ty:typ), tailcomp -> option (eval_typ ty * lenv).

    Fixpoint update_lenv (te:tenv) (l:list (ident * tailcomp)) (le:lenv) : option lenv :=
      match l with
      | nil => Some le
      | (x,tc)::l =>
          let* ty := typof_tailcomp te tc in
          let* (v,le') := eval_tailcomp_rec le ty tc in
          update_lenv te l (lenv_update tabs le' x (Val tabs ty v))
      end.

  End EVALINIT.

  Definition is_actr (ty: typ) :=
    match ty with
    | TRecord None l => Some l
    | _ => None
    end.


  Fixpoint eval_tailcomp_rec (te: tenv) (ge: genv) (le: lenv) (ty: typ) (tc: tailcomp) : option (eval_typ ty * lenv) :=
    match tc with
    | TcBegin x tc1 tc2 _ =>
        let* ty1 := typof_tailcomp te tc1 in
        let* (v1, le1) := eval_tailcomp_rec te ge le ty1 tc1 in
        let le' := lenv_update tabs le1 x (Val tabs ty1 v1) in
        eval_tailcomp_rec te ge le' ty tc2
    | TcWhile init cond decr body tc _ =>
        let* le' := update_lenv (eval_tailcomp_rec te ge) te init le in
        let* tyd := (typof_atom te decr) in
        let* m := eval_atom te ge le' tyd decr in
        let* n := nat_of_val _ m in
        let* tyb := MapList.mmap _ (typof_tailcomp te)  init in
        (* Dynamic check that there is no shadowing *)
        let* _   := record_of_lenv tabs ge tyb le' in
        let C := fun le =>
                   eval_atom te ge le TBool cond in
        let B := fun le =>
                   let* (r,le') := eval_tailcomp_rec te ge le (TRecord None tyb) body in
                   Some (lenv_of_record _ _ r le') in
        let* le'' := while C B n le' in
        eval_tailcomp_rec te ge le'' ty tc
    | TcComp c =>
        let* tc := typof_comp te c in
        let* vc := ecast_typ tabs (eval_comp te ge le tc c) ty in
        ret (vc, le)
    | TcActRecord r bt =>
        match ty with
        | TRecord None fields =>
            let* ty1 := Typing.btyp_to_typ te bt in
            if typ_eqb ty ty1
            then
              let* v := eval_act_record tabs eval_atom te ge r fields le in
              Some (v, le) (* This is the job of the while to update the environment *)
            else None
        |  _             => None
        end
    | TcIfThenElse a tc1 tc _ =>
        let* va := eval_atom te ge le TBool a in
        if va then eval_tailcomp_rec te ge le ty tc1
        else eval_tailcomp_rec te ge le ty tc
    | TcSwitch a cases _ =>
        let* ta := typof_atom te a in
        let* va := eval_atom te ge le ta a in
        let vcases := MapList.map (eval_tailcomp_rec te ge le ty) cases in
        eval_match tabs ta va  vcases
    | TcAttr _ tc1 => eval_tailcomp_rec te ge le ty tc1
    end.

  Definition eval_tailcomp (te: tenv) (ge: genv) (le: lenv) (tr: typ) (tc: tailcomp) : option (eval_typ tr) :=
    let* (v, _) :=  (eval_tailcomp_rec te ge le tr tc) in
    ret v.

  Definition eval_prog (impl: genv) (prog: program) : option (tenv * genv) :=
    Denot.eval_prog tabs  eval_tailcomp impl prog.

End DENOT.

