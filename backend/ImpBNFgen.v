From Coq Require Import String List Eqdep.
From compcert Require Import Coqlib.
From compcert Require Axioms.
From BarocqComp Require Import Error Syntax Utils Types BarocqBNF ImpBNF Maps2 Denot.
Import ListNotations.

Open Scope string_scope.

Fixpoint transl_expr (e: expr) : res tailcomp :=
  match e with
  | EAtom a => ret (TcComp (CpAtom a))
  | EArraySet a1 a2 a3 ty => ret (TcComp (CpArraySet a1 a2 a3 ty))
  | ERecordUpdate a1 x a2 ty => ret (TcComp (CpRecordUpdate a1 x a2 ty))
  | EApp a args ty =>
      let* (fid, tf) :=
        match a with
        | AVar x tx => ret (x, tx)
        | _ => fail
        end
      in
      ret (TcComp (CpCall fid tf args ty))
  | ELetIn x e1 e2 ty =>
      let* tc1 := transl_expr e1 in
      let* tc2 := transl_expr e2 in
      ret (TcBegin (StSetTailcomp x tc1) tc2 ty)
  | EIfThenElse a e1 e2 ty =>
      let* tc1 := transl_expr e1 in
      let* tc2 := transl_expr e2 in
      ret (TcIfThenElse a tc1 tc2 ty)
  | EMatch a cases ty =>
      let* cases' := MapList.map_err transl_expr cases in
      ret (TcSwitch a cases' ty)
  | EAttr id e =>
      let* tc := transl_expr e in
      ret (TcAttr id tc)
  end.

Definition check_params_noshadow {A T: Type} (ge: STree.t A) (ls_init: SSet.t) (params: smaplist T) : res SSet.t :=
  list_fold_left_err
    (fun acc '(pi, _) =>
      match STree.get pi ge with
      | Some _ => fail
      | None =>
        if negb (SSet.mem pi acc) then ret (SSet.add pi acc)
        else fail
      end)
    params
    (ls_init).

Definition transl_function (gs: SSet.t) (f: BarocqBNF.function) : res ImpBNF.function :=
  let* ls := check_params_noshadow gs SSet.empty (fn_params f) in
  if wf_expr gs ls (fn_body f) then
    let* body := transl_expr (fn_body f) in
    ret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}
  else fail.

Definition transl_globdef (gs: SSet.t) (def: BarocqBNF.globdef) : res ImpBNF.globdef :=
  match def with
  | DefConst x l ty => ret (DefConst x l ty)
  | DefFun x f =>
      let* f' := transl_function gs f in
      ret (DefFun x f')
  | DeclConst x ty => ret (DeclConst x ty)
  | DeclFun f tparams tret => ret (DeclFun f tparams tret)
  end.

Fixpoint transl_prog_defs (gs: SSet.t) (defs: list BarocqBNF.globdef) : res (list ImpBNF.globdef) :=
  match defs with
  | nil => ret nil
  | d :: defs' =>
      let* d' := transl_globdef gs d in
      let* dr := transl_prog_defs (SSet.add (globdef_id d) gs) defs' in
      ret (d' :: dr)
  end. 

Definition transl_program (prog: BarocqBNF.program) : res ImpBNF.program :=
  let* defs := transl_prog_defs SSet.empty (prog_defs prog) in
  ret {|
    prog_defs := defs;
    prog_types := prog_types prog;
    prog_tabs := prog_tabs prog;
  |}.

Section CORRECTNESS.

  Variable arch : Target.archi.

  Variable tabs : Maps.PMap.t Type.

  Notation genv := (@Denot.genv tabs).

  Notation lenv := (@Denot.lenv tabs).

  Theorem transl_expr_preserve_typ :
    forall te e tc,
      transl_expr e = OK tc ->
      ImpBNF.typof_tailcomp te tc = BarocqBNF.typof_expr te e.
  Proof.
    induction e; unfold BarocqBNF.typof_expr, ImpBNF.typof_tailcomp,
    ImpBNF.btypof_tailcomp; simpl; intros.
    - inversion H. reflexivity.
    - inversion H. reflexivity.
    - inversion H. reflexivity. 
    - destruct a; try discriminate.
      inv H. reflexivity.
    - monadInv H. inv EQ2. reflexivity.
    - monadInv H. inv EQ0. reflexivity.
    - monadInv H. inv EQ2. reflexivity.
    - monadInv H. inv EQ0. eapply IHe; eauto.
  Qed.
  
  (* Defines wether environment e2 shadows some variables of environment e1 *)
  Definition env_noshadow {A B} (e1: STree.t A) (e2: STree.t B) : Prop :=
    forall x v,
      STree.get x e1 = Some v ->
      STree.get x e2 = None.

  Lemma env_noshadow_set:
    forall (A B: Type) (e1: STree.t A) (e2: STree.t B) x,
      env_noshadow e1 e2 ->
      STree.get x e1 = None ->
      (forall b, env_noshadow e1 (STree.set x b e2)).
  Proof.
    unfold env_noshadow. intros.
    specialize (H _ _ H1).
    destruct (string_dec x0 x).
    - subst. congruence.
    - rewrite STree.gso; tauto.
  Qed.

  Definition match_lenv (le1 le2: lenv) : Prop :=
    forall x v,
      lenv_get tabs le1 x = Some v ->
      lenv_get tabs le2 x = Some v.

  Lemma match_lenv_refl:
    forall (le: lenv), match_lenv le le.
  Proof.
    intros. unfold match_lenv. tauto.
  Qed.

  Lemma match_lenv_update1:
    forall (le: lenv) k v,
    lenv_get tabs le k = None ->
    match_lenv le (lenv_update tabs le k v).
  Proof.
    unfold match_lenv, eval_var; intros.
    destruct (Ident.eq_dec x k).
    - subst. rewrite H in H0. discriminate. 
    - unfold lenv_update. unfold lenv_get in *.
      rewrite STree.gso; auto.
  Qed.

  Lemma match_lenv_update2:
    forall (le1 le2: lenv) (k: string) v,
      match_lenv le1 le2 ->
      match_lenv (lenv_update tabs le1 k v) (lenv_update tabs le2 k v).
  Proof.
    unfold match_lenv, lenv_get, lenv_update; intros.
    destruct (Ident.eq_dec x k).
    - subst. rewrite STree.gss in H0. simpl in H0.
      inv H0. rewrite STree.gss. reflexivity.
    - rewrite STree.gso in *; try exact n.
      apply (H _ _ H0).
  Qed.

  Lemma match_lenv_trans:
    forall (le1 le2 le3: lenv),
      match_lenv le1 le2 ->
      match_lenv le2 le3 ->
      match_lenv le1 le3.
  Proof.
    unfold match_lenv; intros.
    specialize (H _ _ H1). specialize (H0 _ _ H).
    exact H0.
  Qed.

  Lemma eval_var_match_lenv_eq:
    forall ge le1 le2 x ty v,
      env_noshadow ge le2 ->
      match_lenv le1 le2 ->
      ((lenv_get tabs le1 x = Some v) \/ (genv_get tabs ge x = Some v)) ->
      eval_var tabs ge le2 x ty = eval_var tabs ge le1 x ty.
  Proof.
    unfold env_noshadow, match_lenv, eval_var; intros.
    destruct H1.
    - specialize (H0 x v H1). rewrite H0, H1. reflexivity.
    - destruct (lenv_get tabs le1 x) eqn:Eget1.
      * specialize (H0 _ _ Eget1). rewrite H0. reflexivity.
      * rewrite H1; simpl. unfold genv_get in H1.
        specialize (H x v H1). unfold lenv_get. rewrite H. simpl. reflexivity.
  Qed.

  Theorem var_defined_env_get:
      forall ge le x,
        var_defined (STree.keys ge) (STree.keys le) x = true ->
        (exists v,
          (lenv_get tabs le x = Some v) \/
          (genv_get tabs ge x = Some v)).
    Proof.
      unfold var_defined, lenv_get, genv_get; intros.
      apply orb_prop in H. destruct H.
      - apply STree.keys_mem_true_get in H. destruct H.
        exists x0. left. rewrite H. reflexivity. 
      - apply STree.keys_mem_true_get in H. destruct H.
        exists x0. right. rewrite H. reflexivity.
    Qed.

  Theorem eval_atom_match_lenv_eq:
    forall te ge le1 le2,
    env_noshadow ge le2 ->
    match_lenv le1 le2 ->
    (forall a ty,
      wf_atom (STree.keys ge) (STree.keys le1) a = true ->
      eval_atom arch tabs te ge le2 ty a =
      eval_atom arch tabs te ge le1 ty a).
  Proof.
    induction a using atom_depth_ind; simpl; intros; try tauto.
    - apply var_defined_env_get in H1; try tauto.
      destruct H1. eapply eval_var_match_lenv_eq; eauto.
    - destruct (Typing.btyp_to_typ te t); simpl; try reflexivity.
      destruct (typof_atom te a); simpl; try reflexivity.
      erewrite IHa; eauto.
    - destruct (typof_atom te a); simpl; try reflexivity.
      erewrite IHa; eauto.
    - destruct (typof_atom te a1); simpl; try reflexivity.
      destruct (typof_atom te a2); simpl; try reflexivity.
      apply andb_prop in H1. destruct H1.
      erewrite IHa1; eauto.
      erewrite IHa2; eauto.
    - destruct (typof_atom te a1); simpl; try reflexivity.
      destruct (typof_atom te a2); simpl; try reflexivity.
      apply andb_prop in H1. destruct H1.
      erewrite IHa1; eauto.
      erewrite IHa2; eauto.
    - destruct (typof_atom te a); simpl; try reflexivity.
      erewrite IHa; eauto.
    - destruct (Typing.btyp_to_typ te tf); simpl; try reflexivity.
      apply andb_prop in H2. destruct H2.
      apply var_defined_env_get in H2; try tauto.
      destruct H2. destruct t; simpl; try reflexivity.
      erewrite eval_var_match_lenv_eq; eauto.
      destruct (eval_var tabs ge le1 i (TFun l t)); simpl; try reflexivity.
      assert (DList.map2 (eval_typ tabs) (eval_atom arch tabs te ge le2) args l =
                DList.map2 (eval_typ tabs) (eval_atom arch tabs te ge le1) args l).
      {
        apply DList.map2_eq.
        assert (forall x ty,
                   In x args ->
                       eval_atom arch tabs te ge le2 ty x =
                         eval_atom arch tabs te ge le1 ty x).
        {
          intros.
          apply H1; auto.
          rewrite forallb_forall in H3.
          auto.
        }
        clear - H4.
        induction args.
        - constructor.
        - constructor.
          intros.
          apply H4.
          simpl; tauto.
          eapply IHargs.
          intros. apply H4. simpl;tauto.
      }
      rewrite H4.
      reflexivity.
  Qed.

  Definition wf_comp (globs: SSet.t) (locals: SSet.t) (c: comp) : bool :=
    match c with
    | CpAtom a => wf_atom globs locals a
    | CpArraySet a1 a2 a3 _ =>
        (wf_atom globs locals a1) &&
        (wf_atom globs locals a2) &&
        (wf_atom globs locals a3)
    | CpRecordUpdate a1 _ a2 _ =>
        (wf_atom globs locals a1) &&
        (wf_atom globs locals a2)
    | CpCall f _ args _ =>
        (var_defined globs locals f) &&
        (List.forallb (wf_atom globs locals) args)
    end.

  Lemma eval_comp_match_lenv_eq:
    forall te ge le1 le2,
      env_noshadow ge le2 ->
      match_lenv le1 le2 ->
      (forall c ty, wf_comp (STree.keys ge) (STree.keys le1) c = true ->
        eval_comp arch tabs te ge le2 ty c =
        eval_comp arch tabs te ge le1 ty c).
  Proof.
    induction c; simpl; intros.
    - apply eval_atom_match_lenv_eq; tauto.
    - destruct_conj H1.
      destruct (typof_atom te a); simpl; try reflexivity.
      destruct (typof_atom te a0); simpl; try reflexivity.
      destruct (typof_atom te a1); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 t a); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 t0 a0); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
    - destruct_conj H1.
      destruct (typof_atom te a); simpl; try reflexivity.
      destruct (typof_atom te a0); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 t a); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
    - destruct_conj H1.
      destruct (Typing.btyp_to_typ te b); simpl; try reflexivity.
      destruct t; try reflexivity.
      eapply var_defined_env_get in C; eauto. destruct C.
      erewrite eval_var_match_lenv_eq; eauto.
      destruct (eval_var tabs ge le1 i (TFun l0 t)); simpl; try reflexivity.
      assert (EQ: DList.map2 (eval_typ tabs) (eval_atom arch tabs te ge le2) l l0 =
                DList.map2 (eval_typ tabs) (eval_atom arch tabs te ge le1) l l0).
      {
        apply DList.map2_eq.
        rewrite Forall_forall.
        intros.
        apply eval_atom_match_lenv_eq; auto.
        rewrite List.forallb_forall in C0.
        auto.
      }
      congruence.
  Qed.

  Import OptionMonad.

  Ltac destruct_bind :=
    match goal with
    | H : (bind ?V _) = Some _ |- context[?V] => destruct V; simpl in H
    end.

  Fixpoint transl_expr_correct_ok e:
    forall te ge le1 le2 ty tc v
      (WF_EXPR: wf_expr (STree.keys ge) (STree.keys le1) e = true)
      (NOSHADOW: env_noshadow ge le2)
      (MATCH_LENV: match_lenv le1 le2)
      (TRANSL: transl_expr e = OK tc)
      (EVAL_EXPR: BarocqBNF.eval_expr_rec arch tabs te ge le1 ty e = Some v),
      (exists le2', ImpBNF.eval_tailcomp_rec arch tabs te ge le2 ty tc = Some (v, le2')
        /\ env_noshadow ge le2'
        /\ match_lenv le1 le2').
  Proof.
    destruct e; simpl; intros.
    (* atom *)
    - inv TRANSL. monadInv EVAL_EXPR. simpl. eexists.
      repeat split; eauto. unfold typof_atom in EQ.
      rewrite EQ; simpl. erase_cast EQ0.
      erewrite eval_atom_match_lenv_eq; simpl; eauto.
      rewrite ecast_typ_id.  setoid_rewrite EQ0; simpl. reflexivity.
    (* array set *)
    - inv TRANSL. simpl.
      repeat destruct_bind; try discriminate.
      simpl.
      monadInv EVAL_EXPR. destruct_conj WF_EXPR.
      erewrite eval_atom_match_lenv_eq; eauto.
      rew EQ.
      erewrite eval_atom_match_lenv_eq; eauto.
      rew EQ1. simpl.
      erewrite eval_atom_match_lenv_eq; eauto.
      rew EQ0. simpl.
      setoid_rewrite EQ3.
      eexists. simpl. split; eauto.
    (* record update *)
    -
      inv TRANSL; simpl.
      repeat destruct_bind; try discriminate.
      simpl.  destruct_conj WF_EXPR.
      monadInv EVAL_EXPR.
      erewrite eval_atom_match_lenv_eq; eauto.
      rew EQ; simpl.
      erewrite eval_atom_match_lenv_eq; eauto.
      rew EQ1; simpl. setoid_rewrite EQ2.
      exists le2; repeat split; auto.
    (* application *)
    - destruct a; simpl; try discriminate.
      simpl in TRANSL. inv TRANSL. simpl.
      destruct_conj WF_EXPR. simpl in C.
      apply var_defined_env_get in C; try tauto. destruct C.
      simpl in EVAL_EXPR. monadInv EVAL_EXPR.
      unfold typof_atom in EQ1. simpl in EQ1.
      rewrite EQ, EQ1; simpl.
      destruct x1; try discriminate.
      monadInv EQ2.
      erewrite eval_var_match_lenv_eq; eauto. rewrite EQ0; simpl.
      assert (EQM: DList.map2 (eval_typ tabs) (eval_atom arch tabs te ge le2) l l0 =
                DList.map2 (eval_typ tabs) (eval_atom arch tabs te ge le1) l l0).
      {
        apply DList.map2_eq.
        rewrite Forall_forall.
        intros.
        apply eval_atom_match_lenv_eq; auto.
        rewrite List.forallb_forall in C0.
        auto.
      }
      setoid_rewrite EQ2 in EQM.
      rew EQM. simpl.
      setoid_rewrite EQ4. simpl.
      exists le2. repeat split. 
      exact NOSHADOW. exact MATCH_LENV.
    (* if-then-else *)
    - Res.monadInv TRANSL. inv EQ2. simpl. monadInv EVAL_EXPR.
      destruct_conj WF_EXPR.
      erewrite eval_atom_match_lenv_eq; eauto.
      setoid_rewrite EQ0; simpl.
      destruct x1.
      eapply transl_expr_correct_ok with (e := e1); eauto.
      eapply transl_expr_correct_ok with (e := e2); eauto.
    (* match-with *)
    - Res.monadInv TRANSL. inv EQ0. monadInv EVAL_EXPR. simpl.
      destruct_conj WF_EXPR.
      setoid_rewrite EQ0; simpl. erewrite eval_atom_match_lenv_eq; eauto.
      setoid_rewrite EQ2; simpl.
      destruct x0; simpl in EQ3; try discriminate. unfold ImpBNF.eval_match.
      revert b le1 le2 ty v C C0 NOSHADOW MATCH_LENV x EQ i l0 EQ0 x1 EQ2 EQ3.
      induction l; intros.
      + simpl in EQ. inv EQ. simpl in EQ3. discriminate.
      + simpl in EQ. Res.monadInv EQ. destruct a0. Res.monadInv EQ1. inv EQ5.
        simpl in EQ3. simpl. simpl in C0. destruct_conj C0.
        destruct p.
        * monadInv EQ3. rewrite EQ1; simpl.
          destruct (Benum.enum_eq x0 x1).
          -- eapply transl_expr_correct_ok; eauto.
          -- eapply IHl; eauto.
        * eapply transl_expr_correct_ok; eauto.
    (* let-in *)
    - Res.monadInv TRANSL. inv EQ2. monadInv EVAL_EXPR. simpl.
      destruct_conj WF_EXPR. 
      pose proof (transl_expr_preserve_typ te _ _ EQ).
      rewrite H. rewrite EQ0; simpl.
      rename x1 into ty1. rename x2 into v1. rename x into tc1.
      rename x0 into tc2. rename v into v2.
      eapply transl_expr_correct_ok in EQ3; eauto. destruct EQ3. destruct_conj H0.
      rewrite C1; simpl. rename x into le2'.
      eapply transl_expr_correct_ok with
        (le1 := (lenv_update tabs le1 i (Val tabs ty1 v1)))
        (le2 := lenv_update tabs le2' i (Val tabs ty1 v1))
      in EQ4; eauto.
      destruct EQ4. destruct_conj H0.
      rename x into le2''.
      eexists. rewrite C4; repeat split.
      exact C8. apply match_lenv_trans with (le2 := (lenv_update tabs le1 i (Val tabs ty1 v1))).
      eapply match_lenv_update1. unfold lenv_get. apply negb_true_iff in C3.
      apply STree.keys_get_mem_false_iff in C3. rewrite C3. reflexivity. exact C9.
      unfold lenv_update. rewrite STree.keys_set. exact C0.
      apply env_noshadow_set. exact C5. apply negb_true_iff in C.
      apply STree.keys_get_mem_false_iff in C. exact C.
      apply match_lenv_update2. exact C6.
    (* attr *)
    - Res.monadInv TRANSL. inv EQ0. simpl. eapply transl_expr_correct_ok; eauto.
  Qed.

  Ltac ecast_typ_err_resolve :=
    try (unfold ecast_typ; destruct (typ_eq_dec _ _); subst; simpl); eauto.


  Fixpoint transl_expr_correct_err e:
    forall te ge le1 le2 ty tc
      (WF_EXPR: wf_expr (STree.keys ge) (STree.keys le1) e = true)
      (NOSHADOW: env_noshadow ge le2)
      (MATCH_LENV: match_lenv le1 le2)
      (TRANSL: transl_expr e = OK tc),
      BarocqBNF.eval_expr_rec arch tabs te ge le1 ty e = None ->
      (ImpBNF.eval_tailcomp_rec arch tabs te ge le2 ty tc = None).
  Proof.
    destruct e; simpl; intros.
    - inv TRANSL. simpl. unfold typof_atom in H.
      destruct (Typing.btyp_to_typ te (Syntax.typof_atom a)); simpl in H; simpl; eauto.
      erewrite eval_atom_match_lenv_eq; eauto. setoid_rewrite H; simpl; eauto.
    - inv TRANSL. destruct_conj WF_EXPR. simpl.
      destruct (Typing.btyp_to_typ te b); simpl in H; simpl; eauto.
      destruct (typof_atom te a); simpl in H; simpl; ecast_typ_err_resolve.
      destruct (typof_atom te a0); simpl in H; simpl; ecast_typ_err_resolve.
      destruct (typof_atom te a1); simpl in H; simpl; ecast_typ_err_resolve.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 t0 a); simpl in H; simpl; ecast_typ_err_resolve.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 t a0); simpl in H; simpl; ecast_typ_err_resolve.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 t1 a1); simpl in H; simpl; ecast_typ_err_resolve.
      destruct (eval_array_set arch tabs t0 e t e0 t1 e1 ty); simpl in H; simpl; eauto.
      rewrite ecast_typ_id in H. discriminate.
    - inv TRANSL. simpl. destruct_conj WF_EXPR.
      destruct (Typing.btyp_to_typ te b); simpl in H; simpl; eauto.
      destruct (typof_atom te a); simpl in H; simpl; ecast_typ_err_resolve.
      destruct (typof_atom te a0); simpl in H; simpl; ecast_typ_err_resolve.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 t0 a); simpl in H; simpl; ecast_typ_err_resolve.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 t a0); simpl in H; simpl; ecast_typ_err_resolve.
      destruct (eval_record_update tabs t0 e i t e0 ty); simpl in H; simpl; eauto.
      rewrite ecast_typ_id in H. discriminate. 
    - destruct a; simpl in H; try discriminate.
      simpl in TRANSL. inv TRANSL. simpl.
      destruct_conj WF_EXPR.
      unfold typof_atom in H. simpl in H.
      destruct (Typing.btyp_to_typ te b); simpl in H; simpl; eauto.
      destruct (Typing.btyp_to_typ te b0); simpl in H; simpl; ecast_typ_err_resolve.
      destruct t0; simpl; unfold efail in H; eauto.
      simpl in C. eapply var_defined_env_get in C; destruct C; eauto.
      erewrite eval_var_match_lenv_eq; eauto.
      destruct (eval_var tabs ge le1 i (TFun l0 t0)); simpl in H; simpl; try congruence.
        assert (
            DList.map2 (eval_typ tabs) (eval_atom arch tabs te ge le2) l l0 =
              DList.map2 (eval_typ tabs) (eval_atom arch tabs te ge le1) l l0).
        {
          apply DList.map2_eq.
          apply Forall_forall.
          intros.
          apply eval_atom_match_lenv_eq; eauto.
          rewrite List.forallb_forall in C0.
          apply C0 ; auto.
        }
        destruct (DList.map2 (eval_typ tabs)
                    (eval_atom arch tabs te ge le1) l l0) eqn:Hmap2.
      + simpl in H.
        setoid_rewrite H1. simpl.
        rewrite ecast_typ_id in H.
        setoid_rewrite H. reflexivity.
      + simpl in H.
        setoid_rewrite H1. simpl. reflexivity.
    - Res.monadInv TRANSL. inv EQ2. simpl.
      destruct_conj WF_EXPR.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 TBool a); simpl in H; simpl; eauto.
      destruct e.
      + eapply transl_expr_correct_err with (e := e1); eauto.
      + eapply transl_expr_correct_err with (e := e2); eauto. 
    - Res.monadInv TRANSL. inv EQ0. simpl. destruct_conj WF_EXPR.
      destruct (typof_atom te a); simpl in H; simpl; eauto.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom arch tabs te ge le1 t a); simpl in H; simpl; eauto.
      destruct t; simpl in H; inv H; simpl; try unfold efail; eauto.
      revert b le1 le2 ty C C0 NOSHADOW MATCH_LENV i l0 e x EQ H1.
      induction l; intros.
      + simpl in EQ. inv EQ. simpl. unfold efail; eauto.
      + simpl in EQ. Res.monadInv EQ. destruct a0. Res.monadInv EQ0.
        inv EQ2. simpl in C0. destruct_conj C0.
        simpl in H1. simpl. destruct p.
        * destruct (Benum.make_enum l0 i0); simpl in H1; simpl; eauto.
          destruct (Benum.enum_eq e1 e).
          -- eapply transl_expr_correct_err; eauto.
          -- eapply IHl; eauto.
        * eapply transl_expr_correct_err; eauto.
    - simpl in TRANSL. Res.monadInv TRANSL.
      inv EQ2. simpl. destruct (typof_expr te e1) eqn:Etypof_expr; simpl in H.
      + rewrite transl_expr_preserve_typ with (e := e1). 
        rewrite Etypof_expr. simpl.
        simpl in WF_EXPR. apply andb_prop in WF_EXPR. destruct WF_EXPR.
        apply andb_prop in H0. destruct H0. apply andb_prop in H0. destruct H0.
        destruct (eval_expr_rec arch tabs te ge le1 t e1) eqn:Eeval_e1; simpl in H.
        * eapply transl_expr_correct_ok in Eeval_e1; eauto.
          destruct Eeval_e1 as [le2' [EVAL_TC [NOSHADOW_LE2' MATCH_LENV_LE2']]].
          rewrite EVAL_TC. simpl. eapply transl_expr_correct_err with (e := e2); eauto.
          unfold lenv_update. rewrite STree.keys_set. exact H1.
          unfold lenv_update. apply env_noshadow_set. exact NOSHADOW_LE2'.
          unfold negb in H0. destruct (SSet.mem i (STree.keys ge)) eqn:Hmemi; try discriminate.
          apply STree.keys_get_mem_false_iff. exact Hmemi.
          apply match_lenv_update2. exact MATCH_LENV_LE2'.
        * eapply transl_expr_correct_err in Eeval_e1; eauto.
          rewrite Eeval_e1. simpl. reflexivity.
        * exact EQ. 
      + inv H. rewrite transl_expr_preserve_typ with (e := e1).
        rewrite Etypof_expr. simpl. eauto.
        exact EQ.
    - Res.monadInv TRANSL. inv EQ0. simpl.
      eapply transl_expr_correct_err; eauto.
  Qed.

  Lemma transl_expr_correct:
    forall e te ge le1 le2 ty tc
    (WF_EXPR: wf_expr (STree.keys ge) (STree.keys le1) e = true)
    (NOSHADOW: env_noshadow ge le2)
    (MATCH_LENV: match_lenv le1 le2)
    (TRANSL: transl_expr e = OK tc),
      ImpBNF.eval_tailcomp arch tabs te ge le2 ty tc =
      BarocqBNF.eval_expr arch tabs te ge le1 ty e. 
  Proof.
    intros. unfold eval_expr, eval_tailcomp. 
    destruct (eval_expr_rec arch tabs te ge le1 ty e) eqn:Eeval_e.
    - eapply transl_expr_correct_ok in Eeval_e; eauto.
      destruct Eeval_e. destruct_conj H. rewrite C. reflexivity.
    - eapply transl_expr_correct_err in Eeval_e; eauto.
      rewrite Eeval_e. reflexivity.
  Qed.

  Lemma params_noshadow : 
    forall {A T: Type} (params: smaplist T) (ge: STree.t A) ls ls',
      env_noshadow ge ls ->
      check_params_noshadow ge ls params = OK ls' ->
      env_noshadow ge ls'.
  Proof.
    induction params; intros.
    - unfold check_params_noshadow in H0.
      simpl in H0. inv H0. assumption.
    - unfold check_params_noshadow in H0. simpl in H0. 
      destruct a. destruct (STree.get s ge) eqn:Hgets_ge;
        try discriminate.
      + destruct (SSet.mem s ls) eqn:Hmems_ls.
        * simpl in H0.
          discriminate.
        * simpl in H0.
          eapply IHparams with (ls := SSet.add s ls); eauto.
          apply env_noshadow_set. exact H. exact Hgets_ge.
  Qed.

  Lemma transl_function_correct_aux:
    forall params ls e tc te ge le tret
    (NOSHADOW: env_noshadow ge le)
    (CHECK_PARAMS: check_params_noshadow (STree.keys ge) (STree.keys le) params = OK ls)
    (WF_EXPR: wf_expr (STree.keys ge) ls e = true)
    (TRANSL: transl_expr e = OK tc),
      eval_fun_rec tabs  (eval_tailcomp arch tabs) te ge le params tret tc =
      eval_fun_rec tabs  (eval_expr arch tabs) te ge le params tret e.
  Proof.
    induction params; intros.
    - simpl. apply Axioms.functional_extensionality; intro.
      unfold check_params_noshadow in CHECK_PARAMS. 
      simpl in CHECK_PARAMS. inv CHECK_PARAMS.
      apply transl_expr_correct; try tauto.
      apply match_lenv_refl.
    - simpl. unfold check_params_noshadow in CHECK_PARAMS.
      simpl in CHECK_PARAMS.
      destruct params.
      + apply Axioms.functional_extensionality; intros.
        simpl in CHECK_PARAMS. destruct a.
        destruct (STree.get s (STree.keys ge)) eqn:Egets_ge; try discriminate.
        destruct (SSet.mem s (STree.keys le)); try discriminate.
        apply transl_expr_correct; auto.
        * simpl in *. inv CHECK_PARAMS.
          unfold lenv_update. rewrite STree.keys_set.
          exact WF_EXPR.
        * simpl in *. inv CHECK_PARAMS.
          unfold lenv_update. apply env_noshadow_set.
          exact NOSHADOW. apply STree.keys_get_none_iff. exact Egets_ge.
        * apply match_lenv_refl.
      + simpl in CHECK_PARAMS. destruct a. 
        destruct (STree.get s (STree.keys ge)) eqn:Egets_ge; try discriminate.
        destruct (SSet.mem s (STree.keys le)); try discriminate.
        simpl in CHECK_PARAMS.
        apply Axioms.functional_extensionality; intros.
        eapply IHparams; eauto; simpl.
        unfold lenv_update. apply env_noshadow_set; auto.
        apply STree.keys_get_none_iff. exact Egets_ge.
        unfold check_params_noshadow, lenv_update. simpl.
        rewrite STree.keys_set. exact CHECK_PARAMS. 
  Qed.

  Lemma transl_function_correct:
    forall f f' te ge x
    (TRANSL: transl_function (STree.keys ge) f = OK f'),
    eval_def_fun tabs (eval_tailcomp arch tabs) te ge x f' =
    eval_def_fun tabs (eval_expr arch tabs) te ge x f.
  Proof.
    unfold transl_function, eval_def_fun, eval_fun. intros.
    destruct f; simpl in TRANSL. Res.monadInv TRANSL. rename x0 into ls.
    destruct (wf_expr (STree.keys ge) ls fn_body) eqn:WF_EXPR; try discriminate. 
    Res.monadInv EQ0. rename x0 into tc. destruct f'. inv EQ2.
    simpl. destruct (MapList.nodup Ident.eq_dec fn_params0); try reflexivity.
    destruct (Typing.btyp_to_typ te fn_return0); simpl; try reflexivity.
    destruct (map_err _ _) eqn:H; simpl; try reflexivity. repeat f_equal.
    erewrite transl_function_correct_aux; eauto.
    unfold  env_noshadow; intros. reflexivity.
    simpl. unfold SSet.empty, SSet._Set.empty in EQ.
    assert (forall {A B C} (params: smaplist A) (ge: STree.t C) ls ls' f (params': smaplist B),
      check_params_noshadow ge ls params = OK ls' ->
      map_err f params = Some params' ->
      check_params_noshadow ge ls params' = OK ls').
    { clear; induction params; intros.
    - simpl in H0. inv H0. exact H.
    - simpl in H0. monadInv H0. destruct a. simpl in EQ.
      monadInv EQ.
      unfold check_params_noshadow. simpl.
      unfold check_params_noshadow in H. simpl in H.
      destruct (STree.get s ge); try discriminate.
      + destruct (SSet.mem s ls); simpl in H; try discriminate.
        simpl. eapply IHparams; eauto. }
    eapply H0; eauto.
  Qed.

  Lemma transl_globdef_correct:
    forall def def' te impl ge
    (TRANSL: transl_globdef (STree.keys ge) def = OK def'),
      eval_globdef tabs (eval_tailcomp arch tabs) te impl ge def' =
      eval_globdef tabs (eval_expr arch tabs) te impl ge def.
  Proof.
    intros. destruct def;
    simpl in TRANSL; inv TRANSL; try reflexivity.
    Res.monadInv H0. inv EQ0. simpl.
    apply transl_function_correct.
    exact EQ.
  Qed.

  Lemma eval_globdef_add_gid:
    forall (T: Type) eval_T te impl ge ge' def, 
      eval_globdef tabs (EXPR:=T) (eval_T arch tabs) te impl ge def = Some ge' ->
      STree.keys ge' = SSet.add (globdef_id def) (STree.keys ge).
  Proof.
    intros; destruct def; simpl in H.
    - unfold eval_def_const in H. monadInv H.
      unfold genv_update in EQ3.
      destruct (genv_get tabs ge i); try discriminate.
      inv EQ3. simpl. apply STree.keys_set.
    - unfold eval_def_fun in H.
      destruct (MapList.nodup Ident.eq_dec (fn_params f)); try discriminate.
      monadInv H. unfold genv_update in EQ2.
      destruct (genv_get tabs ge i); try discriminate.
      inv EQ2. simpl. apply STree.keys_set. 
    - unfold eval_decl_const in H. monadInv H.
      destruct (typ_eq_dec x (typeof_value tabs x0)); try discriminate.
      unfold genv_update in EQ2.
      destruct (genv_get tabs ge i); try discriminate.
      inv EQ2. simpl. apply STree.keys_set. 
    - unfold eval_decl_fun in H.
      Opaque typ_eq_dec. monadInv H.
      destruct (typ_eq_dec (TFun x x0) (typeof_value tabs x1)); try discriminate.
      unfold genv_update in EQ3. destruct (genv_get tabs ge i); inv EQ3.
      simpl. apply STree.keys_set.
  Qed. 

  Lemma transl_prog_defs_correct:
    forall defs defs' te impl ge
    (TRANSL: transl_prog_defs (STree.keys ge) defs = OK defs'),
      eval_prog_rec tabs (eval_tailcomp arch tabs) te impl ge defs'=
      eval_prog_rec tabs (eval_expr arch tabs) te impl ge defs.
  Proof.
    unfold eval_prog_rec.
    induction defs; intros.
    - simpl in TRANSL. inv TRANSL. simpl. reflexivity.
    - simpl in TRANSL. Res.monadInv TRANSL. inv EQ2.
      rename a into d. rename x into d'. rename x0 into defs'.
      simpl. rewrite transl_globdef_correct with (def := d); try exact EQ.
      destruct (eval_globdef tabs  (eval_expr arch tabs) te impl ge d) as [ge' |]eqn:Ege.
      + apply IHdefs. apply eval_globdef_add_gid in Ege.
        rewrite Ege. exact EQ1.
      + destruct defs.
        * simpl in EQ1. inv EQ1. reflexivity.
        * simpl in EQ1. Res.monadInv EQ1. inv EQ3. reflexivity.
  Qed.


  Theorem transl_prog_correct:
    forall impl p p'
    (TRANSL: transl_program p = OK p'),
      ImpBNF.eval_prog arch tabs impl p' = 
      BarocqBNF.eval_prog arch tabs impl p.
  Proof.
    intros. destruct p, p'.
    unfold transl_program in TRANSL. simpl in TRANSL.
    Res.monadInv TRANSL. inv EQ0.
    unfold ImpBNF.eval_prog, BarocqBNF.eval_prog.
    unfold Denot.eval_prog. simpl.
    destruct (Typing.tenv_of_type_defs prog_types0); simpl; try reflexivity.
    setoid_rewrite (transl_prog_defs_correct prog_defs prog_defs0 t impl STree.empty).
    reflexivity. simpl. exact EQ.
  Qed.

End CORRECTNESS.
