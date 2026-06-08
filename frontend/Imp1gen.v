From Stdlib Require Import List String Lia Eqdep RelationClasses.
From BarocqComp Require Import Res Utils Brecord Types Syntax ImpBNF Imp1 Maps2 Denot Imp1Pure.
Import ListNotations.

Local Open Scope error_monad_scope.
Close Scope Z_scope.
Open Scope string_scope.

Fixpoint norm_begin (x: ident) (t: ImpBNF.tailcomp) : res Imp1.statement :=
  match t with
  | ImpBNF.TcBegin x1 t1 t2 _ =>
      do s1 <- norm_begin x1 t1;
      do s2 <- norm_begin x t2;
      eret (StSequence s1 s2)
  | ImpBNF.TcIfThenElse a t1 t2 _ =>
      do s1 <- norm_begin x t1;
      do s2 <- norm_begin x t2;
      eret (StIfThenElse a s1 s2)
  | ImpBNF.TcSwitch a cases _ =>
      do cases' <-
        Utils.list_fold_right_err
          (fun '(ci, ti) acc =>
              do si <- norm_begin x ti;
              eret ((ci, si) :: acc))
          nil
          cases;
      eret (StSwitch a cases')
  | ImpBNF.TcComp c => eret (StSet x c)
  | ImpBNF.TcAttr a t1 =>
      do s1 <- norm_begin x t1;
      eret (StAttr a s1)
  end.

Fixpoint norm_tailcomp (t: ImpBNF.tailcomp) : res Imp1.statement :=
  match t with
  | ImpBNF.TcBegin x t1 t2 _ =>
      do s1 <- norm_begin x t1;
      do s2 <- norm_tailcomp t2;
      eret (StSequence s1 s2)
  | ImpBNF.TcIfThenElse a t1 t2 _ =>
      do t1' <- norm_tailcomp t1;
      do t2' <- norm_tailcomp t2;
      eret (StIfThenElse a t1' t2')
  | ImpBNF.TcSwitch a cases _ =>
      do cases' <- MapList.map_err norm_tailcomp cases;
      eret (StSwitch a cases')
  | ImpBNF.TcComp c =>
      match c with
      | CpAtom a => eret (StReturn a)
      | _ => eret (StSequence (StSet "res" c) (StReturn (AVar "res" (btypof_comp c))))
      end
  | ImpBNF.TcAttr a c =>
      do t1 <- norm_tailcomp c;
      eret (StAttr a t1)
  end.

Definition norm_function (te: Typing.tenv) (f: ImpBNF.function) : res Imp1.function :=
  if wf_tailcomp te (fn_body f) then
    do body <- norm_tailcomp (fn_body f);
    eret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}
  else efail.

Definition norm_globdef (te: Typing.tenv) (def: ImpBNF.globdef) : res Imp1.globdef :=
  match def with
  | DefConst x l ty => eret (DefConst x l ty)
  | DefFun x f =>
      do f' <- norm_function te f;
      eret (DefFun x f')
  | DeclConst x ty => eret (DeclConst x ty)
  | DeclFun f tparams tret => eret (DeclFun f tparams tret)
  end.

Definition norm_program (prog: ImpBNF.program) : res Imp1.program :=
  do te <- Res.of_opt (Typing.tenv_of_type_defs (prog_types prog));
  do defs <- mmap (norm_globdef te) (prog_defs prog);
  let prog' := {|
    prog_defs := defs;
    prog_types := prog_types prog;
    prog_tabs := prog_tabs prog
  |} in
  eret prog'.

Section CORRECTNESS.

  Variable tabs : Maps.PMap.t Type.

  Import Option.

  Lemma norm_begin_correct_fw:
    forall te ge tc i s le le' ty v,
      norm_begin i tc = OK s ->
      ImpBNF.eval_tailcomp_rec tabs te ge le ty tc = Some (v, le') ->
      Imp1Pure.eval_statement_rec tabs te ge le None s =
      Some (Denot.lenv_update tabs le' i (Denot.Val tabs ty v)).
  Proof.
    induction tc using tailcomp_depth_ind; simpl; intros.
    - Res.monadInv H. inv EQ2.
      simpl. simpl in H0. monadInv H0.
      rename x0 into s1, x1 into s2, x2 into ty1, 
      x3 into v1, x4 into le1.
      eapply IHtc1 with (i := x) (s := s1) (le := le) (le' := le1) in EQ3; eauto.
      rewrite EQ3; simpl. eapply IHtc2 with (i := i) (s := s2) in EQ4; eauto.
    - monadInv H0. inv EQ2. inv H. erase_cast EQ1. simpl.
      rewrite EQ; simpl. rewrite EQ1; simpl. reflexivity.
    - Res.monadInv H. monadInv H0.
      rename x into s1, x0 into s2, x1 into va.
      inv EQ2. simpl; rewrite EQ0; simpl. destruct va; simpl.
      eapply IHtc1; eauto. eapply IHtc2; eauto.
    - Res.monadInv H0. monadInv H1. inv EQ0.
      rename x0 into ta, x1 into va. simpl.
      rewrite EQ1; simpl. rewrite EQ3; simpl.
      destruct ta; try discriminate. simpl in EQ4; simpl.
      rename x into cases'.
      revert ty H i le le' ty0 v cases' EQ i0 l EQ1 va EQ3 EQ4.
      induction cases; simpl; intros.
      + discriminate.
      + Res.monadInv EQ. destruct a0. simpl in EQ4.
        Res.monadInv EQ2. inv EQ5. simpl.
        destruct p.
        * monadInv EQ4. rewrite EQ2; simpl.
          destruct (Benum.enum_eq x1 va).
          -- eapply H; eauto.
          -- eapply IHcases; eauto.
        * eapply H; eauto.
    - Res.monadInv H. inv EQ0. simpl.
      eapply IHtc; eauto.
  Qed.

  Lemma norm_tailcomp_correct_fw :
    forall tc s te ge le le' ty (v: eval_typ tabs ty),
      norm_tailcomp tc = OK s ->
      ImpBNF.eval_tailcomp_rec tabs te ge le ty tc = Some (v, le') ->
      Imp1Pure.eval_statement_rec tabs te ge le (Some ty) s = Some v.
  Proof.
    induction tc using tailcomp_depth_ind; simpl; intros.
    - monadInv H0. Res.monadInv H. inv EQ5.
      simpl. eapply norm_begin_correct_fw in EQ1; eauto.
      rewrite EQ1; simpl. eapply IHtc2; eauto.
    - monadInv H0. inv EQ2.
      destruct c eqn:Ec; simpl in EQ.
      1: { inv H. erase_cast EQ1.
           simpl; simpl in EQ1.
           unfold Typing.typof_comp in EQ. simpl in EQ.
           unfold Typing.typof_atom.
           rewrite EQ; simpl. rewrite ecast_typ_id.
           exact EQ1. }
      all: ltac:(inversion H; rewrite <- Ec in *; simpl;
        rewrite EQ; simpl;
        erase_cast EQ1; rewrite EQ1; simpl;
        unfold Typing.typof_atom; simpl; unfold Typing.typof_comp in EQ;
        simpl in EQ; rewrite EQ; simpl;
        rewrite ecast_typ_id; unfold eval_var;
        unfold lenv_get, lenv_update; rewrite STree.gss; simpl;
        apply cast_typ_id).
    - Res.monadInv H. inv EQ2.
      monadInv H0. simpl.
      rewrite EQ0; simpl.
      destruct x1.
      + eapply IHtc1; eauto.
      + eapply IHtc2; eauto.
    - Res.monadInv H0. inv EQ0.
      monadInv H1. simpl.
      rename x into cases'.
      rename x0 into ta.
      rename x1 into va.
      rewrite EQ0; simpl. rewrite EQ2; simpl.
      destruct ta; try discriminate.
      unfold ImpBNF.eval_match in EQ3.
      unfold Imp1Pure.eval_match.
      revert le le' cases' EQ va EQ2 EQ3.
      clear - H l.
      {
        induction cases; intros.
        + simpl in EQ3. discriminate.
        + destruct a0. simpl in va, EQ3, EQ.
          Res.monadInv EQ. destruct p.
          * monadInv EQ3. Res.monadInv EQ0. inv EQ5. simpl.
            rewrite EQ1; simpl.
            destruct (Benum.enum_eq x1 va).
            -- eapply H with (p := Benum.PIdent i0 z); eauto.
               apply List.in_eq.
            -- simpl in H. eapply IHcases; eauto.
          * Res.monadInv EQ0. inv EQ4. simpl.
            eapply H with (p := Benum.PWildcard); eauto.
            apply List.in_eq.
      }
    - Res.monadInv H. inv EQ0.
      simpl. eapply IHtc; eauto.
  Qed.

  Lemma norm_begin_correct_bw:
  forall te ge tc i s le le' ty
    (TYPOF_TAIL: typof_tailcomp te tc = Some ty)
    (WF_TAIL: wf_tailcomp te tc = true),
    norm_begin i tc = OK s ->
    Imp1Pure.eval_statement_rec tabs te ge le None s = Some le' ->
    (exists v le1,
      ImpBNF.eval_tailcomp_rec tabs te ge le ty tc = Some (v, le1) /\
      lenv_update tabs le1 i (Val tabs ty v) = le').
  Proof.
    induction tc using tailcomp_depth_ind; simpl; intros.
    - Res.monadInv H. inv EQ2. rename x0 into s1, x1 into s2.
      destruct_conj WF_TAIL.
      pose proof C2. apply wf_tailcomp_btyp_to_typ in H.
      destruct H. unfold typof_tailcomp. rewrite H; simpl.
      simpl in H0. monadInv H0.
      eapply IHtc1 in EQ0; eauto. destruct EQ0 as [v1 [le1 [EVAL_TC1 LE1_UPDATE]]].
      rewrite EVAL_TC1; simpl. rename x1 into le1'.
      pose proof C0. apply wf_tailcomp_btyp_to_typ in H0.
      destruct H0. unfold typof_tailcomp. rename x1 into ty2.
      rewrite LE1_UPDATE. eapply IHtc2 with (ty := ty0) (i := i) in EQ2; eauto.
      unfold typof_tailcomp in TYPOF_TAIL. simpl in TYPOF_TAIL.
      rewrite btyp_eqb_eq in C3. unfold typof_tailcomp.
      rewrite C3. exact TYPOF_TAIL.
    - inv H. simpl in H0. monadInv H0. inv EQ2.
      rewrite EQ; simpl. rewrite EQ1; simpl.
      unfold typof_tailcomp in TYPOF_TAIL.
      simpl in TYPOF_TAIL. unfold Typing.typof_comp in EQ.
      rewrite EQ in TYPOF_TAIL. inv TYPOF_TAIL.
      rewrite ecast_typ_id; simpl. eauto.
    - destruct_conj WF_TAIL. Res.monadInv H.
      inv EQ2. simpl in H0. monadInv H0.
      rewrite EQ0; simpl.
      unfold typof_tailcomp in TYPOF_TAIL.
      simpl in TYPOF_TAIL.
      rewrite btyp_eqb_eq in C4, C3. destruct x1.
      eapply IHtc1; eauto. unfold typof_tailcomp. congruence.
      eapply IHtc2; eauto. unfold typof_tailcomp. congruence.
    - destruct_conj WF_TAIL. Res.monadInv H0. inv EQ0.
      simpl in H1. monadInv H1. rewrite EQ0; simpl.
      rewrite EQ2; simpl.
      rename x0 into ta, x1 into va, x into cases'.
      destruct ta; try discriminate.
      simpl in EQ3; simpl.
      revert ty H i le le' ty0 TYPOF_TAIL C1 C2 C0 cases' EQ i0 l EQ0 va EQ2 EQ3.
      {
        induction cases; simpl; intros.
        - inv EQ. simpl in EQ3. discriminate.
        - Res.monadInv EQ. destruct a0; simpl.
          Res.monadInv EQ4. inv EQ5. simpl in EQ3.
          destruct_conj C2. destruct_conj C0.
          unfold typof_tailcomp in TYPOF_TAIL.
          simpl in TYPOF_TAIL.
          pose proof C2.
          apply wf_tailcomp_btyp_to_typ in C2.
          destruct C2. apply btyp_eqb_eq in C.
          destruct p.
          + destruct (Benum.make_enum l i1); simpl in *.
            * destruct (Benum.enum_eq e va).
              -- eapply H; eauto.
                  unfold typof_tailcomp. congruence.
              -- rename x into cases'. rename x0 into s.
                  eapply IHcases; eauto.
            * discriminate.
          + eapply H; eauto. unfold typof_tailcomp.
            congruence.    
      }
    - Res.monadInv H. inv EQ0.
      eapply IHtc; eauto.
  Qed.

  Lemma norm_tailcomp_correct_bw:
    forall tc s te ge le ty (v: eval_typ tabs ty)
    (WF_TAIL: wf_tailcomp te tc = true),
      norm_tailcomp tc = OK s ->
      Imp1Pure.eval_statement_rec tabs te ge le (Some ty) s = Some v ->
      (exists le', ImpBNF.eval_tailcomp_rec tabs te ge le ty tc = Some (v, le')).
  Proof.
    induction tc using tailcomp_depth_ind; simpl; intros.
    - destruct_conj WF_TAIL. Res.monadInv H. inv EQ2.
      rename x0 into s1, x1 into s2.
      pose proof C2. eapply wf_tailcomp_btyp_to_typ in C2.
      destruct C2. unfold typof_tailcomp. rewrite H1; simpl.
      simpl in H0. monadInv H0. simpl in x1. 
      rename x0 into t1, x1 into le1.
      eapply norm_begin_correct_bw in EQ0; eauto.
      destruct EQ0 as [v1 [le' [EVAL_TC1 LE2_UPDATE]]].
      rewrite EVAL_TC1; simpl. rewrite LE2_UPDATE.
      eapply IHtc2 in EQ2; eauto.
    - destruct c eqn:Ec.
      1: { inv H. monadInv H0. erase_cast EQ0.
           simpl; simpl in EQ0. unfold Typing.typof_atom in EQ.
           unfold Typing.typof_comp. simpl. rewrite EQ; simpl.
           rewrite ecast_typ_id. rewrite EQ0; simpl. eauto. }
      all: ltac:(rewrite <- Ec in *; simpl; clear Ec; inv H; simpl in H0;
        monadInv H0; monadInv EQ; rewrite EQ0; simpl; inv EQ4;
        erase_cast EQ2; unfold Typing.typof_comp in EQ0;
        unfold Typing.typof_atom in EQ1; simpl in EQ1;
        rewrite EQ1 in EQ0; inv EQ0; rewrite ecast_typ_id;
        rewrite EQ; simpl; unfold lenv_update in EQ2;
        unfold eval_var in EQ2; unfold lenv_get in EQ2;
        rewrite STree.gss in EQ2; unfold cast_value in EQ2;
        rewrite cast_typ_id in EQ2; inv EQ2; eauto;
        apply convertible_btyp_iff in WF_TAIL; destruct WF_TAIL;
        unfold Typing.typof_comp; rewrite H1; simpl;
        rewrite <- H2 in H0).
    - destruct_conj WF_TAIL. Res.monadInv H.
      inv EQ2. rename x into s1, x0 into s2.
      simpl in H0. monadInv H0.
      rename x into va. rewrite EQ0; simpl.
      destruct va.
      + eapply IHtc1; eauto.
      + eapply IHtc2; eauto.
    - destruct_conj WF_TAIL. Res.monadInv H0.
      inv EQ0. rename x into cases'. simpl in H1.
      monadInv H1. rename x into ta, x0 into va.
      rewrite EQ0; simpl. rewrite EQ2; simpl.
      destruct ta; try discriminate.
      simpl in EQ3; simpl.
      revert ty H te ge le ty0 v C1 C2 C0 cases' EQ i l EQ0 va EQ2 EQ3.
      {
        induction cases; simpl; intros.
        - inv EQ. simpl in EQ3. discriminate.
        - Res.monadInv EQ. destruct a0. Res.monadInv EQ1.
          inv EQ5. rename x0 into cases', x1 into s.
          simpl in EQ3. simpl. destruct_conj C2.
          destruct_conj C0. destruct p.
          + monadInv EQ3. rewrite EQ1; simpl.
            destruct (Benum.enum_eq x va).
            * eapply H; eauto.
            * eapply IHcases; eauto.
          + eapply H; eauto.
      }
    - Res.monadInv H. inv EQ0. simpl in H0.
      eapply IHtc; eauto.
  Qed. 

  Theorem norm_tailcomp_correct:
    forall te ge le tc s ty,
      wf_tailcomp te tc = true ->
      norm_tailcomp tc = OK s ->
      Imp1Pure.eval_statement tabs te ge le ty s =
      ImpBNF.eval_tailcomp tabs te ge le ty tc.
  Proof.
    unfold ImpBNF.eval_tailcomp, Imp1Pure.eval_statement; intros.
    destruct (eval_tailcomp_rec tabs te ge le ty tc) as [[v le']|] eqn:Eeval_tc;
    simpl.
    - erewrite norm_tailcomp_correct_fw; eauto.
    - destruct (eval_statement_rec tabs te ge le (Some ty) s) eqn:Eeval_s; simpl.
      + eapply norm_tailcomp_correct_bw in Eeval_s; eauto.
        destruct Eeval_s. rewrite H1 in Eeval_tc. discriminate.
      + reflexivity.
  Qed.

  Lemma norm_function_correct_aux:
    forall params tc s te ge le tret,
      wf_tailcomp te tc = true ->
      norm_tailcomp tc = OK s ->
      eval_fun_rec tabs (Imp1Pure.eval_statement tabs) te ge le params tret s =
      eval_fun_rec tabs (ImpBNF.eval_tailcomp tabs) te ge le params tret tc.
    Proof.
      induction params; intros.
      - simpl. apply Axioms.functional_extensionality; intros.
        eapply norm_tailcomp_correct; eauto.
      - simpl. destruct params.
        + apply Axioms.functional_extensionality; intros.
          eapply norm_tailcomp_correct; eauto.
        + apply Axioms.functional_extensionality; intros.
          eapply IHparams; eauto.
    Qed.

  Lemma norm_function_correct:
    forall f f' te ge x,
    norm_function te f = OK f' ->
    eval_def_fun tabs (Imp1Pure.eval_statement tabs) te ge x f' =
    eval_def_fun tabs (ImpBNF.eval_tailcomp tabs) te ge x f.
  Proof.
    unfold norm_function; intros.
    destruct (wf_tailcomp te (fn_body f)) eqn:Ewf_body.
    + Res.monadInv H. inv EQ0. destruct f; simpl in *.
      unfold eval_def_fun; simpl.
      destruct (MapList.nodup Ident.eq_dec fn_params); try reflexivity.
      destruct (Typing.btyp_to_typ te fn_return); try reflexivity.
      destruct (map_err
        (Typing.btyp_to_typ te) fn_params); try reflexivity.
      simpl. repeat f_equal. unfold eval_fun.
      apply norm_function_correct_aux; auto.
    + discriminate.
  Qed.

  Lemma norm_globdef_correct:
    forall te impl ge d d',
      norm_globdef te d = OK d' ->
      eval_globdef tabs (Imp1Pure.eval_statement tabs) te impl ge d' =
      eval_globdef tabs (ImpBNF.eval_tailcomp tabs) te impl ge d.
  Proof.
    destruct d; simpl; intros.
    - inv H. simpl. reflexivity.
    - Res.monadInv H. inv EQ0. simpl.
      apply norm_function_correct. exact EQ.
    - inv H. simpl. reflexivity.
    - inv H. simpl. reflexivity.
  Qed.

  Lemma norm_program_correct_aux:
    forall te impl defs defs' a0,
      Res.mmap (norm_globdef te) defs = OK defs' ->
      Option.fold_left_err
        (fun acc d =>
          eval_globdef tabs  (eval_statement tabs) te impl acc d) defs' a0 =
      Option.fold_left_err
        (fun acc d =>
          eval_globdef tabs  (eval_tailcomp tabs) te impl acc d) defs a0.
  Proof.
    induction defs; intros.
    - simpl in H. inv H. simpl. reflexivity.
    - simpl in H. Res.monadInv H. simpl.
      erewrite norm_globdef_correct; eauto.
      destruct
        (eval_globdef tabs (eval_tailcomp tabs) te impl a0 a);
        try reflexivity.
      simpl; auto.
  Qed.

  Theorem norm_program_correct:
    forall impl p p',
      norm_program p = OK p' ->
      Imp1Pure.eval_prog tabs impl p' =
      ImpBNF.eval_prog tabs impl p.
  Proof.
    intros. unfold norm_program in H.
    Res.monadInv H. inv EQ2.
    destruct p; simpl in *.
    apply ok_imp_some in EQ.
    unfold Imp1Pure.eval_prog, ImpBNF.eval_prog, Denot.eval_prog.
    simpl. rewrite EQ.
    simpl. f_equal.
    apply norm_program_correct_aux. exact EQ1.
  Qed.

End CORRECTNESS.
