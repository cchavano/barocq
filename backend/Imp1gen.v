From Coq Require Import List String Lia Eqdep RelationClasses.
From BarocqComp Require Import Error Utils Brecord Types Syntax ImpBNF Imp1 Maps2 Denot Imp1Pure.
Import ListNotations.

Close Scope Z_scope.
Open Scope string_scope.

Fixpoint norm_statement (fuel: nat) (s: ImpBNF.statement) : res Imp1.statement :=
  match fuel with
  | O => fail
  | S fuel' =>
      let '(ImpBNF.StSetTailcomp x t) := s in
      match t with
      | ImpBNF.TcBegin s tc _ =>
          let* s' := norm_statement fuel' s in
          let* sc := norm_statement fuel' (ImpBNF.StSetTailcomp x tc) in
          ret (StSequence s' sc)
      | ImpBNF.TcIfThenElse a t1 t2 _ =>
          let* s1 := norm_statement fuel' (ImpBNF.StSetTailcomp x t1) in
          let* s2 := norm_statement fuel' (ImpBNF.StSetTailcomp x t2) in
          ret (StIfThenElse a s1 s2)
      | ImpBNF.TcSwitch a cases _ =>
          let* cases' :=
            Utils.list_fold_right_err
              (fun '(ci, ti) acc =>
                 let* si := norm_statement fuel' (ImpBNF.StSetTailcomp x ti) in
                 ret ((ci, si) :: acc))
              nil
              cases
          in
          ret (StSwitch a cases')
      | ImpBNF.TcComp c => ret (StSet x c)
      | ImpBNF.TcAttr a c =>
          let* s1 := norm_statement fuel' (StSetTailcomp x c) in
          ret (StAttr a s1)
      end
  end.

Fixpoint norm_tailcomp (t: ImpBNF.tailcomp) : res Imp1.statement :=
  match t with
  | ImpBNF.TcBegin s t1 _ =>
      let* s' := norm_statement (statement_depth s + 1) s in
      let* t1' := norm_tailcomp t1 in
      ret (StSequence s' t1')
  | ImpBNF.TcIfThenElse a t1 t2 _ =>
      let* t1' := norm_tailcomp t1 in
      let* t2' := norm_tailcomp t2 in
      ret (StIfThenElse a t1' t2')
  | ImpBNF.TcSwitch a cases _ =>
      let* cases' := MapList.map_err norm_tailcomp cases in
      ret (StSwitch a cases')
  | ImpBNF.TcComp c =>
      match c with
      | CpAtom a => ret (StReturn a)
      | _ => ret (StSequence (StSet "res" c) (StReturn (AVar "res" (btypof_comp c))))
      end
  | ImpBNF.TcAttr a c =>
      let* t1 := norm_tailcomp c in
      ret (StAttr a t1)
  end.

Definition norm_function (te: Typing.tenv) (f: ImpBNF.function) : res Imp1.function :=
  if wf_tailcomp te (fn_body f) then
    let* body := norm_tailcomp (fn_body f) in
    ret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}
  else fail.

Definition norm_globdef (te: Typing.tenv) (def: ImpBNF.globdef) : res Imp1.globdef :=
  match def with
  | DefConst x l ty => ret (DefConst x l ty)
  | DefFun x f =>
      let* f' := norm_function te f in
      ret (DefFun x f')
  | DeclConst x ty => ret (DeclConst x ty)
  | DeclFun f tparams tret => ret (DeclFun f tparams tret)
  end.

Definition norm_program (prog: ImpBNF.program) : res Imp1.program :=
  let* te := err_of_opt (Typing.tenv_of_type_defs (prog_types prog)) in
  let* defs := mmap (norm_globdef te) (prog_defs prog) in
  let prog' := {|
    prog_defs := defs;
    prog_types := prog_types prog;
    prog_tabs := prog_tabs prog
  |} in
  ret prog'.

Section CORRECTNESS.

  Lemma norm_statement_fuel_gt: 
    forall fuel fuel' (FUEL_GT: fuel' > fuel) s s1,
      norm_statement fuel s = OK s1 ->
      norm_statement fuel' s = OK s1.
  Proof.
    induction fuel; intros.
    - simpl in H. discriminate.
    - simpl in H. destruct fuel'; try lia.
      apply PeanoNat.lt_S_n in FUEL_GT.
      destruct s. destruct t.
      + monadInv H. inv EQ2. simpl. 
        rewrite IHfuel with (s1 := x); auto. simpl.
        rewrite IHfuel with (s1 := x0); auto.    
      + inv H. reflexivity.
      + monadInv H. inv EQ2. simpl.
        rewrite IHfuel with (s1 := x); auto. simpl.
        rewrite IHfuel with (s1 := x0); auto.
      + monadInv H. inv EQ0. simpl.
        specialize (IHfuel _ FUEL_GT).
        unfold "let* _ := _ in _" in *.
        remember (
          fun '(ci, ti) (acc: list (Benum.pattern * statement)) =>
            do si <- norm_statement fuel (StSetTailcomp i ti);
            eret ((ci, si) :: acc)
        ) as f.
        remember (
          fun '(ci, ti) (acc : list (Benum.pattern * statement)) =>
            do si <- norm_statement fuel' (StSetTailcomp i ti);
            eret ((ci, si) :: acc)
        ) as g.
        apply list_fold_right_err_ext_OK with (f := f) (g := g) in EQ.
        rewrite EQ; simpl. reflexivity.
        subst; intros. destruct b0.
        destruct (norm_statement fuel (StSetTailcomp i t)) eqn:Hnorm; try discriminate.
        simpl in H. inv H. rewrite IHfuel with (s1 := s); auto.
      + monadInv H. inv EQ0. simpl. 
        rewrite IHfuel with (s1 := x); auto.
  Qed.

  Variable arch : Target.archi.
  Variable tabs : Maps.PMap.t Type.

  Import OptionMonad.

  Lemma norm_statement_set_fw:
    forall te ge fuel
    (NORM_STATEMENT_CORRECT:
      forall sb s1 le le',
        norm_statement fuel sb = OK s1 ->
        ImpBNF.eval_statement arch tabs te ge le sb = Some le' ->
        Imp1Pure.eval_statement_rec arch tabs te ge le None s1 = Some le')
    i tc s1 le le' ty v,
      norm_statement fuel (StSetTailcomp i tc) = OK s1 ->
      ImpBNF.eval_tailcomp_rec arch tabs te ge le ty tc = Some (v, le') ->
      Imp1Pure.eval_statement_rec arch tabs te ge le None s1 =
      Some (Denot.lenv_update tabs le' i (Denot.Val tabs ty v)).
  Proof.
    induction fuel; intros.
    - simpl in H. discriminate.
    - simpl in H. destruct tc.
      + Res.monadInv H. inv EQ2.
        simpl in H0. monadInv H0. simpl.
        erewrite NORM_STATEMENT_CORRECT; eauto.
        simpl. eapply IHfuel; eauto.
        intros. eapply NORM_STATEMENT_CORRECT; eauto.
        eapply norm_statement_fuel_gt; eauto.
        eapply norm_statement_fuel_gt; eauto.
      + inv H. simpl in H0. monadInv H0. inv EQ2.
        simpl. rewrite EQ; simpl. erase_cast EQ1.
        setoid_rewrite EQ1; simpl. reflexivity.
      + Res.monadInv H. inv EQ2. simpl in H0. monadInv H0.
        simpl. setoid_rewrite EQ0; simpl.
        destruct x1.
        * eapply IHfuel with (tc := tc1) (s1 := x); eauto; intros.
          eapply NORM_STATEMENT_CORRECT; eauto.
          eapply norm_statement_fuel_gt; eauto.
        * eapply IHfuel with (tc := tc2) (s1 := x0); eauto; intros.
          eapply NORM_STATEMENT_CORRECT; eauto.
          eapply norm_statement_fuel_gt; eauto.
      + Res.monadInv H. inv EQ0. simpl in H0. monadInv H0.
        simpl. setoid_rewrite EQ0; simpl. setoid_rewrite EQ2; simpl.
        rename x0 into ta. rename x1 into va.
        rename l into cases. rename x into cases'.
        destruct ta; try discriminate. simpl in va.
        simpl in EQ3. simpl.
        revert b le le' ty v cases' EQ EQ0 va EQ2 EQ3.
        {
          induction cases; intros.
          - simpl in EQ. inv EQ. simpl in EQ3. discriminate.
          - simpl in EQ. Res.monadInv EQ. destruct a0. Res.monadInv EQ4.
            inv EQ5. simpl. simpl in EQ3. destruct p.
            + monadInv EQ3. rewrite EQ4; simpl.
              destruct (Benum.enum_eq x1 va).
              eapply IHfuel; eauto; intros;
              eapply NORM_STATEMENT_CORRECT; eauto;
              eapply norm_statement_fuel_gt; eauto.
              apply IHcases; auto.
            + eapply IHfuel; eauto; intros;
              eapply NORM_STATEMENT_CORRECT; eauto;
              eapply norm_statement_fuel_gt; eauto.
        }
        + Res.monadInv H. inv EQ0. simpl in H0.
          simpl. eapply IHfuel; eauto; intros;
          eapply NORM_STATEMENT_CORRECT; eauto;
          eapply norm_statement_fuel_gt; eauto.
  Qed.

  Lemma norm_statement_set_bw:
    forall te ge fuel
    (NORM_STATEMENT_CORRECT_BW:
      forall sb s1 le le'
        (WF_STMT: wf_statement te sb = true),
        norm_statement fuel sb = OK s1 ->
        Imp1Pure.eval_statement_rec arch tabs te ge le None s1 = Some le' ->
        ImpBNF.eval_statement arch tabs te ge le sb = Some le')
      i tc s1 le le' ty
      (TYPOF_TAIL: typof_tailcomp te tc = Some ty)
      (WF_TAIL: wf_tailcomp te tc = true),
      norm_statement fuel (StSetTailcomp i tc) = OK s1 ->
      Imp1Pure.eval_statement_rec arch tabs te ge le None s1 = Some le' ->
      (exists v le1,
        ImpBNF.eval_tailcomp_rec arch tabs te ge le ty tc = Some (v, le1) /\
        (lenv_update tabs le1 i (Val tabs ty v) = le')).
  Proof.
    induction fuel; intros.
    - simpl in H. discriminate.
    - simpl in H. destruct tc;
      simpl in WF_TAIL; destruct_conj WF_TAIL.
      + Res.monadInv H. inv EQ2.
        simpl in H0. monadInv H0. simpl.
        erewrite NORM_STATEMENT_CORRECT_BW; eauto.
        eapply IHfuel; eauto. intros.
        eapply NORM_STATEMENT_CORRECT_BW; eauto.
        eapply norm_statement_fuel_gt; eauto.
        unfold typof_tailcomp in *. simpl in TYPOF_TAIL.
        rewrite btyp_eqb_eq in C3. rewrite C3. exact TYPOF_TAIL.
        eapply norm_statement_fuel_gt; eauto.
      + inv H. simpl in H0. monadInv H0. inv EQ2. simpl.
        rewrite EQ; simpl. unfold typof_tailcomp in TYPOF_TAIL.
        simpl in TYPOF_TAIL. unfold Typing.typof_comp in EQ.
        rewrite TYPOF_TAIL in EQ. inv EQ.
        rewrite ecast_typ_id. setoid_rewrite EQ1; simpl.
        exists x0, le. split; reflexivity.
      + Res.monadInv H. inv EQ2. simpl in H0. monadInv H0.
        simpl. setoid_rewrite EQ0; simpl.
        rewrite btyp_eqb_eq in C4, C3.
        destruct x1.
        * eapply IHfuel; eauto. intros.
          eapply NORM_STATEMENT_CORRECT_BW; eauto.
          eapply norm_statement_fuel_gt; eauto.
          unfold typof_tailcomp in *; simpl in TYPOF_TAIL.
          rewrite C4. exact TYPOF_TAIL.
        * eapply IHfuel; eauto. intros.
          eapply NORM_STATEMENT_CORRECT_BW; eauto.
          eapply norm_statement_fuel_gt; eauto.
          unfold typof_tailcomp in *; simpl in TYPOF_TAIL.
          rewrite C3. exact TYPOF_TAIL.       
      + Res.monadInv H. inv EQ0. simpl in H0. monadInv H0.
        simpl. setoid_rewrite EQ0; simpl. setoid_rewrite EQ2; simpl.
        rename x0 into ta. rename x1 into va.
        rename l into cases. rename x into cases'.
        destruct ta; try discriminate. simpl in va.
        simpl in EQ3.
        revert b le le' ty TYPOF_TAIL C1 C2 C0 cases' EQ i0 l va EQ0 EQ2 EQ3.
        {
          induction cases; intros.
          - simpl in EQ. inv EQ. simpl in EQ3. discriminate.
          - simpl in EQ. Res.monadInv EQ. destruct a0. Res.monadInv EQ4.
            inv EQ5. simpl. simpl in EQ3. destruct p.
            + monadInv EQ3. rewrite EQ4; simpl.
              destruct (Benum.enum_eq x1 va).
              eapply IHfuel; eauto; intros.
              eapply NORM_STATEMENT_CORRECT_BW; eauto.
              eapply norm_statement_fuel_gt; eauto.
              simpl in C2. destruct_conj C2.
              rewrite btyp_eqb_eq in C.
              unfold typof_tailcomp in *. simpl in TYPOF_TAIL.
              rewrite C. exact TYPOF_TAIL.
              simpl in C0. destruct_conj C0. exact C.
              eapply IHcases; eauto.
              simpl. simpl in C2. destruct_conj C2. exact C3.
              simpl in C0. destruct_conj C0. exact C3.
            + eapply IHfuel; eauto; intros.
              eapply NORM_STATEMENT_CORRECT_BW; eauto.
              eapply norm_statement_fuel_gt; eauto.
              unfold typof_tailcomp in *. simpl in TYPOF_TAIL.
              simpl in C2. destruct_conj C2.
              rewrite btyp_eqb_eq in C. rewrite C.
              exact TYPOF_TAIL.
              simpl in C0. destruct_conj C0. exact C.
        }
        + Res.monadInv H. inv EQ0. simpl in H0.
          simpl. eapply IHfuel; eauto; intros;
          eapply NORM_STATEMENT_CORRECT_BW; eauto;
          eapply norm_statement_fuel_gt; eauto.
  Qed.

  Section NORM_TAILCOMP.

  Local Notation norm_tailcomp_correct_fw_def tc :=
    (forall s te ge le le' ty (v: eval_typ tabs ty),
      norm_tailcomp tc = OK s ->
      ImpBNF.eval_tailcomp_rec arch tabs te ge le ty tc = Some (v, le') ->
      Imp1Pure.eval_statement_rec arch tabs te ge le (Some ty) s = Some v).

  Local Notation norm_statement_correct_fw_def sb :=
    (forall fuel s1 te ge le le',
      norm_statement fuel sb = OK s1 ->
      ImpBNF.eval_statement arch tabs te ge le sb = Some le' ->
      Imp1Pure.eval_statement_rec arch tabs te ge le None s1 = Some le').

  Lemma norm_tailcomp_correct_mut:
    (forall tc, norm_tailcomp_correct_fw_def tc) /\
    (forall sb, norm_statement_correct_fw_def sb).
  Proof.
    apply tailcomp_depth_ind_mut with
      (P := fun tc => norm_tailcomp_correct_fw_def tc)
      (P0 := fun sb => norm_statement_correct_fw_def sb);
    intros.
    - simpl in H1. Res.monadInv H1. inv EQ2.
      simpl in H2. monadInv H2. simpl.
      erewrite H; eauto.
    - simpl in H0. monadInv H0. inv EQ2.
      destruct c eqn:Ec; simpl in EQ.
      1: { inv H. erase_cast EQ1.
           simpl; simpl in EQ1. simpl in EQ.
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
    - simpl in H1. Res.monadInv H1. inv EQ2.
      simpl in H2. monadInv H2. simpl.
      setoid_rewrite EQ0; simpl.
      destruct x1.
      + eapply H; eauto.
      + eapply H0; eauto.
    - simpl in H0. Res.monadInv H0. inv EQ0.
      simpl in H1. monadInv H1. simpl.
      rename x into cases'.
      rename x0 into ta.
      rename x1 into va.
      setoid_rewrite EQ0; simpl. setoid_rewrite EQ2; simpl.
      destruct ta; try discriminate.
      unfold ImpBNF.eval_match in EQ3. simpl in EQ3.
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
    - simpl in H0. Res.monadInv H0. inv EQ0.
      simpl in H1. simpl. eapply H; eauto.
    - remember (StSetTailcomp i tc) as s. 
      clear - H0 H1. 
      revert s s1 le le' H0 H1.
      induction fuel; intros.
      + simpl in H0. discriminate.
      + simpl in H0. destruct s. destruct t.
        * Res.monadInv H0. inv EQ2.
          simpl in H1. monadInv H1.
          monadInv EQ3.
          simpl. inv EQ4.
          erewrite IHfuel; eauto; simpl.
          eapply norm_statement_set_fw; eauto.
        * inv H0. simpl in H1. monadInv H1.
          monadInv EQ1. simpl. inv EQ4.
          rewrite EQ0; simpl. inv EQ2. simpl.
          erase_cast EQ1. setoid_rewrite EQ1; simpl.
          reflexivity.
        * Res.monadInv H0. inv EQ2. simpl in H1. monadInv H1.
          monadInv EQ3. inv EQ4. simpl.
          setoid_rewrite EQ2; simpl. destruct x4;
          eapply norm_statement_set_fw; eauto.
        * Res.monadInv H0. inv EQ0. simpl in H1.
          monadInv H1. monadInv EQ2.
          inv EQ3. simpl. setoid_rewrite EQ1; simpl.
          setoid_rewrite EQ2; simpl. rename l into cases.
          rename x into cases'. rename x0 into tb.
          rename x3 into ta. rename x4 into va.
          unfold typof_tailcomp in EQ0.
          rename x1 into v. rename x2 into le'.
          destruct ta; try discriminate. simpl in EQ5. simpl.
          revert cases cases' EQ EQ0 EQ5.
          {
            induction cases; simpl; intros.
            - discriminate.
            - Res.monadInv EQ. destruct a0. simpl in EQ5.
              Res.monadInv EQ4. inv EQ6. simpl.
              destruct p.
              + monadInv EQ5. rewrite EQ4; simpl.
                 destruct (Benum.enum_eq x1 va).
                 eapply norm_statement_set_fw; eauto.
                 eapply IHcases; eauto.
              + eapply norm_statement_set_fw; eauto.
          }
        * Res.monadInv H0. inv EQ0. simpl in H1.
          monadInv H1. inv EQ3.
          simpl. eapply norm_statement_set_fw; eauto.
  Qed.

  Theorem norm_tailcomp_correct_fw:
    forall tc, norm_tailcomp_correct_fw_def tc.
  Proof.
    pose proof norm_tailcomp_correct_mut.
    destruct H. exact H.
  Qed.

  Theorem norm_statement_fw_correct:
    forall sb, norm_statement_correct_fw_def sb.
  Proof.
    pose proof norm_tailcomp_correct_mut.
    destruct H. exact H0.
  Qed.

  Local Notation norm_tailcomp_correct_bw_def tc :=
    (forall s te ge le ty (v: eval_typ tabs ty)
    (WF_TAIL: wf_tailcomp te tc = true),
      norm_tailcomp tc = OK s ->
      Imp1Pure.eval_statement_rec arch tabs te ge le (Some ty) s = Some v ->
      (exists le', ImpBNF.eval_tailcomp_rec arch tabs te ge le ty tc = Some (v, le'))).

  Local Notation norm_statement_correct_bw_def sb :=
    (forall fuel s1 te ge le le'
    (WF_STMT: wf_statement te sb = true),
      norm_statement fuel sb = OK s1 ->
      Imp1Pure.eval_statement_rec arch tabs te ge le None s1 = Some le' ->
      ImpBNF.eval_statement arch tabs te ge le sb = Some le').

  Theorem norm_tailcomp_bw_correct:
    forall tc, norm_tailcomp_correct_bw_def tc.
  Proof.
    induction tc using tailcomp_depth_ind with
      (P0 := fun sb => norm_statement_correct_bw_def sb);
    intros.
    - simpl in H. Res.monadInv H. inv EQ2. simpl in H0.
      monadInv H0. simpl. simpl in WF_TAIL.
      destruct_conj WF_TAIL. erewrite IHtc; eauto.
    - simpl in H. destruct c eqn:Ec.
      1: inv H. simpl in H0. simpl. monadInv H0.
        erase_cast EQ0. unfold Typing.typof_comp. simpl.
        unfold Typing.typof_atom in EQ.
        rewrite EQ; simpl. rewrite ecast_typ_id.
        rewrite EQ0; simpl. exists le. reflexivity.
      all: ltac:(rewrite <- Ec in *;
        inversion H; clear H; rewrite <- H2 in H0;
        simpl in H0; monadInv H0; monadInv EQ;
        inversion EQ4; simpl; rewrite EQ0; simpl;
        clear EQ4; erase_cast EQ2;
        assert (x1 = ty) by (simpl in EQ0; unfold Typing.typof_atom in EQ1;
        simpl in EQ1; unfold Typing.typof_comp in EQ0; simpl in EQ0;
        congruence); subst;
        rewrite ecast_typ_id; rewrite EQ; exists le;
        simpl; unfold eval_var in EQ2; unfold lenv_get, lenv_update in EQ2;
        rewrite STree.gss in EQ2; simpl in EQ2; erase_cast EQ2;
        inv EQ2; reflexivity).
    - simpl in H. Res.monadInv H. inv EQ2. simpl in H0.
      monadInv H0. simpl. rewrite EQ0; simpl.
      simpl in WF_TAIL. destruct_conj WF_TAIL. 
      destruct x1. eapply IHtc1; eauto. eapply IHtc2; eauto.
    - simpl in H0. Res.monadInv H0. inv EQ0.
      simpl in H1. monadInv H1. simpl.
      setoid_rewrite EQ0; simpl. setoid_rewrite EQ2; simpl.
      simpl in WF_TAIL. destruct_conj WF_TAIL.
      destruct x0; try discriminate. simpl in EQ3; simpl.
      rename x into cases'. rename x1 into va. simpl in va.
      clear - C0 H EQ EQ3 cases.
      {
        revert cases' l va EQ3 EQ.
        induction cases; simpl; intros.
        - inv EQ. simpl in EQ3. discriminate.
        - Res.monadInv EQ. destruct a. Res.monadInv EQ0.
          inv EQ2. simpl. simpl in EQ3.
          simpl in C0. destruct_conj C0.
          destruct p.
          + monadInv EQ3. rewrite EQ0; simpl.
            destruct (Benum.enum_eq x va).
            * eapply H; eauto. apply List.in_eq.
            * simpl in H. eapply IHcases; eauto.
          + eapply H; eauto. apply List.in_eq.
      }
    - simpl in H. Res.monadInv H. inv EQ0. simpl in H0.
      simpl. eapply IHtc; eauto.
    - clear - WF_STMT H H0.
      revert s1 le le' i tc H H0 WF_STMT.
      {
        induction fuel; intros.
        - simpl in H. discriminate.
        - simpl in H. destruct tc; simpl.
          + Res.monadInv H. inv EQ2. simpl in H0. monadInv H0.
            unfold typ_of_statement in x1, le'.
            unfold typof_tailcomp; simpl.
            rename x into s'. rename x0 into si.
            rename x1 into le1.
            simpl in WF_STMT. destruct_conj WF_STMT.
            rewrite convertible_btyp_iff in C. destruct C.
            rewrite H; simpl.
            destruct s. erewrite IHfuel; eauto; simpl.
            eapply norm_statement_set_bw with (ty := x) in EQ2; eauto.
            destruct EQ2. destruct H0. destruct H0.
            rewrite H0; simpl. rewrite H1. reflexivity.
            intros. destruct sb. eapply IHfuel; eauto.
            rewrite btyp_eqb_eq in C3.
            unfold typof_tailcomp. rewrite C3.
            exact H.
          + inv H. simpl in H0. monadInv H0. inv EQ2.
            unfold typof_tailcomp. simpl.
            unfold Typing.typof_comp in *. rewrite EQ; simpl.
            rewrite ecast_typ_id. setoid_rewrite EQ1; simpl. reflexivity.
          + Res.monadInv H. inv EQ2. simpl in WF_STMT. destruct_conj WF_STMT.
            simpl in H0. monadInv H0. unfold typof_tailcomp.
            simpl. rewrite convertible_btyp_iff in C1. destruct C1.
            rewrite H. simpl.
            setoid_rewrite EQ0; simpl. destruct x1.
            * eapply norm_statement_set_bw with (ty := x2) in EQ; eauto.
              destruct EQ. destruct H0. destruct H0. rewrite H0; simpl.
              rewrite H1. reflexivity.
              intros. destruct sb. eapply IHfuel; eauto.
              rewrite btyp_eqb_eq in C4. unfold typof_tailcomp.
              rewrite C4. exact H. 
            * eapply norm_statement_set_bw with (ty := x2) in EQ1; eauto.
              destruct EQ1. destruct H0. destruct H0. rewrite H0; simpl.
              rewrite H1. reflexivity.
              intros. destruct sb. eapply IHfuel; eauto.
              rewrite btyp_eqb_eq in C3. unfold typof_tailcomp.
              rewrite C3. exact H. 
          + simpl in WF_STMT. destruct_conj WF_STMT.
            Res.monadInv H. inv EQ0. simpl in H0. monadInv H0.
            rewrite convertible_btyp_iff in C1.
            unfold typof_tailcomp; simpl. destruct C1.
            rewrite H; simpl.
            setoid_rewrite EQ0; simpl. setoid_rewrite EQ2; simpl.
            destruct x0; try discriminate.
            simpl; simpl in EQ3. rename l into cases.
            rename x into cases'.
            revert b cases' x2 H C2 C0 EQ i0 l0 EQ0 x1 EQ2 EQ3.
            {
              induction cases; intros.
              - simpl in EQ. inv EQ. simpl in EQ3. discriminate.
              - simpl in EQ. Res.monadInv EQ. destruct a0. Res.monadInv EQ4.
                inv EQ5. simpl. simpl in EQ3.
                simpl in C2. destruct_conj C2.
                simpl in C0. destruct_conj C0.
                destruct p.
                + monadInv EQ3. rewrite EQ4; simpl.
                  destruct (Benum.enum_eq x3 x1).
                  * eapply norm_statement_set_bw with (ty := x2) in EQ; eauto.
                    destruct EQ. destruct H0. destruct H0.
                    rewrite H0; simpl. rewrite H1; reflexivity.
                    intros. destruct sb. eapply IHfuel; eauto.
                    rewrite btyp_eqb_eq in C. unfold typof_tailcomp.
                    rewrite C. exact H.
                  * eapply IHcases; eauto.
                + eapply norm_statement_set_bw with (ty := x2) in EQ; eauto.
                  destruct EQ. destruct H0. destruct H0. rewrite H0; simpl.
                  rewrite H1; reflexivity.
                  intros. destruct sb. eapply IHfuel; eauto.
                  rewrite btyp_eqb_eq in C. unfold typof_tailcomp.
                  rewrite C. exact H.
            }
          + Res.monadInv H. inv EQ0. simpl in H0.
            simpl in WF_STMT. unfold typof_tailcomp.
            simpl. pose proof (wf_tailcomp_btyp_to_typ _ _ WF_STMT).
            destruct H. rewrite H; simpl.
            eapply norm_statement_set_bw with (ty := x0) in EQ; eauto.
              destruct EQ. destruct H1. destruct H1.
              rewrite H1; simpl. rewrite H2; reflexivity.
              intros. destruct sb. eapply IHfuel; eauto.
      }
  Qed.

  End NORM_TAILCOMP.

  Theorem norm_tailcomp_correct:
    forall te ge le tc s ty,
      wf_tailcomp te tc = true ->
      norm_tailcomp tc = OK s ->
      Imp1Pure.eval_statement arch tabs te ge le ty s =
      ImpBNF.eval_tailcomp arch tabs te ge le ty tc.
  Proof.
    unfold ImpBNF.eval_tailcomp, Imp1Pure.eval_statement; intros.
    destruct (eval_tailcomp_rec arch tabs te ge le ty tc) as [[v le']|] eqn:Eeval_tc;
    simpl.
    - erewrite norm_tailcomp_correct_fw; eauto.
    - destruct (eval_statement_rec arch tabs te ge le (Some ty) s) eqn:Eeval_s; simpl.
      + eapply norm_tailcomp_bw_correct in Eeval_s; eauto.
        destruct Eeval_s. rewrite H1 in Eeval_tc. discriminate.
      + reflexivity.
  Qed.

  Lemma norm_function_correct_aux:
    forall params tc s te ge le tret,
      wf_tailcomp te tc = true ->
      norm_tailcomp tc = OK s ->
      eval_fun_rec tabs (Imp1Pure.eval_statement arch tabs) te ge le params tret s =
      eval_fun_rec tabs (ImpBNF.eval_tailcomp arch tabs) te ge le params tret tc.
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
    eval_def_fun tabs (Imp1Pure.eval_statement arch tabs) te ge x f' =
    eval_def_fun tabs (ImpBNF.eval_tailcomp arch tabs) te ge x f.
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
      eval_globdef tabs (Imp1Pure.eval_statement arch tabs) te impl ge d' =
      eval_globdef tabs (ImpBNF.eval_tailcomp arch tabs) te impl ge d.
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
      OptionMonad.fold_left_err
        (fun acc d =>
          eval_globdef tabs  (eval_statement arch tabs) te impl acc d) defs' a0 =
      OptionMonad.fold_left_err
        (fun acc d =>
          eval_globdef tabs  (eval_tailcomp arch tabs) te impl acc d) defs a0.
  Proof.
    induction defs; intros.
    - simpl in H. inv H. simpl. reflexivity.
    - simpl in H. Res.monadInv H. simpl.
      erewrite norm_globdef_correct; eauto.
      destruct
        (eval_globdef tabs (eval_tailcomp arch tabs) te impl a0 a);
        try reflexivity.
      simpl; auto.
  Qed.

  Theorem norm_program_correct:
    forall impl p p',
      norm_program p = OK p' ->
      Imp1Pure.eval_prog arch tabs impl p' =
      ImpBNF.eval_prog arch tabs impl p.
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
