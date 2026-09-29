From Stdlib Require Import Bool List String Lia Eqdep RelationClasses.
From BarocqComp Require Import Res Utils Brecord Types Syntax ImpBNF Imp1 Maps2 Denot BarocqBNF Imp1Pure.
Import ListNotations.

Local Open Scope error_monad_scope.
Close Scope Z_scope.
Open Scope string_scope.

Section NormInit.
  Variable norm_tailcomp : option ident -> ImpBNF.tailcomp -> res Imp1.statement.

  Fixpoint norm_list (l : list (ident * ImpBNF.tailcomp)) : res Imp1.statement :=
    match l with
    | nil => OK StSkip
    | (x,tc) :: l => do s1 <- norm_tailcomp (Some x) tc ;
                     do s2 <- norm_list l;
                     OK (StSequence s1 s2)
    end.
End NormInit.

(*Section Norm.
  Variable norm_tailcomp : forall (t: ImpBNF.tailcomp), res Imp1.statement.

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
    | ImpBNF.TcWhile init cond variant body tc _ =>
      if MapList.nodup string_dec init
      then
        do init' <- norm_list norm_begin init;
        do body' <- norm_tailcomp body;
        do tc    <- norm_begin x tc;
        eret (StSequence (StSequence init' (StWhile cond variant body')) tc)
      else efail
    | ImpBNF.TcSwitch a cases _ =>
      do cases' <- MapList.map_err
                     (fun ti => norm_begin x ti)
                     cases;
      eret (StSwitch a cases')
    | ImpBNF.TcComp c => eret (StSet x c)
    | ImpBNF.TcActRecord _ _ => Error (msg "The program is not well-typed")
    | ImpBNF.TcAttr a t1 =>
      do s1 <- norm_begin x t1;
      eret (StAttr a s1)
  end.
End Norm.
 *)

Definition comp_is_atom (c:comp) :=
  match c with
  | CpAtom a => Some a
  | _        => None
  end.

(*Fixpoint norm_tailcomp (t: ImpBNF.tailcomp) : res Imp1.statement :=
  match t with
  | ImpBNF.TcBegin x t1 t2 _ =>
      do s1 <- norm_begin norm_tailcomp x t1;
      do s2 <- norm_tailcomp t2;
      eret (StSequence s1 s2)
  | ImpBNF.TcIfThenElse a t1 t2 _ =>
      do t1' <- norm_tailcomp t1;
      do t2' <- norm_tailcomp t2;
      eret (StIfThenElse a t1' t2')
  | ImpBNF.TcWhile init cond variant body tc _ =>
      if MapList.nodup string_dec init
      then
      do init' <- norm_list (norm_begin norm_tailcomp) init;
      do body' <- norm_tailcomp body;
      do tc'   <- norm_tailcomp tc;
      eret (StSequence (StSequence init' (StWhile cond variant body')) tc')
      else efail
  | ImpBNF.TcSwitch a cases _ =>
      do cases' <- MapList.map_err norm_tailcomp cases;
      eret (StSwitch a cases')
  | ImpBNF.TcComp c => (* Could StReturn take a computation ? *)
      match comp_is_atom c with
      | Some a   => eret (StReturn a)
      | None => eret (StSequence (StSet "res" c) (StReturn (AVar "res" (btypof_comp c))))
      end
  | ImpBNF.TcActRecord l _ =>
      eret (List.fold_right (fun '(x,a) p => StSequence (StSet x (CpAtom a)) p) StSkip l)
  | ImpBNF.TcAttr a c =>
      do t1 <- norm_tailcomp c;
      eret (StAttr a t1)
  end.
*)


Fixpoint norm_tailcomp (oid: option ident) (t: ImpBNF.tailcomp) : res Imp1.statement :=
  match t with
  | ImpBNF.TcBegin x t1 t2 _ =>
      do s1 <- norm_tailcomp (Some x) t1;
      do s2 <- norm_tailcomp oid t2;
      eret (StSequence s1 s2)
  | ImpBNF.TcIfThenElse a t1 t2 _ =>
      do t1' <- norm_tailcomp oid t1;
      do t2' <- norm_tailcomp oid t2;
      eret (StIfThenElse a t1' t2')
  | ImpBNF.TcWhile init cond variant body tc _ =>
      if MapList.nodup string_dec init
      then
      do init' <- norm_list norm_tailcomp init;
      do body' <- norm_tailcomp None body;
      do tc'   <- norm_tailcomp oid tc;
      eret (StSequence (StSequence init' (StWhile cond variant body')) tc')
      else efail
  | ImpBNF.TcSwitch a cases _ =>
      do cases' <- MapList.map_err (norm_tailcomp oid) cases;
      eret (StSwitch a cases')
  | ImpBNF.TcComp c => (* Could StReturn take a computation ? *)
      match oid with
      | Some x => eret (StSet x c)
      | None   =>
          match comp_is_atom c with
          | Some a   => eret (StReturn a)
          | None => eret (StSequence (StSet "res" c) (StReturn (AVar "res" (btypof_comp c))))
          end
      end
  | ImpBNF.TcActRecord l _ =>
      match oid with
      | Some x => Error (MSG "Cannot bind variable " :: MSG x :: MSG " to activation record " :: nil)
      | None   =>
          eret (List.fold_right (fun '(x,a) p => StSequence (StSet x (CpAtom a)) p) StSkip l)
      end
  | ImpBNF.TcAttr a c =>
      do t1 <- norm_tailcomp oid c;
      eret (StAttr a t1)
  end.




Definition norm_function (te: Typing.tenv) (f: ImpBNF.function) : res Imp1.function :=
  if wf_tailcomp te (fn_body f) && btyp_eqb (btypof_tailcomp (fn_body f)) (fn_return f)
     && negb (btyp_is_actr (fn_return f))
  then
    do body <- norm_tailcomp None (fn_body f);
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

  Lemma update_lenv_more_keys_aux : forall te ge init
      (RC:
    forall (i : ident) (v : tailcomp),
    In (i, v) init ->
    forall (ty : typ) (le : lenv tabs) (v0 : eval_typ tabs ty)
      (le' : lenv tabs),
    eval_tailcomp_rec tabs te ge le ty v = Some (v0, le') ->
    forall x : StringIndexed.t,
    SSet.mem x (STree.keys le) = true ->
    SSet.mem x (STree.keys le') = true)
      (le : lenv tabs)
      (le1 : lenv tabs)
      (UP :
         update_lenv tabs (eval_tailcomp_rec tabs te ge) te init le =
         Some le1),
      forall x, SSet.mem x (STree.keys le) = true -> SSet.mem x (STree.keys le1) = true.
  Proof.
    induction init.
    - simpl. intros. congruence.
    - simpl; intros.
      destruct a.
      monadInv UP.
      eapply RC in EQ1; eauto.
      apply IHinit with (x:=x) in EQ2; auto.
      { intros.
        eapply RC  ;eauto.
      }
      rewrite keys_lenv_update.
      rewrite SSet.mem_add.
      destruct (string_dec x i); auto.
  Qed.


  Lemma eval_tailcomp_rec_more_keys : forall te ge tc ty le v le',
      eval_tailcomp_rec tabs te ge le ty tc = Some (v, le') ->
      forall x, SSet.mem x (STree.keys le) = true ->
                SSet.mem x (STree.keys le') = true.
  Proof.
    induction tc using tailcomp_depth_ind.
    - simpl.
      intros. monadInv H.
      apply IHtc1 with (x:=x0) in EQ1.
      eapply IHtc2; eauto.
      rewrite keys_lenv_update.
      rewrite SSet.mem_add.
      destruct (string_dec x0 x); auto.
      auto.
    - simpl;intros.
      monadInv H0.
      rename x0 into le1, x4 into tinit, x6 into lew.
      assert (INIT : SSet.mem x (STree.keys le1) = true).
      {
        clear - H H1 EQ.
        eapply update_lenv_more_keys_aux; eauto.
      }
      assert (WHILE : SSet.mem x (STree.keys lew) = true).
      { revert INIT.
        revert EQ5. revert IHtc1.
        clear.
        revert le1 lew.
        induction x3 ; simpl.
        - intros.
          monadInv EQ5.
          destruct x0 ; monadInv EQ0.
          congruence.
        - intros.
          monadInv EQ5.
          destruct x0.
          + monadInv EQ0.
            monadInv EQ1.
            eapply IHtc1 in EQ0; eauto.
            eapply IHx3; eauto.
            rewrite keys_lenv_of_record.
            rewrite EQ0. reflexivity.
          + congruence.
      }
      eapply IHtc2;eauto.
    - simpl.
      intros.
      monadInv H. inv EQ2;auto.
    - simpl. destruct ty0; try discriminate.
      destruct o; try discriminate.
      intros. monadInv H.
      destruct (typ_eqb (TRecord None l) x0); try discriminate.
      monadInv EQ0.
      auto.
    - intros.
      simpl in H.
      monadInv H.
      destruct x0; eauto.
    - simpl.
      intros.
      monadInv H0.
      unfold Denot.eval_match in EQ2.
      destruct x0; try discriminate.
      revert EQ2 H1.
      induction cases; auto.
      + simpl. discriminate.
      + simpl.
        destruct a0.
        simpl. destruct p.
        * intros. monadInv EQ2.
          destruct (Benum.enum_eq x0 x1).
          eapply H;eauto.
          simpl. left;reflexivity.
          eapply IHcases;eauto.
          intros.
          eapply H; eauto.
          right;eauto.
        * intros. eapply H;eauto.
          simpl. left;reflexivity.
    - simpl.
      intros;eapply IHtc;eauto.
  Qed.


  Lemma update_lenv_more_keys :
    forall te ge init le leinit'
           (UP: update_lenv tabs (eval_tailcomp_rec tabs te ge) te init le =
                  Some leinit'),
           forall x, SSet.mem x (STree.keys le) = true ->
                     SSet.mem x (STree.keys leinit') = true.
  Proof.
    intros.
    eapply update_lenv_more_keys_aux; eauto.
    intros.
    eapply eval_tailcomp_rec_more_keys; eauto.
  Qed.


  Lemma update_lenv_mem :
    forall te ge init le leinit' tinit
           (UP: update_lenv tabs (eval_tailcomp_rec tabs te ge) te init le =
                  Some leinit')
           (SAME : MapList.mmap typ (typof_tailcomp te) init = Some tinit),
    forall (x0 : StringIndexed.t) (v0 : typ),
      In (x0, v0) tinit -> SSet.mem x0 (STree.keys leinit') = true.
  Proof.
    induction init.
    - simpl. intros. inv SAME. simpl in H. tauto.
    - simpl.
      intros. destruct a.
      monadInv UP.
      monadInv SAME.
      monadInv EQ0.
      simpl in H.
      destruct H.
      + inv H.
        eapply update_lenv_more_keys; eauto.
        rewrite keys_lenv_update.
        rewrite SSet.mem_add. destruct (string_dec x0 x0); congruence.
      + eapply IHinit;eauto.
  Qed.

  Lemma match_on_update_l : forall P ge1 le1 id v ge2 le2,
      match_on tabs P ge1 (lenv_update tabs le1 id v) ge2 le2 ->
      match_on tabs (BSet.diff P (singleton id)) ge1  le1 ge2 le2.
  Proof.
    unfold match_on.
    intros.
    unfold BSet.diff in H0. rewrite andb_true_iff in H0.
    destruct H0.
    specialize (H _ H0).
    unfold get_env,lenv_update in *.
    rewrite STree.gsspec in H.
    unfold singleton in H1.
    rewrite negb_true_iff in H1.
    unfold BSet.singleton in H1.
    destruct (string_dec x id); try discriminate.
    destruct (STree.elt_eq x id); try congruence.
  Qed.

  Definition updated_by_binding (x_tc: ident * tailcomp) :=
    BSet.union (BSet.singleton string_dec (fst x_tc)) (SSet.bset (updated_vars (snd x_tc))).


  Lemma update_lenv_not_updated_aux :
    forall te ge init le le'
      (REC :
    forall (i : ident) (v : tailcomp),
    In (i, v) init ->
    forall (ty : typ) (le : lenv tabs) (v0 : eval_typ tabs ty)
      (le' : lenv tabs),
    eval_tailcomp_rec tabs te ge le ty v = Some (v0, le') ->
    match_on tabs (BSet.compl (SSet.bset (updated_vars v))) ge le ge le')
    (UP : update_lenv tabs (eval_tailcomp_rec tabs te ge) te init le = Some le'),
  match_on tabs
    (BSet.compl
       (BSet.union_list updated_by_binding init))
    ge le ge le'.
  Proof.
    induction init ; simpl.
    - intros. inv UP.
      apply match_on_refl.
    - intros.
      destruct a as (x,tc).
      monadInv UP.
      eapply REC in EQ1.
      eapply IHinit in EQ2.
      apply match_on_update_l in EQ2.
      eapply match_on_le.
      eapply match_on_trans;eauto.
      { unfold updated_by_binding at 1.
        unfold fst,snd.
        BSet.sset.
      }
      intros.
      eapply REC. right. eauto.
      eauto.
      left; eauto.
  Qed.


  Lemma get_lenv_of_record : forall lty r x le1,
    (forall ty, ~ In (x,ty) lty) ->
      STree.get x (lenv_of_record tabs lty r le1) = STree.get x le1.
  Proof.
    induction lty ; simpl; auto.
    intros.
    destruct a as (id,ty).
    simpl.
    rewrite IHlty.
    unfold lenv_update. rewrite STree.gsspec.
    destruct (STree.elt_eq x id);auto. exfalso.
    apply (H ty). left ; congruence.
    repeat intro. apply (H ty0).
    tauto.
  Qed.

  Lemma get_env_lenv_of_record : forall ge le1 lty r x,
    (forall ty, ~ In (x,ty) lty) ->
      get_env tabs ge (lenv_of_record tabs lty r le1) x = get_env tabs ge le1 x.
  Proof.
    unfold get_env.
    intros.
    rewrite get_lenv_of_record; auto.
  Qed.


  
  Lemma match_on_lenv_of_record_l : forall P lty r ge1 le1 ge2 le2,
      match_on tabs P ge1 (lenv_of_record tabs lty r le1) ge2 le2 ->
      match_on tabs (BSet.diff P (bset_of_bindings lty)) ge1 le1 ge2 le2.
  Proof.
    unfold match_on.
    intros.
    unfold BSet.diff in H0. rewrite andb_true_iff in H0.
    rewrite negb_true_iff in H0.
    destruct H0.
    specialize (H  _ H0).
    rewrite get_env_lenv_of_record in H. auto.
    rewrite bset_of_bindings_eq in H1.
    unfold SSet.bset in H1.
    rewrite mem_sset_of_bindings in H1.
    repeat intro.
    apply MapList.in_mem with (key_eq:= string_dec) in H2.
    congruence.
  Qed.



  Lemma while_not_updated :
    forall te ge cond body  lty
      (REC :
    forall (ty : typ) (le : lenv tabs) (v0 : eval_typ tabs ty)
      (le' : lenv tabs),
      eval_tailcomp_rec tabs te ge le ty body = Some (v0, le') ->
      match_on tabs (BSet.compl (SSet.bset (updated_vars body))) ge le ge le')
      fuel le le',
      While.while (fun le : lenv tabs => eval_atom tabs te ge le TBool cond)
      (fun le : lenv tabs =>
         (let* (r, le'):= eval_tailcomp_rec tabs te ge le (TRecord None lty) body
          in Some (lenv_of_record tabs lty r le'))%option_monad)
      fuel le =
             Some le' ->
           match_on tabs
             (BSet.compl
                (BSet.union (SSet.bset (updated_vars body)) (bset_of_bindings lty)))
    ge le ge le'.
  Proof.
    induction fuel; intros.
    - simpl in H.
      destruct (eval_atom tabs te ge le TBool cond); try discriminate.
      simpl in H. destruct e; auto.
      destruct (eval_tailcomp_rec tabs te ge le (TRecord None lty) body); try discriminate.
      simpl in H. destruct p. discriminate.
      inv H. apply match_on_refl.
    - simpl in H.
      destruct (eval_atom tabs te ge le TBool cond); try discriminate.
      simpl in H.
      rewrite bind2_bind in H; unfold uncurry in H.
      destruct e.
      monadInv H.
      monadInv EQ.
      apply IHfuel in EQ0.
      destruct x0.
      apply REC in EQ1.
      simpl in EQ0.
      apply match_on_lenv_of_record_l in EQ0.
      eapply match_on_le.
      eapply match_on_trans;eauto.
      BSet.sset.
      inv H.
      apply match_on_refl.
  Qed.


  Lemma eval_tailcomp_rec_not_updated : forall te ge tc ty le v le',
      eval_tailcomp_rec tabs te ge le ty tc = Some (v, le') ->
      match_on tabs (BSet.compl (SSet.bset(updated_vars tc))) ge le ge le'.
  Proof.
    induction tc using tailcomp_depth_ind.
    - simpl.
      intros. monadInv H.
      apply IHtc1  in EQ1.
      eapply IHtc2 in EQ2.
      eapply match_on_le.
      apply match_on_update_l in EQ2.
      eapply match_on_trans; eauto.
      unfold BSet.subset,BSet.compl, BSet.inter, BSet.union.
      intros.
      rewrite SSet.bset_add in H.
      rewrite negb_true_iff in *.
      rewrite andb_true_iff.
      rewrite negb_true_iff.
      unfold BSet.union in H.
      rewrite SSet.bset_singleton in H.
      unfold BSet.diff.
      rewrite andb_true_iff.
      rewrite! negb_true_iff.
      unfold BSet.singleton in H.
      rewrite orb_false_iff in H.
      rewrite SSet.bset_union in H.
      unfold BSet.union in H.
      rewrite orb_false_iff in H.
      unfold singleton.
      unfold BSet.singleton.
      tauto.
    - intros.
      simpl in H0.
      monadInv H0.
      simpl.
      rename x into le1.
      rename x3 into lty.
      rename x2 into fuel.
      rename x5 into lew.
      apply while_not_updated  in EQ5.
      apply IHtc2 in  EQ7.
      eapply update_lenv_not_updated_aux in EQ; auto.
      eapply match_on_le.
      eapply match_on_trans;eauto.
      eapply match_on_trans;eauto.
      { BSet.sset.
        rewrite SSet.bset_union in H0.
        unfold BSet.union in H0.
        rewrite SSet.bset_union_list in H0.
        rewrite orb_false_iff in H0.
        rewrite SSet.bset_union in H0.
        unfold BSet.union in H0.
        rewrite orb_false_iff in H0.
        intuition idtac.
        rewrite <- H1.
        apply BSet.union_list_morph.
        intros. unfold updated_by_binding_aux.
        rewrite SSet.bset_union. unfold BSet.union.
        rewrite SSet.bset_singleton. unfold updated_by_binding.
        reflexivity.
        unfold bset_of_bindings.
        rewrite <- not_true_iff_false.
        rewrite <- not_true_iff_false in H1.
        intro. apply H1.
        assert (BSet.union_list (fun x : ident * tailcomp => singleton (fst x)) init x = true).
        {
          clear - EQ3 H2.
          revert lty H2 EQ3.
          induction init ; simpl.
          - intros. inv EQ3. simpl in H2. auto.
          - intros.
            monadInv EQ3. monadInv EQ.
            simpl in H2.
            unfold BSet.union in H2.
            rewrite orb_true_iff in H2.
            destruct H2.
            BSet.sset.
            apply IHinit in EQ1;auto.
            { BSet.sset. }
        }
        revert H4.
        apply BSet.subset_union_list_mono.
        intros. unfold updated_by_binding_aux.
        repeat intro. rewrite SSet.bset_union.
        unfold BSet.union. rewrite orb_true_iff. rewrite SSet.bset_singleton.
        tauto.
      }
      auto.
    - simpl;intros.
      monadInv H. inv EQ2.
      apply match_on_refl.
    - simpl. intros. destruct ty0; try discriminate.
      destruct o; try discriminate.
      monadInv H.
      destruct (typ_eqb (TRecord None l) x); try discriminate.
      monadInv EQ0. apply match_on_refl.
    - simpl. intros.
      monadInv H.
      destruct x.
      apply IHtc1 in EQ0.
      eapply match_on_le;eauto.
      BSet.sset.
      rewrite SSet.bset_union in H.
      unfold BSet.union in H. rewrite orb_false_iff in H. tauto.
      apply IHtc2 in EQ0.
      eapply match_on_le;eauto.
      BSet.sset.
      rewrite SSet.bset_union in H.
      unfold BSet.union in H. rewrite orb_false_iff in H. tauto.
    - simpl.
      intros.
      monadInv H0.
      unfold Denot.eval_match in EQ2.
      destruct x; try discriminate.
      apply Benum.ematch_with_inv_Some in EQ2.
      destruct EQ2 as (p & c & IN & M & EQM).
      subst.
      rewrite MapList.in_map_iff in IN.
      destruct IN as (ptc & PEQ & IN).
      inv PEQ.
      destruct ptc.
      simpl in H2.
      assert (IN':=IN).
      eapply H in IN; eauto.
      eapply match_on_le;eauto.
      apply BSet.subset_compl.
      eapply BSet.subset_morph2.
      intro.
      rewrite SSet.bset_union_list.
      reflexivity.
      eapply BSet.subset_trans.
      2: {
        eapply BSet.subset_union_list_in. eauto.
      }
      simpl. apply BSet.subset_refl.
    - simpl ; intros.
      eapply IHtc;eauto.
  Qed.


  Lemma update_lenv_not_updated :
    forall te ge init le le'
    (UP : update_lenv tabs (eval_tailcomp_rec tabs te ge) te init le = Some le'),
  match_on tabs
    (BSet.compl
       (BSet.union_list updated_by_binding init))
    ge le ge le'.
  Proof.
    intros.
    eapply update_lenv_not_updated_aux; eauto.
    intros.
    eapply eval_tailcomp_rec_not_updated; eauto.
  Qed.




  Lemma is_actr_Some : forall ty l,
      is_actr ty = Some l -> ty = TRecord None l.
  Proof.
    destruct ty ; try discriminate.
      simpl; auto.
      destruct o; try discriminate.
      congruence.
    Qed.

    Lemma comp_is_atom_Some : forall c a,
        comp_is_atom c = Some a -> c = CpAtom a.
    Proof. destruct c ; try discriminate.
           simpl; congruence.
    Qed.


    Lemma comp_not_actr_tailcomp : forall te c ty,
        typof_tailcomp te c = Some ty ->
      btyp_is_actr (btypof_tailcomp c) = false ->
      is_actr ty = None.
    Proof.
      unfold typof_tailcomp.
      intros.
      destruct (btypof_tailcomp c); try (inv H; reflexivity);
        simpl in H; monadInv H; try inv EQ0; try reflexivity.
      - simpl in H0. discriminate.
      - inv EQ2. reflexivity.
    Qed.


    Lemma comp_not_actr : forall te c ty,
      Typing.typof_comp te c = Some ty ->
      btyp_is_actr (btypof_comp c) = false ->
      is_actr ty = None.
    Proof.
      intros.
      apply comp_not_actr_tailcomp with (te:=te) (c:= TcComp c); eauto.
    Qed.




    Lemma para_eval_has_var : forall x r s,
        para_eval s r = true ->
        SSet.mem x s = true  ->
        BSet.union_list (fun x2 : ident * atom => AtomOrdered.has_var (snd x2)) r x = false.
    Proof.
      induction r; simpl.
      - unfold BSet.bot. reflexivity.
      - destruct a as (id,a).
        intros.
        rewrite andb_true_iff in H.
        destruct H.
        unfold BSet.union.
        rewrite orb_false_iff. simpl.
        split.
        + rewrite SSet.is_empty_correct in H.
          specialize (H x).
          rewrite SSet.mem_inter in H.
          rewrite andb_false_iff in H.
          destruct H; try congruence.
          change (SSet.bset (AtomOrdered.has_varb a) x = false) in H.
          rewrite AtomOrdered.has_var_eq in H. auto.
        +
          eapply IHr; eauto.
          rewrite SSet.mem_add. destruct (string_dec x id); auto.
    Qed.


    Lemma option_rel_intro_bind_r:
  forall {A B : Type} [R : B ->A -> Prop] (X:option B)  (x : option A),
  Coqlib.option_rel R X (let* v := x in Some v)%option_monad ->
  Coqlib.option_rel R X x.
    Proof.
      intros.
      destruct x; auto.
    Qed.

    
    Lemma eval_act_record_ok :
      forall te ge r l le le' s
             (WF : para_eval s r = true)
        (TYP : MapList.mmap typ (Typing.btyp_to_typ te)
                 (MapList.map btypof_atom r) =
                 Some l)
        (MATCH : match_on tabs (BSet.union_list (fun x => AtomOrdered.has_var (snd x)) r) ge le  ge le')
      ,
        Coqlib.option_rel (fun v v_le => fst v_le = Some tt /\ lenv_of_record tabs l v le' = snd v_le)
          (eval_act_record tabs (eval_atom tabs) te ge r l le)
          (eval_statement_rec tabs te ge le' TUnit
             (fold_right
                (fun '(x, a) (p : statement) =>
                   StSequence (StSet x (CpAtom a)) p)
                StSkip r)).
    Proof.
      induction r ; simpl.
      - destruct l.
        + intros. constructor. simpl. split; reflexivity.
        + discriminate.
      - intros.
        monadInv TYP.
        monadInv EQ.
        destruct a as (x,a).
        simpl.
        destruct (string_dec x x); try congruence.
        simpl in EQ0.
        rewrite bind2_bind; unfold uncurry.
        unfold Typing.typof_comp.
        simpl. rewrite EQ0.
        simpl.
        rewrite assoc_bind.
        rewrite match_on_union in MATCH.
        simpl in MATCH.
        destruct MATCH as (M1 & M2).
        eapply option_rel_bind_rel.
        {
          apply eval_atom_match_on with (te:=te) (ty := x1)
          in M1; eauto.
        }
        intros; subst.
        unfold ret. unfold bind at 2.
        unfold snd at 5.
        apply option_rel_intro_bind_r        .
        eapply option_rel_bind_rel.
        rewrite andb_true_iff in WF.
        destruct WF.
        eapply IHr; eauto.
        apply match_on_update_r; auto.
        eapply para_eval_has_var; eauto.
        rewrite SSet.mem_add. destruct (string_dec x x); try congruence.
        intros. constructor.
        simpl in H.
        destruct H ; tauto.
    Qed.


    Definition norm_begin_inv (i:ident) (ty:typ) (v_le : eval_typ tabs ty  * lenv tabs) (v1_le1 : (option (eval_typ tabs TUnit)) * lenv tabs) : Prop :=
      snd v1_le1 = Denot.lenv_update tabs (snd v_le) i (Denot.Val tabs ty (fst v_le)) /\
        fst v1_le1 = Some tt.


    Definition typ_of_option_ident (ty:typ) (o:option ident) : typ :=
      match o with
      | None => match is_actr ty with
                | None => ty
                |  _   => TUnit
                end
      | Some _ => TUnit
      end.


    Definition norm_tc_inv (oid:option ident) (ty:typ) :
      forall (v_le : eval_typ tabs ty  * lenv tabs)
             (v1_le1 : (option (eval_typ tabs (typ_of_option_ident ty oid)) * lenv tabs)), Prop.
    Proof.
      destruct oid.
      - exact (fun v_le v1_le1 => norm_begin_inv i ty v_le v1_le1).
      - simpl.
        destruct (is_actr ty) as [rt|].
        exact (fun v_le v1_le1 => exists v', cast_typ tabs (fst v_le) (TRecord None rt) = Some v' /\
                                        snd v1_le1 = lenv_of_record tabs  rt v' (snd v_le)).
        exact (fun v_le v1_le1 => fst v1_le1 = Some (fst v_le)).
    Defined.

    Lemma update_lenv_same : forall te ge init le le' x,
        update_lenv tabs (eval_tailcomp_rec tabs te ge) te init le = Some le' ->
        BSet.compl (BSet.union_list updated_by_binding init) x = true ->
        get_env tabs ge le' x =  get_env tabs ge le x.
    Proof.
      intros.
      symmetry.
      apply option_rel_eq_eq.
      apply update_lenv_not_updated in H.
      apply H; auto.
    Qed.

    Lemma no_overwrite_not_updated : forall x init ow,
        SSet.mem x ow = true ->
        no_overwrite ow init = true ->
        BSet.compl (BSet.union_list updated_by_binding init) x = true.
    Proof.
      induction init; simpl.
      - reflexivity.
      - intros.
        destruct a as (x1,tc).
        rewrite! andb_true_iff in H0.
        rewrite BSet.compl_union.
        unfold BSet.inter. rewrite andb_true_iff.
        split.
        + unfold updated_by_binding.
          simpl. rewrite BSet.compl_union.
          unfold BSet.inter. rewrite andb_true_iff.
          split.
          unfold BSet.compl. rewrite negb_true_iff.
          rewrite BSet.singleton_false_iff.
          intro. subst. rewrite negb_true_iff in H0.
          intuition congruence.
          destruct H0 as ((E & N) & OW).
          rewrite SSet.is_empty_correct in E.
          specialize (E x).
          rewrite SSet.mem_inter in E.
          rewrite andb_false_iff in E.
          destruct E. unfold BSet.compl, SSet.bset. rewrite H0. reflexivity.
          congruence.
        + destruct H0 as ((S1 & S2) & S3).
          eapply IHinit with (2:= S3).
          rewrite SSet.mem_add. rewrite H.
          destruct (string_dec x x1);auto.
    Qed.

   Lemma record_of_lenv_update_lenv :
      forall te ge init lty le le'
        (UP : update_lenv tabs (eval_tailcomp_rec tabs te ge) te init le = Some le')
        (OW : no_overwrite SSet.empty init = true)
        (TY : MapList.mmap typ (typof_tailcomp te) init = Some lty),
        exists r, record_of_lenv tabs ge lty le' = Some r.
    Proof.
      intros.
      revert OW.
      generalize SSet.empty as ow.
      revert lty le le' UP TY .
      induction init.
      - simpl. intros. inv TY. eexists. reflexivity.
      - simpl. intros.
        destruct a as (x,tc).
        monadInv UP. monadInv TY.
        monadInv EQ0.
        rename x0 into tytc.
        rename x1 into vtc.
        rename x2 into le1.
        rename x5 into ttc.
        rewrite! andb_true_iff in OW.
        assert (UP := EQ2).
        apply IHinit with (lty:= x4) (ow := SSet.add x ow) in EQ2;
          try tauto.
        destruct EQ2 as (r & EQR).
        simpl.
        apply update_lenv_same with (x:=x) in UP.
        rewrite UP.
        unfold get_env,lenv_update.
        rewrite STree.gss.
        simpl.
        simpl in EQ3. assert (tytc = ttc) by congruence.
        subst. rewrite cast_typ_id. simpl.
        rewrite EQR. simpl.
        eexists ; reflexivity.
        destruct OW.
        eapply no_overwrite_not_updated in H0;eauto.
        rewrite SSet.mem_add.
        destruct (string_dec x x); try congruence.
    Qed.

    Lemma ecast_typ_cast_typ : forall t1 t2 (v: option (eval_typ tabs t1)),
        ecast_typ tabs v t2 = (let* vl := v in cast_typ tabs vl t2)%option_monad.
    Proof.
      intros.
      unfold ecast_typ,cast_typ.
      destruct (typ_eq_dec t1 t2).
      - subst. destruct v; reflexivity.
      - destruct v; reflexivity.
    Qed.

    Lemma typof_tailcomp_body : forall te init body lty,
        BActR (MapList.map btypof_tailcomp init) = btypof_tailcomp body ->
        MapList.mmap typ (typof_tailcomp te) init = Some lty ->
        typof_tailcomp te body = Some (TRecord None lty).
    Proof.
      unfold typof_tailcomp.
      intros.
      rewrite <- H.
      simpl.
      rewrite MapList.mmap_map.
      rewrite H0. reflexivity.
    Qed.

    Lemma forall2b_refl : forall {A: Type} (P: A -> A -> bool) l,
      (forall x, In x l -> P x x = true) ->
      forall2b P l l = true.
    Proof.
      induction l ;simpl; auto.
      intros.
      rewrite H.
      apply IHl;auto.
      tauto.
    Qed.

    Lemma norm_correct_fw:
      forall te ge tc  le ty oi
             (WF : wf_tailcomp te tc = true)
             (TYP: typof_tailcomp te tc = Some ty)
             s,
        norm_tailcomp oi tc = OK s ->
        Coqlib.option_rel (norm_tc_inv oi ty) (ImpBNF.eval_tailcomp_rec tabs te ge le ty tc)
                                                     (Imp1Pure.eval_statement_rec tabs te ge le (typ_of_option_ident ty oi) s).
    Proof.
      induction tc using tailcomp_depth_ind; simpl; intros.
      - (* Sequence *)
        Res.monadInv H. inv EQ2.
        simpl.
        rename x0 into s1.
        rename x1 into s2.
        rewrite! andb_true_iff in WF.
        assert (exists ty1, typof_tailcomp te tc1 = Some ty1).
        {
          apply wf_tailcomp_btyp_to_typ.
          tauto.
        }
        destruct H as (ty1 & TTC1).
        rewrite TTC1. simpl.
        rewrite bind2_bind. unfold uncurry.
        eapply option_rel_bind_rel with (RA:= norm_tc_inv (Some x) ty1).
        { change TUnit with (typ_of_option_ident ty1 (Some x)).
          eapply IHtc1; eauto.
          tauto.
        }
        intros.
        destruct y.
        unfold norm_tc_inv in H.
        unfold norm_begin_inv in H.
        simpl in H. destruct H ; subst.
        eapply IHtc2; eauto.
        tauto.
        { unfold typof_tailcomp in TYP. simpl in TYP.
          rewrite btyp_eqb_eq in WF.
          unfold typof_tailcomp. intuition congruence.
        }
      - (* while *)
        destruct (MapList.nodup string_dec init) eqn:DUP;
          try discriminate.
        Res.monadInv H0. inv EQ3.
        rename x into init'.
        rename tc1 into body.
        rename x0 into body'.
        simpl.
        rewrite! bind2_bind.
        unfold uncurry.
        rewrite! assoc_bind.
        eapply option_rel_bind_rel with (RA := fun le1 vle2 =>
                                                 le1 = snd vle2).
        {
          rewrite! andb_true_iff in WF.
          assert (WFI : forallb (fun x : ident * tailcomp => wf_tailcomp te (snd x)) init =
     true) by tauto.
          clear IHtc1 IHtc2.
          revert EQ.
          clear - H WFI.
          revert  le init'.
          induction init.
          - intros. inv EQ.
            simpl. constructor.
            reflexivity.
          - simpl.
            intros.
            simpl in WFI. rewrite andb_true_iff in WFI.
            destruct WFI as (WF1 & WF2).
            destruct a as (id,tc).
            Res.monadInv EQ.
            simpl.
            simpl in WF1.
            assert (exists ty1, typof_tailcomp te tc = Some ty1).
            {
              apply wf_tailcomp_btyp_to_typ.
              tauto.
            }
            destruct H0 as (ty1 & TTC); simpl.
            rewrite TTC. simpl.
            rewrite bind2_bind. unfold uncurry.
            change TUnit with (typ_of_option_ident ty1 (Some id)).
            eapply option_rel_bind_rel with
              (RA:= norm_tc_inv (Some id) ty1).
            { eapply H;eauto.  simpl. left; tauto. }
            intros. clear H1 H2.
            unfold norm_tc_inv in H0.
            unfold norm_begin_inv in H0.
            simpl in *. destruct H0 ; subst.
            destruct y. simpl in *. subst.
            eapply IHinit; auto; clear IHinit.
            {
              intros.
              eapply H;eauto.
            }
        }
        (** All the loop variable are part of the environment - but weird things can happen *)
        intros. subst.
        rewrite assoc_bind.
        eapply option_rel_bind_equal.
        intros.
        rewrite assoc_bind.
        eapply option_rel_bind_equal.
        intros.
        rewrite assoc_bind.
        eapply option_rel_bind_equal.
        intros.
        rewrite assoc_bind.
        assert (TYINIT : exists lty, MapList.mmap typ (typof_tailcomp te) init = Some lty).
        {
          rewrite !andb_true_iff in WF.
          assert (WFI :forallb (fun x : ident * tailcomp => wf_tailcomp te (snd x)) init =
                         true) by tauto.
          clear - WFI. induction init.
          - simpl. exists nil. reflexivity.
          - simpl.
            simpl in WFI.
            rewrite andb_true_iff in WFI.
            assert (exists ty, typof_tailcomp te (snd a) = Some ty).
            {
              apply wf_tailcomp_btyp_to_typ. tauto.
            }
            destruct H as (ty & H).
            rewrite H. simpl.
            destruct WFI as (WF1 & WF2).
            apply  IHinit in WF2.
            destruct WF2 as (lty & WF2).
            rewrite WF2. simpl.
            eexists ; reflexivity.
        }
        destruct TYINIT as (lty & TYINIT).
        rewrite TYINIT. simpl.
        assert (REC : exists r, record_of_lenv tabs ge lty (snd y) =
                                  Some r).
        {
          eapply record_of_lenv_update_lenv; eauto.
          rewrite! andb_true_iff in WF.
          tauto.
        }
        destruct REC as (rinit & REC).
        rewrite REC. simpl.
        eapply option_rel_bind_rel with (RA:= eq).
        destruct y as (vi,leinit).
        simpl in *.
        assert (INIT2 : lenv_of_record tabs lty rinit  leinit = leinit).
          {
            apply lenv_of_record_of_lenv with (ge:=ge) ; auto.
            - eapply update_lenv_mem;eauto.
            -
              {
                rewrite <- DUP.
                symmetry.
                apply MapList.nodup_fst.
                eapply MapList.mmap_fst; eauto.
              }
          }
          assert (WFB : wf_tailcomp te body = true).
          { rewrite !andb_true_iff in WF. tauto. }
          assert (TYBODY : typof_tailcomp te body = Some (TRecord None lty)).
          {
            rewrite! andb_true_iff in WF.
            rewrite! btyp_eqb_eq in WF.
            intuition idtac.
            eapply typof_tailcomp_body; eauto.
          }
          { rewrite <- INIT2 at 1.
            clear H.
            rewrite INIT2.
            clear H1 H2 H3 REC INIT2 WF IHtc2 H4.
          revert leinit rinit.
          induction a1; simpl; auto.
          - intros.
            apply option_rel_bind_equal.
            intros. destruct a1.
            rewrite! bind2_bind. unfold uncurry.
            eapply option_rel_bind_rel with (RA:=eq).
            change TUnit with (typ_of_option_ident (TRecord None lty)
                                 None).
            eapply option_rel_bind_rel with (RA := (norm_tc_inv None (TRecord None lty))).
            eapply IHtc1; auto.
            intros.
            constructor.
            unfold norm_tc_inv in H1.
            simpl in H1.
            destruct H1. destruct H1. destruct y; simpl in *.
            rewrite cast_typ_id in H1. inv H1. reflexivity.
            intros; subst.
            constructor.
            constructor;auto.
          - intros.
            apply option_rel_bind_equal.
            intros. destruct a2.
            rewrite! bind2_bind. unfold uncurry.
            eapply option_rel_bind_rel with (RA:=eq).
            change TUnit with (typ_of_option_ident (TRecord None lty)
                                 None).
            eapply option_rel_bind_rel with (RA := (norm_tc_inv None (TRecord None lty))).
            eapply IHtc1; auto.
            intros.
            constructor.
            unfold norm_tc_inv in H1.
            simpl in H1.
            destruct H1. destruct H1. destruct y; simpl in *.
            rewrite cast_typ_id in H1. inv H1. reflexivity.
            intros; subst.
            apply IHa1; auto.
            constructor. reflexivity.
          }
          intros ; subst.
          eapply IHtc2;auto.
          rewrite! andb_true_iff in WF. tauto.
          { clear - WF TYP.
            unfold typof_tailcomp in TYP.
            simpl in TYP.
            rewrite! andb_true_iff in WF.
            rewrite btyp_eqb_eq in WF.
            unfold typof_tailcomp.
            intuition congruence.
          }
      -
        rewrite  andb_true_iff in WF.
        destruct WF as (WF1 & WF2).
        destruct oi.
        + inv H.
          unfold eval_statement_rec.
          eapply option_rel_bind_equal.
          intros.
          rewrite ecast_typ_cast_typ.
          rewrite assoc_bind.
          eapply option_rel_bind_equal.
          unfold typof_tailcomp in TYP.
          simpl in TYP.
          unfold Typing.typof_comp in H.
          assert (ty = a) by congruence; subst.
          intros.
          rewrite cast_typ_id. simpl.
          constructor.
          unfold norm_begin_inv.
          simpl. tauto.
        +   assert (NACTR : is_actr ty = None).
            {
              eapply comp_not_actr with (te:=te) (c:=  c).
              unfold Typing.typof_comp. simpl.
              auto.
              rewrite negb_true_iff in WF2.
              auto.
            }
          destruct (comp_is_atom c) eqn:ATOM.
          * inv H.
            rewrite convertible_btyp_iff in WF1.
            destruct WF1 as (ty1 & TY).
            unfold Typing.typof_comp.
            rewrite TY. unfold bind at 1.
            unfold eval_statement_rec.
            apply comp_is_atom_Some in ATOM.
            subst. unfold eval_comp.
            simpl in TY.
            unfold Typing.typof_atom.
            rewrite TY. unfold bind at 2.
            unfold typof_tailcomp in TYP.
            simpl in TYP.
            assert (ty = ty1) by congruence ; subst.
            rewrite! ecast_typ_id.
            unfold typ_of_option_ident.
            eapply option_rel_bind_equal.
            simpl.
            destruct (is_actr ty1); try discriminate.
            intros.
            constructor.
            rewrite cast_typ_id. reflexivity.
          * inv H.
            unfold eval_statement_rec.
            rewrite bind2_bind; unfold uncurry.
            rewrite assoc_bind.
            apply option_rel_bind_equal.
            intros.
            rewrite assoc_bind.
            assert (a = ty).
            { unfold typof_tailcomp in TYP.
              simpl in TYP. unfold Typing.typof_comp in H.
              congruence.
            } subst.
            rewrite ecast_typ_id.
            eapply option_rel_bind_equal.
            intros.
            unfold ret. unfold bind.
            unfold Typing.typof_atom.
            unfold btypof_atom.
            unfold Typing.typof_comp in H.
            rewrite H. simpl.
            destruct (is_actr ty); try discriminate.
            rewrite eval_var_lenv_update.
            constructor.
            rewrite cast_typ_id. reflexivity.
      - inv H.
        unfold typof_tailcomp in TYP.
        simpl in TYP.
        rewrite! andb_true_iff in WF.
        rewrite btyp_eqb_eq in WF.
        destruct WF as ((WF1 & WF2) & WF3).
        subst. simpl in TYP.
        rewrite MapList.mmap_map in TYP.
        monadInv TYP.
        inv EQ0.
        simpl. rewrite MapList.mmap_map.
        rewrite EQ.
        cbn.
        rewrite forall2b_refl.
        destruct oi; try discriminate.
        inv H1.
        {
          unfold typ_of_option_ident. unfold is_actr.
          rename x into lty.
          rewrite <- MapList.mmap_map in EQ.
          apply option_rel_intro_bind_r.
          eapply option_rel_bind_rel.
          eapply eval_act_record_ok; eauto.
          apply match_on_refl.
          intros.
          simpl in H. constructor;auto.
          simpl. rewrite cast_typ_id.
          eexists ; split; auto.
          intuition congruence.
        }
        { intros.
          unfold ExtOrdered.pair_eqb.
          destruct x0. rewrite String.eqb_refl.
          rewrite typ_eqb_true. reflexivity.
        }
      - Res.monadInv H.
        inv EQ2.
        simpl.
        eapply option_rel_bind_equal.
        intros.
        rewrite! andb_true_iff in WF.
        intuition idtac.
        unfold typof_tailcomp in TYP.
        simpl in TYP.
        rewrite btyp_eqb_eq in H5.
        rewrite btyp_eqb_eq in H4.
        subst.
        destruct a0.
        + eapply IHtc1;eauto.
          unfold typof_tailcomp.
          congruence.
        + eapply IHtc2;eauto.
      - Res.monadInv H0.
        inv EQ0.
        simpl.
        apply option_rel_bind_equal.
        intros.
        apply option_rel_bind_equal.
        intros.
        rename x into cases'.
        rewrite! andb_true_iff in WF.
        destruct WF as ((C1 & ALL1) & ALL2).
        unfold Denot.eval_match.
        destruct a0; try constructor.
        clear H0 H1.
        unfold typof_tailcomp in TYP.
        simpl in TYP.
        assert (ALL1': forall p tc, In (p,tc) cases ->
                             typof_tailcomp te tc = Some ty0).
        {
          intros.
          rewrite forallb_forall in ALL1.
          apply ALL1 in H0.
          rewrite btyp_eqb_eq in H0.
          subst.
          unfold typof_tailcomp. congruence.
        }
        clear ALL1.
        revert cases' ALL1' ALL2 EQ .
          { induction cases.
            - simpl. intros. destruct cases'; try discriminate.
              simpl. constructor.
            - intros. simpl.
              simpl in EQ.  destruct a0 as (p,tc).
              Res.monadInv EQ.
              Res.monadInv EQ0.
              inv EQ2. simpl.
              simpl in ALL2.
              rewrite andb_true_iff in ALL2.
              destruct p.
              apply option_rel_bind_equal.
              intros.
              destruct (Benum.enum_eq a0 a1) eqn:ENUM.
              +
                eapply H.
                simpl. left; reflexivity.
                tauto.
                eapply ALL1'.
                simpl ; left; reflexivity.
                auto.
              + eapply IHcases.
                intros.
                eapply H ; eauto.
                simpl. right. eauto.
                intros.
                eapply  ALL1'.
                simpl. right; eauto.
                tauto.
                auto.
              +                 eapply H.
                simpl. left; reflexivity.
                tauto.
                eapply ALL1'.
                simpl ; left; reflexivity.
                auto.
          }
      - Res.monadInv H.
        inv EQ0. simpl.
        eapply IHtc; eauto.
    Qed.

  Theorem norm_tailcomp_correct:
    forall te ge le tc s ty,
      is_actr ty = None ->
      wf_tailcomp te tc = true ->
      typof_tailcomp te tc = Some ty ->
      norm_tailcomp None tc = OK s ->
      Imp1Pure.eval_statement tabs te ge le ty s =
        ImpBNF.eval_tailcomp tabs te ge le ty tc.
  Proof.
    intros.
    symmetry.
    apply option_rel_eq_eq.
    unfold eval_tailcomp. unfold eval_statement.
    assert (ST : ty = typ_of_option_ident ty None).
    {
      unfold typ_of_option_ident.
      rewrite H. reflexivity.
    }
    assert (NC := norm_correct_fw te ge tc le ty None H0 H1 _ H2).
    inv NC.
    - simpl.
      destruct ty ; simpl in H5;
        try discriminate; try rewrite <- H5; try constructor.
      destruct o; try discriminate.
      rewrite <- H5. constructor.
    - simpl in ST.
      destruct ty ; try discriminate; simpl in *;
        try rewrite <- H4;
      destruct x,y; simpl in *;
        subst; try (constructor; reflexivity).
      destruct o; try discriminate.
      simpl in H5. subst.
      rewrite <- H4. constructor. reflexivity.
  Qed.


  Lemma norm_function_correct_aux:
    forall params tc s te ge le tret,
      wf_tailcomp te tc = true ->
      is_actr tret = None ->
      typof_tailcomp te tc = Some tret ->
      norm_tailcomp None tc = OK s ->
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
    Denot.eval_def_fun tabs (Imp1Pure.eval_statement tabs) te ge x f' =
    Denot.eval_def_fun tabs (ImpBNF.eval_tailcomp tabs) te ge x f.
  Proof.
    unfold norm_function; intros.
    destruct (wf_tailcomp te (fn_body f) && btyp_eqb (btypof_tailcomp (fn_body f)) (fn_return f) && negb (btyp_is_actr (fn_return f))) eqn:Ewf_body.
    + Res.monadInv H. inv EQ0. destruct f; simpl in *.
      unfold Denot.eval_def_fun; simpl.
      rewrite! andb_true_iff in Ewf_body.
      destruct Ewf_body as ((WF1 & WF2)& WF3).
      rewrite negb_true_iff in WF3.
      rewrite btyp_eqb_eq in WF2. subst.
      destruct (MapList.nodup Ident.eq_dec fn_params); try reflexivity.
      apply option_rel_eq_eq.
      repeat (apply option_rel_bind_equal; intros).
      apply option_rel_eq_eq.
      repeat f_equal.
      apply norm_function_correct_aux; auto.
      eapply comp_not_actr_tailcomp      ; eauto.
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
