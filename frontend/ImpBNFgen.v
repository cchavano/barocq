From Stdlib Require Import String List Eqdep.
From compcert Require Import Coqlib.
From compcert Require Axioms.
From BarocqComp Require Import Res Syntax Utils Denot Types BarocqBNF ImpBNF Maps2 Denot.
Import ListNotations.

Open Scope string_scope.

Local Open Scope error_monad_scope.

Fixpoint transl_expr (e: expr) : res tailcomp :=
  match e with
  | EAtom a => eret (TcComp (CpAtom a))
  | EArraySet a1 a2 a3 ty => eret (TcComp (CpArraySet a1 a2 a3 ty))
  | ERecordUpdate a1 x a2 ty => eret (TcComp (CpRecordUpdate a1 x a2 ty))
  | EApp a args ty =>
      do (fid, tf) <-
        match a with
        | AVar x tx => eret (x, tx)
        | _ => efail
        end;
      eret (TcComp (CpCall fid tf args ty))
  | ELetIn x e1 e2 ty =>
      do tc1 <- transl_expr e1;
      do tc2 <- transl_expr e2;
      eret (TcBegin x tc1 tc2 ty)
  | EIfThenElse a e1 e2 ty =>
      do tc1 <- transl_expr e1;
      do tc2 <- transl_expr e2;
      eret (TcIfThenElse a tc1 tc2 ty)
  | EMatch a cases ty =>
      do cases' <- MapList.map_err transl_expr cases;
      eret (TcSwitch a cases' ty)
  | EActR l ty => OK (TcActRecord l ty)
  | ELetW init cond decr body e2 ty =>
      do init' <- MapList.map_err transl_expr init;
      do body'  <- transl_expr body;
      do e2'    <- transl_expr e2;
      eret (TcWhile init' cond decr body' e2' ty)
  | EAttr id e =>
      do tc <- transl_expr e;
      eret (TcAttr id tc)
  end.

Definition check_params_noshadow {A T: Type} (ge: STree.t A) (ls_init: SSet.t) (params: smaplist T) : res SSet.t :=
  list_fold_left_err
    (fun acc '(pi, _) =>
      match STree.get pi ge with
      | Some _ => efail
      | None =>
        if negb (SSet.mem pi acc) then eret (SSet.add pi acc)
        else efail
      end)
    params
    (ls_init).

Definition transl_function (gs: SSet.t) (f: BarocqBNF.function) : res ImpBNF.function :=
  if wf_expr gs (sset_of_bindings (fn_params f)) (fn_body f) then
    do body <- transl_expr (fn_body f);
    eret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}
  else efail.

Definition transl_globdef (gs: SSet.t) (def: BarocqBNF.globdef) : res ImpBNF.globdef :=
  match def with
  | DefConst x l ty => eret (DefConst x l ty)
  | DefFun x f =>
      do f' <- transl_function gs f;
      eret (DefFun x f')
  | DeclConst x ty => eret (DeclConst x ty)
  | DeclFun f tparams tret => eret (DeclFun f tparams tret)
  end.

Fixpoint transl_prog_defs (gs: SSet.t) (defs: list BarocqBNF.globdef) : res (list ImpBNF.globdef) :=
  match defs with
  | nil => eret nil
  | d :: defs' =>
      do d' <- transl_globdef gs d;
      do dr <- transl_prog_defs (SSet.add (globdef_id d) gs) defs';
      eret (d' :: dr)
  end. 

Definition transl_program (prog: BarocqBNF.program) : res ImpBNF.program :=
  do defs <- transl_prog_defs SSet.empty (prog_defs prog);
  eret {|
    prog_defs := defs;
    prog_types := prog_types prog;
    prog_tabs := prog_tabs prog;
  |}.

Section CORRECTNESS.

  Variable tabs : Maps.PMap.t Type.

  Notation genv := (@Denot.genv tabs).

  Notation lenv := (@Denot.lenv tabs).

  Theorem transl_expr_preserve_typ :
    forall te e tc,
      transl_expr e = OK tc ->
      ImpBNF.typof_tailcomp te tc = BarocqBNF.typof_expr te e.
  Proof.
    induction e; unfold BarocqBNF.typof_expr, ImpBNF.typof_tailcomp,
    ImpBNF.btypof_tailcomp; fold btypof_tailcomp; simpl; intros.
    - inversion H. reflexivity.
    - inversion H. reflexivity.
    - inversion H. reflexivity. 
    - destruct a; try discriminate.
      inv H. reflexivity.
    - monadInv H. inv EQ2. reflexivity.
    - monadInv H. inv EQ0. reflexivity.
    - monadInv H. inv EQ2. reflexivity.
    - monadInv H. reflexivity.
    - monadInv H. inv EQ3. reflexivity.
    - monadInv H. inv EQ0. simpl.
      eapply IHe; eauto.
  Qed.
  

  Lemma eval_var_match_lenv_eq:
    forall ge le1 le2 x ty v,
      env_noshadow ge le2 ->
      match_lenv tabs le1 le2 ->
      ((lenv_get tabs le1 x = Some v) \/ (genv_get tabs ge x = Some v)) ->
      eval_var tabs ge le2 x ty = eval_var tabs ge le1 x ty.
  Proof.
    intros.
    assert (ME : match_env tabs ge le1 ge le2).
    { apply match_lenv_match_env; auto. }
    unfold eval_var.
    specialize (ME x). inv ME.
    - simpl.
      symmetry in H3.
      unfold get_env,lenv_get,genv_get in *.
      destruct H1.
      + rewrite H1 in H3. discriminate.
      + rewrite H1 in *.
        specialize (H0 x).
        unfold lenv_get in H0.
        inv H0.
        rewrite <- H4 in H3. discriminate.
        apply H in H1.
        rewrite H1 in *.
        rewrite H5 in H3. discriminate.
    - rewrite H4.
      apply Option.bind_equal.
      reflexivity.
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
    match_lenv tabs le1 le2 ->
    (forall a ty,
        wf_atom (STree.keys ge) (STree.keys le1) a = true ->
      eval_atom tabs te ge le2 ty a =
      eval_atom tabs te ge le1 ty a).
  Proof.
    induction a using atom_depth_ind; simpl; intros; try tauto.
    - apply var_defined_env_get in H1; try tauto.
      destruct H1. eapply eval_var_match_lenv_eq; eauto.
    - destruct (Typing.btyp_to_typ te t); simpl; try reflexivity.
      destruct (Typing.typof_atom te a); simpl; try reflexivity.
      erewrite IHa; eauto.
    - destruct (Typing.typof_atom te a); simpl; try reflexivity.
      erewrite IHa; eauto.
    - destruct (Typing.typof_atom te a1); simpl; try reflexivity.
      destruct (Typing.typof_atom te a2); simpl; try reflexivity.
      apply andb_prop in H1. destruct H1.
      erewrite IHa1; eauto.
      erewrite IHa2; eauto.
    - destruct (Typing.typof_atom te a1); simpl; try reflexivity.
      destruct (Typing.typof_atom te a2); simpl; try reflexivity.
      apply andb_prop in H1. destruct H1.
      erewrite IHa1; eauto.
      erewrite IHa2; eauto.
    - destruct (Typing.typof_atom te a); simpl; try reflexivity.
      erewrite IHa; eauto.
  (*  -  destruct ty0;auto.
       revert l0.
       induction l; simpl.
       + destruct l0; auto.
       + destruct a as (x1,e1).
         simpl in H2.
         rewrite andb_true_iff in H2.
         destruct H2 as [ALL1 ALL2].
         destruct l0;auto.
         destruct p as (x1',t1).
         destruct (string_dec x1 x1');auto.
         * subst.
           rewrite (H1 (x1',e1)).
           unfold snd.
           destruct (eval_atom tabs te ge le1 t1 e1); auto.
           rewrite IHl; auto.
           intros. apply H1;auto.
           simpl. tauto.
           simpl. tauto.
           tauto. *)
    - destruct (Typing.btyp_to_typ te tf); simpl; try reflexivity.
      apply andb_prop in H2. destruct H2.
      apply var_defined_env_get in H2; try tauto.
      destruct H2. destruct t; simpl; try reflexivity.
      erewrite eval_var_match_lenv_eq; eauto.
      destruct (eval_var tabs ge le1 i (TFun l t)); simpl; try reflexivity.
      assert (DList.map2 (eval_typ tabs) (eval_atom tabs te ge le2) args l =
                DList.map2 (eval_typ tabs) (eval_atom tabs te ge le1) args l).
      {
        apply DList.map2_eq.
        assert (forall x ty,
                   In x args ->
                       eval_atom tabs te ge le2 ty x =
                         eval_atom tabs te ge le1 ty x).
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
      match_lenv tabs le1 le2 ->
      (forall c ty, wf_comp (STree.keys ge) (STree.keys le1) c = true ->
        eval_comp tabs te ge le2 ty c =
        eval_comp tabs te ge le1 ty c).
  Proof.
    induction c; simpl; intros.
    - apply eval_atom_match_lenv_eq; tauto.
    - destruct_conj H1.
      destruct (Typing.typof_atom te a); simpl; try reflexivity.
      destruct (Typing.typof_atom te a0); simpl; try reflexivity.
      destruct (Typing.typof_atom te a1); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom tabs te ge le1 t a); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom tabs te ge le1 t0 a0); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
    - destruct_conj H1.
      destruct (Typing.typof_atom te a); simpl; try reflexivity.
      destruct (Typing.typof_atom te a0); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
      destruct (eval_atom tabs te ge le1 t a); simpl; try reflexivity.
      erewrite eval_atom_match_lenv_eq; eauto.
    - destruct_conj H1.
      destruct (Typing.btyp_to_typ te b); simpl; try reflexivity.
      destruct t; try reflexivity.
      eapply var_defined_env_get in C; eauto. destruct C.
      erewrite eval_var_match_lenv_eq; eauto.
      destruct (eval_var tabs ge le1 i (TFun l0 t)); simpl; try reflexivity.
      assert (EQ: DList.map2 (eval_typ tabs) (eval_atom tabs te ge le2) l l0 =
                DList.map2 (eval_typ tabs) (eval_atom tabs te ge le1) l l0).
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

  Import Option.

  Ltac destruct_bind :=
    match goal with
    | H : (bind ?V _) = Some _ |- context[?V] => destruct V; simpl in H
    end.

  Lemma eval_act_record_ok :
    forall te ge le1 le2 l l0
           (WF :
             forallb
               (fun x : ident * atom =>
                  wf_atom (STree.keys ge) (STree.keys le1) (snd x))
               l =
               true)
           (NOSHADOW : env_noshadow ge le2)
           (MATCH_LENV : match_lenv tabs le1 le2),
      eval_act_record tabs (eval_atom tabs) te ge l l0 le2 = eval_act_record tabs (eval_atom tabs) te ge l l0 le1.
Proof.
  induction l; simpl; auto.
  - destruct a.
    destruct l0; try congruence.
    destruct p.
    destruct (string_dec i s); try congruence.
    subst.
    intros.
    rewrite andb_true_iff in WF.
    destruct WF as (WF1 & WF2).
    rewrite eval_atom_match_lenv_eq with (le1 := le1) by auto.
    rewrite IHl by auto.
    reflexivity.
Qed.

Lemma var_defined_le : forall G L L' i,
  var_defined G L i = true ->
  (forall x : StringIndexed.t, SSet.mem x L = true -> SSet.mem x L' = true) ->
  var_defined G L' i = true.
Proof.
  unfold var_defined. intros.
  rewrite! orb_true_iff in *.
  destruct H; try tauto.
  left. apply H0 ; auto.
Qed.

Lemma wf_atom_le  (G L L': SSet.t) a :
    wf_atom G L a = true ->
    (forall x, SSet.mem x L = true -> SSet.mem x L' = true) ->
    wf_atom G L' a = true.
Proof.
  induction a using atom_depth_ind; simpl; auto.
  - apply var_defined_le.
  - intros. rewrite! andb_true_iff in *. destruct H.
    split; eauto.
  - intros. rewrite! andb_true_iff in *. destruct H.
    split; eauto.
  - intros. rewrite! andb_true_iff in *.
    destruct H0 ; split;eauto.
    eapply var_defined_le;eauto.
    rewrite! forallb_forall in *.
    intros.
    eapply H ; eauto.
Qed.

Lemma add_bindings_add_assoc : forall {A: Type} x S (l:list (ident * A)),
  add_bindings (SSet.add x S) l =
  SSet.add x (add_bindings S l).
Proof.
  induction l; simpl; auto.
  - rewrite! IHl.
    rewrite SSet.add_swap.
    reflexivity.
Qed.


Lemma update_seq_lenv_keys : forall te ge l acc lei,
    update_seq_lenv tabs (eval_expr tabs te ge) te l
      acc = Some lei ->
    forall x,
      SSet.mem x (STree.keys lei) =
        SSet.mem x (STree.keys acc) || MapList.mem string_dec x l.
Proof.
  induction l; simpl.
  - intros.
    inv H.
    rewrite orb_false_r.
    reflexivity.
  - intros.
    monadInv H.
    destruct a.
    apply IHl with (x:=x) in EQ2.
    rewrite EQ2.
    unfold lenv_update.
    simpl.
    rewrite STree.keys_set.
    rewrite SSet.mem_add.
    destruct (string_dec i x); destruct (string_dec x i); try congruence.
    subst.
    simpl. rewrite orb_comm. reflexivity.
Qed.

Lemma update_seq_lenv_keys_eq : forall te ge l acc lei,
    update_seq_lenv tabs (eval_expr tabs te ge) te l
      acc = Some lei ->
    STree.keys lei = add_bindings (STree.keys acc) l.
Proof.
  induction l; simpl.
  - congruence.
  - intros.
    monadInv H.
    apply IHl in EQ2.
    rewrite EQ2.
    rewrite keys_lenv_update.
    rewrite add_bindings_add_assoc.
    reflexivity.
Qed.


Lemma match_lenv_get_env : forall ge le1 le2 x v,
    match_lenv tabs le1 le2 ->
    env_noshadow ge le2 ->
    get_env tabs ge le1 x  = Some v ->
    get_env tabs ge le2 x = Some v.
Proof.
  unfold get_env.
  intros.
  specialize (H x). inv H.
  unfold lenv_get in H3.
  rewrite <- H3 in H1.
  destruct (STree.get x le2) eqn:EQ;auto.
  apply H0 in H1. congruence.
  unfold lenv_get in H4. rewrite <- H4.
  auto.
Qed.


Lemma record_of_lenv_match_env : forall ge rt le1 le2 r,
  record_of_lenv tabs ge rt le1 = Some r ->
  match_lenv tabs le1 le2 ->
  env_noshadow ge le2 ->
  record_of_lenv tabs ge rt le2 = Some r.
Proof.
  induction rt ; simpl; auto.
  - intros. monadInv H.
    eapply match_lenv_get_env in EQ; eauto.
    rewrite EQ. simpl.
    rewrite EQ1. simpl.
    eapply IHrt in EQ0; eauto.
    rewrite EQ0.
    simpl. reflexivity.
Qed.


Lemma update_seq_lenv_less_def :
  forall te ge l le1 le1'
         (WF: wf_init (STree.keys ge) (wf_expr (STree.keys ge)) (STree.keys le1) l =
                true),

    update_seq_lenv tabs (eval_expr tabs te ge) te l le1 = Some le1' ->
    match_lenv tabs le1 le1'.
Proof.
  induction l; simpl.
  -  intros. inv H.
     apply match_lenv_refl.
  - intros.
    monadInv H.
    rewrite! andb_true_iff in WF.
    eapply IHl in EQ2.
    eapply match_lenv_trans; eauto.
    apply match_lenv_update1.
    destruct WF as ((WFa & _) & _).
    unfold wf_binding in WFa.
    rewrite! andb_true_iff in WFa.
    rewrite! negb_true_iff in WFa.
    unfold lenv_get. rewrite STree.keys_get_mem_false_iff.
    tauto.
    rewrite keys_lenv_update.
    tauto.
Qed.

Lemma transl_expr_same_typ :
  forall te l init',
    MapList.map_err transl_expr l = OK init' ->
    MapList.mmap _  (typof_expr te) l = MapList.mmap (key:=ident) _ (typof_tailcomp te) init'.
Proof.
  induction l; simpl.
  - intros. inv H.
    reflexivity.
  - intros.
    Res.monadInv H.
    destruct a.
    Res.monadInv EQ.
    inv EQ2.
    simpl.
    rewrite transl_expr_preserve_typ with (e:=e); auto.
    apply bind_equal.
    intros.
    apply bind_gequal.
    apply IHl in EQ1.
    rewrite EQ1.
    apply option_rel_refl.
    unfold RelationClasses.Reflexive.
    reflexivity.
Qed.

Lemma keys_lenv_of_record_same : forall rt r le,
  (forall (x0 : StringIndexed.t) (v : typ),
    In (x0, v) rt -> SSet.mem x0 (STree.keys le) = true) ->
    STree.keys (lenv_of_record tabs rt r le) =
      STree.keys le.
Proof.
  induction rt; simpl; auto.
  intros.
  destruct a.
  simpl.
  rewrite IHrt; auto.
  -
    rewrite keys_lenv_update.
    apply SSet.add_already_mem.
    eapply H. left; reflexivity.
  - intros.
    rewrite keys_lenv_update.
    rewrite SSet.mem_add.
    destruct (string_dec x0  t); auto.
    eapply H; eauto.
Qed.

Lemma  match_lenv_lenv_of_record:
  forall  (lt : @MapList.t string typ) (r : eval_recordtyp (eval_typ tabs) lt)
          (le1 le2 : lenv),
    match_lenv tabs le1 le2 ->
    match_lenv tabs (lenv_of_record tabs lt r le1)
      (lenv_of_record tabs lt r le2).
Proof.
  induction lt; simpl.
  - auto.
  - intros.
    apply IHlt.
    apply match_lenv_update2; auto.
Qed.

Lemma env_noshadow_keys : forall (ge:genv) (le le':lenv),
    STree.keys le = STree.keys le' ->
    env_noshadow ge le ->
    env_noshadow ge le'.
Proof.
  unfold env_noshadow; repeat intro.
  apply H0 in H1.
  rewrite STree.keys_get_mem_false_iff in *.
  congruence.
Qed.

Lemma get_lenv_of_record : forall rt r le x,
  ~ In x (map fst rt) ->
  STree.get x (lenv_of_record tabs rt r le)  = STree.get x le.
Proof.
  induction rt; simpl;auto.
  - intros.
    destruct (string_dec (fst a) x).
    + tauto.
    + destruct (In_dec string_dec x (map fst rt)).
      * tauto.
      * rewrite IHrt by auto.
        unfold lenv_update.
        rewrite STree.gsspec.
        destruct a as (x',ty); simpl in *.
        destruct (STree.elt_eq x x'); try congruence.
Qed.


Lemma match_lenv_new_keys : forall le1 le2 rt r,
    match_lenv tabs le1 le2 ->
    (forall x v, In (x,v) rt -> SSet.mem x (STree.keys le1) = false) ->
    match_lenv tabs le1 (lenv_of_record tabs rt r le2).
Proof.
  unfold match_lenv.
  intros.
  generalize (H x).
  intro Hx ; inv Hx.
  constructor.
  destruct (In_dec string_dec x (map fst rt)).
  - rewrite in_map_iff in i.
  destruct i as (st & EQ & IN).
  destruct st ; simpl in *.
  subst.
  apply H0 in IN.
  rewrite <- STree.keys_get_mem_false_iff in IN.
  unfold lenv_get. rewrite IN. constructor.
  - unfold lenv_get in *. rewrite get_lenv_of_record by auto.
    rewrite H3.
    apply less_def_refl.
Qed.


Lemma match_env_new_keys : forall ge1 le1 ge2 le2 rt r,
    match_env tabs ge1 le1 ge2 le2 ->
    (forall x v, In (x,v) rt -> SSet.mem x (STree.keys le1) = false) ->
    (forall x v, In (x,v) rt -> SSet.mem x (STree.keys ge1) = false) ->
    match_env tabs ge1 le1 ge2 (lenv_of_record tabs rt r le2).
Proof.
  unfold match_env.
  intros.
  generalize (H x).
  intro Hx ; inv Hx.
  constructor.
  destruct (In_dec string_dec x (map fst rt)).
  - rewrite in_map_iff in i.
    destruct i as (st & EQ & IN).
    destruct st ; simpl in *.
    subst.
    specialize (H0 _ _ IN).
    specialize (H1 _ _ IN).
    rewrite <- STree.keys_get_mem_false_iff in H0.
    rewrite <- STree.keys_get_mem_false_iff in H1.
    unfold get_env. rewrite H0. rewrite H1. constructor.
  - unfold get_env.
    rewrite get_lenv_of_record by auto.
    unfold get_env in H4.
    rewrite H4.
    apply less_def_refl.
Qed.



Definition match_venv (ty:typ) (ge:genv) (le1:lenv) (v: eval_typ tabs ty) (v_le:eval_typ tabs ty * lenv) : Prop :=
  v = fst v_le /\ match_env tabs ge le1 ge (snd v_le).

Lemma match_on_wf_atoms : forall ge le1 le2 l,
    forallb (wf_atom (STree.keys ge) (STree.keys le1)) l = true ->
    match_env tabs ge le1 ge le2 ->
  match_on tabs (BSet.union_list AtomOrdered.has_var l) ge le1 ge le2.
Proof.
  induction l; simpl.
  - intros. apply match_on_bot.
  - intros. rewrite match_on_union.
    rewrite andb_true_iff in H.
    destruct H; split; auto.
    eapply wf_atom_match_on; eauto.
Qed.


Lemma eval_match_ok : forall
    (WF : genv -> lenv -> expr -> bool)
    (MATCH : genv -> lenv -> genv -> lenv -> Prop)
    (P     : forall (ty: typ), genv -> lenv -> eval_typ tabs ty -> eval_typ tabs ty* lenv -> Prop)
    (l : list (Benum.pattern * expr))
    (transl_expr_correct_ok :
      forall (p: Benum.pattern) (e : expr) (te : Typing.tenv)
             (ge le1 : STree.t (value tabs)) (le2 : lenv)
             (ty : typ) (tc : tailcomp),
        In (p,e) l ->
        WF ge le1 e = true ->
        MATCH ge le1 ge le2 ->
        transl_expr e = OK tc ->
        option_rel (P ty ge le1)
          (eval_expr_rec tabs te ge le1 ty e)
          (eval_tailcomp_rec tabs te ge le2 ty tc))
    te t0 v
    (ge : genv) (le1 le2:lenv)
    l' ty
    (WF_EXPR :
    forallb
      (fun '(_, ei) => WF ge le1 ei) l =
    true)
    (M : MATCH ge le1 ge le2)
    (EQ : MapList.map_err transl_expr l = OK l'),
  option_rel (P ty ge le1)
    (eval_match tabs t0 v
       (MapList.map (eval_expr_rec tabs te ge le1 ty) l))
    (eval_match tabs t0 v
       (MapList.map (eval_tailcomp_rec tabs te ge le2 ty) l')).
Proof.
  unfold eval_match.
  destruct t0; try constructor.
  induction l; simpl.
  - intros. inv EQ.
    simpl. constructor.
  - intros.
    Res.monadInv EQ.
    destruct a; simpl in EQ0.
    Res.monadInv EQ0.
    inv EQ2.
    simpl.
    rewrite andb_true_iff in WF_EXPR.
    destruct WF_EXPR as (WF1 & WF2).
    destruct p.
    + eapply option_rel_bind_equal; intros.
      destruct (Benum.enum_eq a v); auto.
      eapply transl_expr_correct_ok; eauto.
      left. reflexivity.
      eapply IHl; eauto.
      intros. eapply transl_expr_correct_ok; eauto.
      simpl. right. eauto.
    + eapply transl_expr_correct_ok; eauto.
      left. reflexivity.
Qed.


Lemma transl_let_ok :
forall
    (WF : genv -> lenv -> expr -> bool)
    (MATCH : genv -> lenv -> genv -> lenv -> Prop)
    (P     : forall (ty: typ), genv -> lenv -> eval_typ tabs ty -> eval_typ tabs ty* lenv -> Prop)
    (transl_expr_correct_ok :
      forall (e : expr) (te : Typing.tenv)
             (ge le1 : STree.t (value tabs)) (le2 : lenv)
             (ty : typ) (tc : tailcomp),
        WF ge le1 e = true ->
        MATCH ge le1 ge le2 ->
        transl_expr e = OK tc ->
        option_rel (P ty ge le1)
          (eval_expr_rec tabs te ge le1 ty e)
          (eval_tailcomp_rec tabs te ge le2 ty tc)),
forall (MUP : forall ge1 le1 ge2 le2 x v1,
           MATCH ge1 le1 ge2 le2 ->
           MATCH ge1 (lenv_update tabs le1 x v1) ge2 (lenv_update tabs le2 x v1)),
forall te t1 ty ge le1 v1 v2_le2 x e2 tc2
       (WFUP : WF ge (lenv_update tabs le1 x (Val tabs t1 v1)) e2 = true),
    P t1 ge le1 v1 v2_le2 ->
    (P t1 ge le1 v1 v2_le2 -> v1 = fst v2_le2) ->
    (P t1 ge le1 (fst v2_le2) v2_le2 -> MATCH ge le1 ge (snd v2_le2)) ->
    forall (PUP : forall v0 v v_le2, P ty ge (lenv_update tabs le1 x v0) v v_le2 ->
                       P ty ge le1 v v_le2),
    transl_expr e2 = OK tc2 ->
    option_rel (P ty ge le1)
      (eval_expr_rec tabs te ge (lenv_update tabs le1 x (Val tabs t1 v1))
         ty e2)
      (eval_tailcomp_rec tabs te ge
         (lenv_update tabs (snd v2_le2) x (Val tabs t1 (fst v2_le2))) ty tc2).
Proof.
  intros.
  eapply option_rel_weaken.
  eapply transl_expr_correct_ok; auto.
  specialize (H0 H).
  subst.
  apply MUP. apply H1; auto.
  intros.
  eapply PUP; eauto.
Defined.

Lemma match_on_wf_atoms_snd : forall l ge le1 le2
    (WF_EXPR : forallb (fun x : ident * atom => wf_atom (STree.keys ge) (STree.keys le1) (snd x)) l = true)
    (MATCH : match_env tabs ge le1 ge le2),
  match_on tabs (BSet.union_list (fun x : string * atom => AtomOrdered.has_var (snd x)) l) ge le1 ge le2.
Proof.
  intros.
  eapply match_on_le.
  eapply match_on_wf_atoms with (l:= map snd l); eauto.
  rewrite forallb_forall in *; intros.
  rewrite in_map_iff in H.
  destruct H as ((id,a) & EQ  & IN).
  apply WF_EXPR in IN.
  simpl in *; congruence.
  apply BSet.subset_union_list.
  reflexivity.
Qed.

Lemma wf_init_indep_bindings : forall  l,
    wf_init_syntax  l  = true ->
  ForallP
    (fun x_e : ident * expr =>
     BSet.is_empty
       (BSet.inter (has_var (snd x_e)) (bset_of_bindings l)))
    l.
Proof.
  unfold wf_init_syntax.
  intro.
  generalize (bset_of_bindings_eq l).
  generalize (bset_of_bindings l) as bs1.
  generalize (sset_of_bindings l) as ss2.
  unfold wf_init_for_binders.
  induction l; simpl; auto.
  intros.
  rewrite andb_true_iff in H0.
  unfold wf_binding_syntax in H0.
  destruct H0.
  split; intros.
  - rewrite SSet.bset_is_empty in H0.
    revert H0.
    eapply BSet.is_empty_morph.
    intros.
    rewrite SSet.bset_inter.
    unfold BSet.inter.
    f_equal.
    rewrite has_var_eq. reflexivity.
    auto.
  - eapply IHl;eauto.
Qed.

Lemma get_update_seq_lenv :
  forall te ge init le1 le1'
         (UP : update_seq_lenv tabs (eval_expr_rec tabs te ge) te init le1 =
                 Some le1')
         (DUP : MapList.nodup string_dec init = true),
  forall k,
    (MapList.mem string_dec k init = false ->
     lenv_get tabs  le1' k =  lenv_get tabs le1 k)
    /\
      forall e, (In (k,e) init ->
                 exists ty, typof_expr te e = Some ty /\
                              exists (v : eval_typ tabs ty),
                                lenv_get tabs le1' k = Some (Val tabs ty v)).
Proof.
  induction init; simpl.
  - intros. inv UP. split; tauto.
  - intros.
    destruct a as (k1,k1e).
    monadInv UP. simpl in *.
    destruct (MapList.mem string_dec k1 init) eqn:MEM in DUP; try discriminate.
    split; intros.
    + destruct (string_dec k1 k); subst.
      * congruence.
      * eapply IHinit with (k:= k) in EQ2; auto.
        destruct EQ2.
        rewrite H0 by auto.
        unfold lenv_get,lenv_update.
        rewrite STree.gso by congruence.
        reflexivity.
    + destruct H.
      * inv H.
        apply IHinit with (k:= k) in EQ2.
        destruct EQ2.
        apply H in MEM.
        unfold lenv_get,lenv_update in MEM.
        rewrite STree.gss in MEM.
        eexists ; split; eauto.
        auto.
      * apply IHinit with (k:= k) in EQ2; auto.
        destruct EQ2.
        apply H1; auto.
Qed.


Lemma get_update_seq_lenv_in :
  forall te ge init le1 le1'
         (UP : update_seq_lenv tabs (eval_expr_rec tabs te ge) te init le1 =
                 Some le1')
         (DUP : MapList.nodup string_dec init = true),
  forall k e, In (k,e) init ->
              exists ty, typof_expr te e = Some ty /\
                           exists (v : eval_typ tabs ty),
                             lenv_get tabs le1' k = Some (Val tabs ty v).
Proof.
  intros.
  specialize (get_update_seq_lenv te ge init le1 le1' UP DUP k).
  intros.
  destruct H0 as (_ & H0).
  apply H0;auto.
Qed.


Lemma record_of_lenv_update_seq_lenv :
  forall te ge init rt le1 le1'
         (UP : update_seq_lenv tabs (eval_expr_rec tabs te ge) te init le1 =
                 Some le1')
         (DUP : MapList.nodup string_dec init = true)
         (TYP : MapList.mmap _  (typof_expr te) init = Some rt),
    exists r, record_of_lenv tabs ge rt le1' = Some r.
Proof.
  intros.
  specialize (get_update_seq_lenv_in te ge init le1 le1' UP DUP).
  clear UP DUP.
  revert rt TYP.
  induction init.
  - simpl. intros. inv TYP. simpl. eexists. reflexivity.
  - intros.
    simpl in TYP.
    monadInv TYP.
    monadInv EQ.
    apply IHinit in EQ1.
    destruct EQ1 as (r1 & EVAL).
    simpl.
    simpl in H.
    destruct a as (k1,e1).
    specialize (H k1 e1  (or_introl eq_refl)).
    destruct H as (ty & TY & (v & GET)).
    unfold get_env.
    simpl. unfold lenv_get in GET.
    rewrite GET.
    simpl.
    simpl in EQ0. assert (x1 = ty) by congruence ; subst.
    rewrite cast_typ_id.
    simpl.
    eexists.
    rewrite EVAL.
    reflexivity.
    intros.
    apply H.
    simpl; tauto.
Qed.

Lemma option_rel_bind_trans : forall
    {A1 A2 A3 B1 B2} (R: B1 -> B2 -> Prop)  (X1': option A3) (X1: option A1)
    (X2:option A2) F1 Y1 Y1' Y2,
    option_rel (fun r le => F1 r = le) X1 X1' ->
    forall (EQ: forall x, option_rel eq (Y1' (F1 x)) (Y1 x)),
    option_rel R (let* x := X1' in Y1' x)%option_monad (let* x := X2 in Y2 x)%option_monad ->
    option_rel R (let* x := X1 in Y1 x)%option_monad (let* x := X2 in Y2 x)%option_monad.
Proof.
  intros.
  inv H.
  - simpl in *; auto.
  - simpl in H0.
    specialize (EQ x).
    apply option_rel_eq_eq in EQ. rewrite EQ in H0.
    simpl; auto.
Qed.

Lemma update_seq_lenv_mmap :
  forall te ge init le1 leinit rt
         (UP:update_seq_lenv tabs (eval_expr_rec tabs te ge) te init le1 =  Some leinit)
         (MMAP: MapList.mmap _ (typof_expr te) init = Some rt),
  forall (x : StringIndexed.t) (v : typ),
    In (x, v) rt -> SSet.mem x (STree.keys leinit) = true.
Proof.
  intros.
  apply update_seq_lenv_keys with (x:=x) in UP.
  rewrite UP.
  rewrite orb_true_iff.
  right.
  apply MapList.mmap_In  with (vr:=x) (v:=v) in MMAP; auto.
  destruct MMAP as (v1 & IN & EQ).
  eapply MapList.in_mem;eauto.
Qed.


Lemma match_env_update_seq_lenv :
  forall te (ge:genv) init le1  leinit
         (WF: wf_init (STree.keys ge) (wf_expr (STree.keys ge)) (STree.keys le1) init = true)
         (UP : update_seq_lenv tabs (eval_expr_rec tabs te ge) te init le1 =
                 Some leinit),
    match_env tabs ge le1 ge leinit.
Proof.
  induction init ; simpl.
  - intros. inv UP. apply match_env_refl.
  - intros.
    monadInv UP.
    unfold wf_binding in WF.
    rewrite! andb_true_iff in WF.
    rewrite! negb_true_iff in WF.
    apply IHinit in EQ2.
    eapply match_env_trans;eauto.
    eapply match_env_update1.
    rewrite STree.keys_get_mem_false_iff. tauto.
    rewrite STree.keys_get_mem_false_iff. tauto.
    rewrite keys_lenv_update. tauto.
Qed.


Lemma record_of_lenv_match_env_less_def :
  forall ge leinit leinit' rt
         (MATCH : match_env tabs ge leinit ge leinit'),
    less_def
      (record_of_lenv tabs ge rt leinit)
      (record_of_lenv tabs ge rt leinit').
Proof.
  induction rt; simpl.
  - intros. constructor.
  - intros.
    eapply less_def_bind_less_def.
    apply MATCH.
    intros.
    eapply less_def_bind_eq.
    intros.
    eapply less_def_bind_less_def.
    apply IHrt; auto.
    constructor.
Qed.

Lemma transl_expr_correct_ok e:
    forall te ge le1 le2 ty tc
      (WF_EXPR: wf_expr (STree.keys ge) (STree.keys le1) e = true)
      (MATCH_LENV: match_env tabs ge le1 ge le2)
      (TRANSL: transl_expr e = OK tc),
      option_rel  (match_venv ty ge le1)
      (BarocqBNF.eval_expr_rec tabs te ge le1 ty e)
      (ImpBNF.eval_tailcomp_rec tabs te ge le2 ty tc).
  Proof.
    induction e using expr_depth_ind; intros.
    (* atom *)
    - inv TRANSL. simpl.
      eapply option_rel_bind_rel with (RA:=eq).
      apply option_rel_refl. auto.
      intros ; subst.
      apply option_rel_intro_bind.
      eapply option_rel_bind_rel with (RA:=eq).
      eapply option_rel_ecast_typ.
      eapply eval_atom_match_on.
      eapply wf_atom_match_on;eauto.
      { intros. subst.
        constructor. split;auto.
      }
    (* array set *)
    - inv TRANSL.
      rewrite eval_expr_rec_eq.
      simpl.
      simpl in WF_EXPR; rewrite! andb_true_iff in WF_EXPR.
      eapply option_rel_bind_rel with (RA:=eq).
      apply option_rel_refl. auto.
      intros ; subst.
      apply option_rel_intro_bind.
      eapply option_rel_bind_rel with (RA:=eq).
      eapply option_rel_ecast_typ.
      repeat (apply option_rel_bind_equal;intros).
      eapply option_rel_bind_rel.
      eapply eval_atom_match_on.
      { eapply wf_atom_match_on;eauto.
        tauto.
      }
      intros. subst.
      eapply option_rel_bind_rel.
      eapply eval_atom_match_on.
      { eapply wf_atom_match_on;eauto.
        tauto.
      }
      intros. subst.
      eapply option_rel_bind_rel.
      eapply eval_atom_match_on.
      { eapply wf_atom_match_on;eauto.
        tauto.
      }
      intros; subst.
      apply option_rel_refl; auto.
      { intros; constructor.
        split;auto.
      }
    (* record update *)
    - inv TRANSL.
      rewrite eval_expr_rec_eq.
      simpl.
      simpl in WF_EXPR; rewrite! andb_true_iff in WF_EXPR.
      eapply option_rel_bind_rel with (RA:=eq).
      apply option_rel_refl. auto.
      intros ; subst.
      apply option_rel_intro_bind.
      eapply option_rel_bind_rel with (RA:=eq).
      eapply option_rel_ecast_typ.
      repeat (apply option_rel_bind_equal;intros).
      eapply option_rel_bind_rel.
      eapply eval_atom_match_on.
      { eapply wf_atom_match_on;eauto.
        tauto.
      }
      intros. subst.
      eapply option_rel_bind_rel.
      eapply eval_atom_match_on.
      { eapply wf_atom_match_on;eauto.
        tauto.
      }
      intros. subst.
      apply option_rel_refl; auto.
      { intros; constructor.
        split;auto.
      }
    (* application *)
    - destruct f; try discriminate.
      simpl in TRANSL. inv TRANSL.
      rewrite eval_expr_rec_eq.
      simpl.
      simpl in WF_EXPR; rewrite! andb_true_iff in WF_EXPR.
      eapply option_rel_bind_rel with (RA:=eq).
      apply option_rel_refl. auto.
      intros ; subst.
      apply option_rel_intro_bind.
      eapply option_rel_bind_rel with (RA:=eq).
      eapply option_rel_ecast_typ.
      repeat (apply option_rel_bind_equal;intros).
      destruct a; try constructor;auto.
      eapply option_rel_bind_rel.
      { eapply eval_var_same with (ty:= TFun l a); eauto.
        tauto.
      }
      intros.
      eapply option_rel_bind_rel with (RA:=eq).
      apply option_rel_map2_eval_atoms.
      eapply match_on_wf_atoms;eauto.
      tauto.
      intros; subst.
      apply option_rel_refl;auto.
      intros; subst.
      constructor; split; auto.
    - (* act record *)
      inv TRANSL.
      unfold eval_expr_rec.
      destruct ty; try constructor.
      destruct o; try constructor.
      unfold eval_tailcomp_rec.
      apply option_rel_bind_equal.
      intros. destruct (typ_eqb (TRecord None l0) a); try constructor.
      eapply option_rel_intro_bind.
      eapply option_rel_bind_rel with (RA:=eq).
      simpl in WF_EXPR.
      apply option_rel_eval_act_record.
      {
        eapply match_on_wf_atoms_snd; eauto.
      }
      intros. subst.
      constructor. split; auto.
    (* if-then-else *)
    - Res.monadInv TRANSL.
      inv EQ2. simpl.
      simpl in WF_EXPR.
      rewrite! andb_true_iff in WF_EXPR.
      eapply option_rel_bind_rel.
      eapply eval_atom_match_on with (ty:=TBool);eauto.
      eapply wf_atom_match_on; eauto. tauto.
      intros; subst.
      destruct y.
      eapply IHe1; eauto.
      tauto.
      eapply IHe2; eauto.
      tauto.
    (* match-with *)
    - Res.monadInv TRANSL. inv EQ0.
      simpl in *.
      rewrite andb_true_iff in WF_EXPR.
      eapply option_rel_bind_equal; intros.
      eapply option_rel_bind_rel.
      eapply eval_atom_match_on.
      eapply wf_atom_match_on;tauto.
      intros; subst.
      destruct WF_EXPR as (_ & WF_EXPR).
      eapply eval_match_ok.
      { intros; eapply H; eauto. apply H4. }
      apply WF_EXPR.
      auto.
      auto.
    (* let-in *)
    - Res.monadInv TRANSL. inv EQ2. simpl.
      eapply option_rel_bind_rel with (RA:=eq).
      apply transl_expr_preserve_typ with (te:=te) in EQ.
      rewrite EQ. apply option_rel_refl;auto.
      simpl in WF_EXPR.
      rewrite! andb_true_iff in WF_EXPR.
      repeat rewrite negb_true_iff in WF_EXPR.
      intros; subst.
      rewrite bind2_bind.
      unfold uncurry.
      eapply option_rel_bind_rel.
      eapply IHe1; auto.
      { tauto. }
      intros.
      eapply option_rel_weaken.
      eapply IHe2.
      rewrite keys_lenv_update.
      tauto.
      destruct H. subst.
      apply match_env_update. auto.
      auto.
      intros.
      destruct H6 ; split; auto.
      { repeat intro.
        specialize (H7 x3).
        unfold get_env at 1.
        unfold get_env at 1 in H7.
        unfold lenv_update in H7.
        rewrite STree.gsspec in H7.
        destruct (STree.elt_eq x3 x).
        + subst.
          destruct (STree.get x le1) eqn:GET.
          apply STree.keys_get_some_mem in GET.
          intuition congruence.
          destruct (STree.get x ge) eqn:GET2.
          apply STree.keys_get_some_mem in GET2.
          intuition congruence.
          constructor.
        + auto.
      }
    - (* while *)
      Res.monadInv TRANSL.
      inv EQ3.
      simpl.
      (** parallel -> sequential *)
      assert (SEQ : update_para_lenv tabs (eval_expr_rec tabs te ge) te le1 init le1 =
    update_seq_lenv tabs (eval_expr_rec tabs te ge) te init le1).
      {
        apply option_rel_eq_eq.
        apply update_para_seq_wf.
        apply wf_init_indep_bindings; auto.
        simpl in WF_EXPR.
        rewrite! andb_true_iff in WF_EXPR.
        tauto.
      }
      rewrite SEQ. clear SEQ.
      rename e1 into body.
      rename x into init'.
      rename x1 into e2'.
      rename x0 into body'.
      eapply option_rel_bind_rel with
        (RA := (fun le1 le2 => match_env tabs ge le1 ge le2)).
      {
        clear IHe2. clear IHe1.
        revert EQ MATCH_LENV.
        simpl in WF_EXPR.
        rewrite !andb_true_iff in WF_EXPR.
        destruct WF_EXPR as ((_ & WFI) & _).
        revert WFI.
        revert init' le1 le2.
        induction init.
        - simpl. intros. inv EQ.
          simpl. constructor. auto.
        - simpl.
          intros.
          Res.monadInv EQ.
          destruct a as (id,eid).
          Res.monadInv EQ2.
          inv EQ4.
          simpl.
          rewrite transl_expr_preserve_typ with (e:=eid) (te:=te).
          eapply option_rel_bind_equal.
          intros.
          unfold wf_binding in WFI.
          rewrite !andb_true_iff in WFI.
          eapply option_rel_bind_rel.
          apply H with (x:= id); eauto.
          simpl; left ; reflexivity.
          tauto.
          intros. destruct y.
          unfold match_venv in H1.
          simpl in H1 ; destruct H1; subst.
          apply IHinit; auto.
          intros. apply H with (x:=x); auto.
          simpl ; tauto.
          rewrite keys_lenv_update.
          tauto.
          apply match_env_update; auto.
          auto.
      }
      intros.
      rename x into leinit.
      rename y into leinit'.
      (* Evaluation of variant *)
      eapply option_rel_bind_equal.
      intros.
      eapply option_rel_bind_rel with (RA:=eq).
      apply eval_atom_match_on.
      eapply wf_atom_match_on; eauto.
      simpl in WF_EXPR.
      rewrite! andb_true_iff in WF_EXPR.
      apply update_seq_lenv_keys_eq in H1.
      rewrite H1. tauto.
      intros; subst.
      eapply option_rel_bind_equal.
      intros.
      eapply option_rel_bind_rel with (RA:=eq).
      { rewrite option_rel_eq_eq.
        apply transl_expr_same_typ; auto. }
      intros. subst.
      rename y into vfuel.
      rename a0 into fuel.
      rename y0 into rt.
      assert (INIT : exists r, record_of_lenv tabs ge rt leinit = Some r).
      {
        eapply record_of_lenv_update_seq_lenv; eauto.
        simpl in WF_EXPR.
        rewrite! andb_true_iff in WF_EXPR.
        intuition idtac;
        eapply wf_init_no_dup; eauto.
      }
      destruct INIT as (rinit & INIT).
      rewrite INIT.
      simpl.
      (** Synchronise the loop *)
      assert (MEM : forall (x : StringIndexed.t) (v : typ),
                 In (x, v) rt -> SSet.mem x (STree.keys leinit) = true).
      {
        eapply update_seq_lenv_mmap; eauto.
      }
      pose proof (alternate_while tabs te ge rt fuel rinit leinit cond body) as W2.
      rewrite lenv_of_record_of_lenv with (ge:=ge) in W2;auto.
      eapply option_rel_bind_trans with (Y1':= fun x => eval_expr_rec tabs te ge x ty e2).
      eapply W2.
      intro. apply option_rel_refl. auto.
      clear W2.
      (** WF *)
      assert (Mle1 : match_env tabs ge le1 ge leinit).
      {
        eapply match_env_update_seq_lenv in H1; auto.
        simpl in WF_EXPR.
        rewrite! andb_true_iff in WF_EXPR.
        tauto.
      }
      assert (RLENV : record_of_lenv tabs ge rt leinit' = Some rinit).
      {
        assert (RINITLD := record_of_lenv_match_env_less_def ge leinit leinit' rt H0).
        rewrite INIT in RINITLD. inv RINITLD. inv H11.
        rewrite <- H10. reflexivity.
      }
      rewrite RLENV. unfold bind at 3.
      eapply option_rel_bind_rel with
        (RA:= fun le1' le2' =>
                STree.keys le1' = STree.keys leinit /\
                  match_env tabs ge le1 ge le1' /\
                  match_env tabs ge le1' ge le2').
      apply While.while_rel.
      { repeat split; auto.
      }
      { (* eval cond *)
        intros i1 i2 (M1 & M2 & M3).
        eapply option_rel_eq_eq.
        eapply eval_atom_match_on with (ty:= TBool).
        eapply wf_atom_match_on; eauto.
        rewrite M1.
        simpl in WF_EXPR.
        rewrite! andb_true_iff in WF_EXPR.
        apply update_seq_lenv_keys_eq in H1.
        rewrite H1. tauto.
      }
      {
        (* eval body *)
        intros i1 i2 (M1 & M2 & M3).
        eapply option_rel_bind_rel.
        { eapply IHe1; eauto.
          rewrite M1.
          apply update_seq_lenv_keys_eq in H1.
          rewrite H1.
          simpl in WF_EXPR.
          rewrite! andb_true_iff in WF_EXPR.
          tauto.
        }
        intros vbody vbody' M EB EB'.
        destruct vbody' as (vbody' & leb).
        constructor.
        repeat split.
        - rewrite BarocqBNF.keys_lenv_of_record_same; auto.
          intros. rewrite M1. eapply MEM ;eauto.
        - unfold match_venv in M.
          simpl in M. destruct M; subst.
          eapply match_env_new_keys;eauto.
          + intros.
          destruct (SSet.mem x (STree.keys le1)) eqn:MLE1;auto.
          eapply MapList.mmap_In in H8; eauto.
          destruct H8 as (ex & IN & _).
          apply wf_init_mem1 with (globs := STree.keys ge)
                                 (wf_expr := wf_expr (STree.keys ge))
                                 (l:=init) in MLE1.
          apply MapList.in_mem  with (key_eq := string_dec) in IN.
          congruence.
          simpl in WF_EXPR. rewrite! andb_true_iff in WF_EXPR.
          tauto.
          + intros.
          destruct (SSet.mem x (STree.keys ge)) eqn:MLE1;auto.
          eapply MapList.mmap_In in H8; eauto.
          destruct H8 as (ex & IN & _).
          apply wf_init_mem2 with (locals := STree.keys le1)
                                 (wf_expr := wf_expr (STree.keys ge))
                                 (l:=init) in MLE1.
          apply MapList.in_mem  with (key_eq := string_dec) in IN.
          congruence.
          simpl in WF_EXPR. rewrite! andb_true_iff in WF_EXPR.
          tauto.
        - unfold match_venv in M.
          simpl in M. destruct M ; subst.
          apply match_env_lenv_of_record; auto.
      }
      intros whiler whiler' (K & M1 & M2).
      intros.
      eapply option_rel_weaken.
      eapply IHe2; eauto.
      { (* wf e2 *)
        rewrite K.
        apply update_seq_lenv_keys_eq in H1.
        rewrite H1.
        simpl in WF_EXPR.
        rewrite! andb_true_iff in WF_EXPR.
        tauto.
      }
      { (* weakening *)
        intros.
        unfold match_venv in H13.
        destruct H13 ; subst.
        unfold match_venv. split ; auto.
        eapply match_env_trans.
        apply M1.
        auto.
      }
      clear W2.
      apply MapList.mmap_fst in H8.
      apply MapList.nodup_fst with (eq_dec:=string_dec) in H8.
      rewrite <- H8.
      simpl in WF_EXPR.
      rewrite! andb_true_iff in WF_EXPR.
      intuition idtac.
      eapply wf_init_no_dup; eauto.
    - (* attr *)
      Res.monadInv TRANSL. inv EQ0. simpl. eapply IHe; eauto.
  Qed.

  Ltac ecast_typ_err_resolve :=
    try (unfold ecast_typ; destruct (typ_eq_dec _ _); subst; simpl); eauto.

  Lemma transl_expr_correct:
    forall e te ge le1 le2 ty tc
    (WF_EXPR: wf_expr (STree.keys ge) (STree.keys le1) e = true)
    (MATCH_LENV: match_env tabs ge le1 ge le2)
    (TRANSL: transl_expr e = OK tc),
            BarocqBNF.eval_expr tabs te ge le1 ty e = ImpBNF.eval_tailcomp tabs te ge le2 ty tc.
  Proof.
    intros.
    unfold eval_tailcomp.
    rewrite bind2_bind.
    unfold uncurry.
    apply option_rel_eq_eq.
    replace (eval_expr tabs te ge le1 ty e)
      with (bind (eval_expr tabs te ge le1 ty e) (fun x => Some x)).
    eapply option_rel_bind_rel.
    eapply transl_expr_correct_ok; auto.
    intros. unfold match_venv in H.
    destruct H ; subst. constructor. reflexivity.
    destruct (eval_expr tabs te ge le1 ty e); reflexivity.
  Qed.

(*
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
 *)

  Lemma transl_function_correct_aux:
    forall params  e tc te ge le tret
           (NODUP      : MapList.nodup string_dec params = true)
           (WF_EXPR: wf_expr (STree.keys ge) (SSet.union (STree.keys le) (sset_of_bindings params)) e = true)
           (TRANSL: transl_expr e = OK tc),
      (eval_fun_rec tabs  (eval_tailcomp tabs) te ge le params tret tc) =
        (eval_fun_rec tabs  (eval_expr tabs) te ge le params tret e).
  Proof.
    induction params; intros.
    - simpl. apply Axioms.functional_extensionality; intro.
      symmetry.
      apply transl_expr_correct; try tauto.
      simpl in WF_EXPR.
      rewrite SSet.union_empty in WF_EXPR. auto.
      apply match_env_refl.
    - destruct params.
      + simpl. apply Axioms.functional_extensionality; intros.
        (*simpl in CHECK_PARAMS. destruct a.
        destruct (STree.get s (STree.keys ge)) eqn:Egets_ge; try discriminate.
        destruct (SSet.mem s (STree.keys le)); try discriminate. *)
        symmetry.
        apply transl_expr_correct; auto.
        * rewrite keys_lenv_update.
          rewrite <- WF_EXPR.
          apply wf_expr_morph;eauto.
          intros.
          rewrite SSet.mem_add.
          rewrite SSet.mem_union.
          rewrite mem_sset_of_bindings.
          simpl. destruct a; simpl.
          destruct (string_dec x0 s); destruct (string_dec s x0); try congruence.
          rewrite orb_comm. reflexivity.
          rewrite orb_comm. reflexivity.
        *  apply match_env_refl.
      + (*simpl in CHECK_PARAMS. destruct a.
        destruct (STree.get s (STree.keys ge)) eqn:Egets_ge; try discriminate.
        destruct (SSet.mem s (STree.keys le)); try discriminate.
        simpl in CHECK_PARAMS. *)
        cbn.
        apply Axioms.functional_extensionality; intros.
        eapply IHparams; eauto; cbn.
        destruct p.
        { simpl in NODUP.
          destruct a. destruct (string_dec s s0); try discriminate.
          destruct (MapList.mem string_dec s0 params); try discriminate.
          auto.
        }
        rewrite <- WF_EXPR.
        apply wf_expr_morph.
        intros.
        change ((SSet.union_list (fun x1 : StringIndexed.t * typ => SSet.singleton (fst x1)) params))
                 with (sset_of_bindings params).
        rewrite! SSet.mem_union.
        rewrite keys_lenv_update.
        rewrite SSet.mem_add.
        rewrite! mem_sset_of_bindings.
        simpl. destruct a. simpl.
        destruct p; simpl.
        rewrite SSet.mem_singleton.
        destruct (string_dec x0 s) ;
          destruct (string_dec s x0); try congruence.
        simpl. rewrite orb_comm. reflexivity.
        destruct (string_dec s0 x0);auto.
  Qed.

  Lemma transl_function_correct:
    forall f f' te ge x
    (TRANSL: transl_function (STree.keys ge) f = OK f'),
    eval_def_fun tabs (eval_tailcomp tabs) te ge x f' =
    eval_def_fun tabs (eval_expr tabs) te ge x f.
  Proof.
    intros.
    apply option_rel_eq_eq.
    unfold transl_function, eval_def_fun, eval_fun in *.
    destruct f; simpl in TRANSL.
    destruct (wf_expr (STree.keys ge) (sset_of_bindings fn_params) fn_body) eqn:WF ; try discriminate.
    Res.monadInv TRANSL. destruct f'. inv EQ0.
    simpl.
    destruct (MapList.nodup Ident.eq_dec fn_params0) eqn:ND;auto.
    eapply option_rel_bind_equal.
    intros.
    eapply option_rel_bind_equal.
    intros.
    rewrite transl_function_correct_aux with (e:=fn_body); eauto.
    apply option_rel_eq_eq. reflexivity.
    { rewrite <-  ND.
      symmetry.
      apply MapList.nodup_fst.
      apply MapList.mmap_fst in H0; auto.
    }
    { rewrite <- WF.
      apply wf_expr_morph.
      intros.
      rewrite SSet.mem_union.
      rewrite SSet.mem_empty.
      rewrite! mem_sset_of_bindings.
      simpl.
      apply MapList.mem_fst.
      apply MapList.mmap_fst in H0; auto.
    }
    constructor.
  Qed.

  Lemma transl_globdef_correct:
    forall def def' te impl ge
    (TRANSL: transl_globdef (STree.keys ge) def = OK def'),
      eval_globdef tabs (eval_tailcomp tabs) te impl ge def' =
      eval_globdef tabs (eval_expr tabs) te impl ge def.
  Proof.
    intros. destruct def;
    simpl in TRANSL; inv TRANSL; try reflexivity.
    Res.monadInv H0. inv EQ0. simpl.
    apply transl_function_correct.
    exact EQ.
  Qed.

  Lemma eval_globdef_add_gid:
    forall (T: Type) eval_T te impl ge ge' def, 
      eval_globdef tabs (EXPR:=T) (eval_T tabs) te impl ge def = Some ge' ->
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
      eval_prog_rec tabs (eval_tailcomp tabs) te impl ge defs'=
      eval_prog_rec tabs (eval_expr tabs) te impl ge defs.
  Proof.
    unfold eval_prog_rec.
    induction defs; intros.
    - simpl in TRANSL. inv TRANSL. simpl. reflexivity.
    - simpl in TRANSL. Res.monadInv TRANSL. inv EQ2.
      rename a into d. rename x into d'. rename x0 into defs'.
      simpl. rewrite transl_globdef_correct with (def := d); try exact EQ.
      destruct (eval_globdef tabs  (eval_expr tabs) te impl ge d) as [ge' |]eqn:Ege.
      + apply IHdefs. apply eval_globdef_add_gid in Ege.
        rewrite Ege. exact EQ1.
      + destruct defs.
        * simpl in EQ1. inv EQ1. reflexivity.
        * simpl in EQ1. Res.monadInv EQ1. inv EQ3. reflexivity.
  Qed.


  Theorem transl_prog_correct:
    forall impl p p'
    (TRANSL: transl_program p = OK p'),
      ImpBNF.eval_prog tabs impl p' = 
      BarocqBNF.eval_prog tabs impl p.
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
