(**  Generation of verification conditions to prove equivalence between
     Shallow and Deep embedding. *)
Set Universe Polymorphism.
From Coq Require Import String List.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Target Denot ExtEqual Ident StateMonads Option Barray Brecord Types Barocq Maps2 MergeSort Utils.
From compcert Require Import Coqlib.
From Coq Require Import ZifyBool.

Open Scope string_scope.
Import Typed.

Local Open Scope option_monad_scope.

Definition ident_of_globdef (g : globdef) :=
  match g with
  | DefType id _ => id
  | DefConst id _ _ => id
  | DefFun id _ => id
  | DeclType id _ => id
  | DeclConst id _ => id
  | DeclFun id _ _  => id
  end.

Definition has_prop (g:globdef) :=
  match g with
  | DeclType _ _ | DefType _ _ => false
  | _  => true
  end.


Section S.
  Variable tabs : Maps.PMap.t Type.

  Local Notation "# X" := (Types.eval_typ tabs X) (at level 90).

  Polymorphic Definition propt : Type := string * value tabs.

  Definition has_property (ge : genv tabs) (p : propt) :=
    exists v', genv_get tabs ge (fst p) = Some v' /\ same_value tabs (snd p) v'.

  (** Prove that [eval_prog_rec] only updates the global environment.
      However, existing definitions are never  overwritten. *)

  Definition env_preserve_defs (ge1 ge2: genv tabs) :=
    forall k' v',
      ge1 ! k' = Some v' -> ge2 ! k' = Some v'.

  Lemma env_preserve_defs_refl : forall ge,
      env_preserve_defs ge ge.
  Proof.
    unfold env_preserve_defs;auto.
  Qed.

  Lemma env_preserve_defs_trans : forall ge1 ge2 ge3,
      env_preserve_defs ge1 ge2 ->
      env_preserve_defs ge2 ge3 ->
      env_preserve_defs ge1 ge3.
  Proof.
    unfold env_preserve_defs.
    intros ; auto.
  Qed.

  Lemma genv_update_preserve_defs : forall ge k v ge',
      genv_update tabs ge k v = Some ge' ->
      env_preserve_defs ge ge'.
  Proof.
    unfold env_preserve_defs,genv_update;intros.
    unfold genv_get in H.
    unfold STree.get in H.
    destruct (ge ! (StringIndexed.index k)) eqn:G; try discriminate.
    inv H. unfold STree.set.
    rewrite PTree.gsspec.
    destruct (peq k' (StringIndexed.index k)); subst; congruence.
  Qed.

  Lemma eval_decl_const_preserve_defs : forall te ge ge' x l ty,
      eval_def_const tabs te ge x l ty = Some ge' ->
      env_preserve_defs ge ge'.
  Proof.
    unfold eval_def_const.
    intros.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    destruct (eval_literal tabs te l); try discriminate.
    simpl in H.
    destruct (cast_value tabs v t); try discriminate.
    simpl in H.
    eapply genv_update_preserve_defs;eauto.
  Qed.

  Lemma eval_def_fun_preserve_defs : forall arch te ge x f ge',
      eval_def_fun arch tabs te ge x f = Some ge' ->
      env_preserve_defs ge ge'.
  Proof.
    unfold eval_def_fun.
    intros.
    destruct (mk_fun_value arch tabs te ge (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f)); try discriminate.
    simpl in H.
    eapply genv_update_preserve_defs;eauto.
  Qed.

  Lemma eval_prog_rec_preserve_defs :
    forall arch prog te ge  te' ge'
           (EVAL: eval_prog_rec arch tabs te ge prog = Some (te', ge')),
      env_preserve_defs ge ge'.
  Proof.
    induction prog.
    - simpl; intros. inv EVAL. apply env_preserve_defs_refl.
    - simpl; intros.
      destruct a.
      + destruct (eval_def_type te i t); try discriminate.
        simpl in EVAL.
        eapply IHprog in EVAL;eauto.
      + destruct (eval_def_const tabs te ge i l b) eqn:EQN; try discriminate.
        simpl in EVAL.
        eapply IHprog in EVAL;eauto.
        eapply eval_decl_const_preserve_defs in EQN; eauto.
        eapply env_preserve_defs_trans; eauto.
      +  destruct (eval_def_fun arch tabs te ge i f) eqn:EQN; try discriminate.
         simpl in EVAL.
         eapply IHprog in EVAL;eauto.
         eapply eval_def_fun_preserve_defs in EQN;eauto.
         eapply env_preserve_defs_trans;eauto.
      + eauto.
      + destruct (eval_decl_const tabs te ge i b); try discriminate.
        simpl in EVAL ; eauto.
      + destruct (eval_decl_fun tabs te ge i l b); try discriminate.
        simpl in EVAL; eauto.
  Qed.

  Lemma genv_update_gss : forall ge ge' id v,
      genv_update tabs ge id v = Some ge' ->
      ge' ! (StringIndexed.index id) = Some v.
  Proof.
    unfold genv_update; intros.
    unfold genv_get in H.
    unfold STree.get in H.
    destruct (ge ! (StringIndexed.index id)) eqn:G ; try discriminate.
    simpl in H. unfold STree.set in H.
    inv H. rewrite PTree.gss. reflexivity.
  Qed.

  Lemma genv_get_preserve_defs :
    forall arch prog te ge  te' ge' x v
           (EVAL: eval_prog_rec arch tabs te ge prog = Some (te', ge'))
           (GET : genv_get tabs ge x = Some v),
      genv_get tabs ge' x = Some v.
  Proof.
    intros.
    eapply eval_prog_rec_preserve_defs in EVAL.
    unfold genv_get in *.
    unfold STree.get in *.
    specialize (EVAL (StringIndexed.index x) v).
    destruct (ge ! (StringIndexed.index x)); try discriminate.
    inv GET.
    rewrite EVAL;auto.
  Qed.

  (* A consequence of the preservation of definitions
   is that existing properties are also preserved. *)

  Lemma eval_prog_rec_preserve_properties : forall arch te ge prog te' ge' props
                                                   (ALL : Forall (has_property ge) props),
      eval_prog_rec arch tabs te ge prog = Some (te', ge') ->
      Forall (has_property ge') props.
  Proof.
    intros.
    rewrite Forall_forall in *.
    intros.
    apply ALL in H0.
    unfold has_property in H0.
    destruct x as (id,v).
    simpl in H0. destruct v as (ty,vty).
    destruct H0 as (v' & GET & EQ).
    eexists. split.
    eapply genv_get_preserve_defs; eauto.
    auto.
  Qed.

  Lemma eval_prog_rec_preserve_app_properties : forall arch  p2  te' te'' ge' ge'' p1' p2',
      Forall (has_property ge') p1' ->
      eval_prog_rec arch tabs te' ge' p2 = Some (te'',ge'') ->
      Forall (has_property ge'') p2' ->
      Forall (has_property ge'') (p1' ++ p2').
  Proof.
    intros.
    rewrite Forall_app.
    split.
    eapply eval_prog_rec_preserve_properties; eauto.
    auto.
  Qed.


  (** Generation of proof obligations. *)



  Definition check_value (v: option (value tabs)) (ty:typ) (prop : value tabs) :=
    match v with
    | Some v' => match cast_value tabs v' ty with
               | Some v' => eq_value tabs prop ty v'
               |  _    => False
               end
    | _    => False
    end.

  Definition generate_const_obligation (te : Typing.tenv) (x:ident) (l:Syntax.literal) (ty:btyp)
    (prop : value tabs) : option Prop :=
    let* ty' := Typing.btyp_to_typ te ty in
    ret (check_value (eval_literal tabs te l) ty' prop).


  Definition get_prop (s:ident) (props : list propt) :=
    match props with
    | nil => fail
    | (s',p)::props' => if String.eqb s s' then
                          ret (p,props')
                        else fail
    end.


  Fixpoint vars_of_expr (vars : STree.t unit) (e:expr)  : STree.t unit :=
    match e with
    | ETrue  | EFalse  |EInt32 _ _ | EInt64 _ _ | EConstr _ _ _ => vars
    | EVar id _ => STree.set id tt vars
    | ECast e _ => vars_of_expr vars e
    | EUnaryOp _ e _ => vars_of_expr vars e
    | EBinaryOp _ e1 e2 _ | EArrayGet e1 e2 _ _ => vars_of_expr (vars_of_expr vars e1) e2
    | EArraySet e1 e2 e3 _ => vars_of_expr (vars_of_expr (vars_of_expr vars e1) e2) e3
    | ERecordProj e _ _ _ => vars_of_expr vars e
    | ERecordUpdate e1 _ e2 _ => vars_of_expr (vars_of_expr vars e1) e2
    | EApp e l _   => List.fold_left vars_of_expr l (vars_of_expr vars e)
    | EIfThenElse e1 e2 e3 _ => vars_of_expr (vars_of_expr (vars_of_expr vars e1) e2) e3
    | EMatch e1 cases _  =>
        MapList.fold_left (fun vars _ ep => vars_of_expr vars ep) cases (vars_of_expr vars e1)
    | ELetIn x e1 e2 _ => (* Ignore scopes - should remove x from e2 *)
        let vars_e2 :=
          match STree.get x vars with
          | Some _ => vars_of_expr vars e2
          | None   => STree.remove x (vars_of_expr vars e2)
          end in vars_of_expr vars_e2 e1
    | EAttr _ e => vars_of_expr vars e
    end.

  Definition has_var (s:string) (vars:STree.t unit) :=
    match STree.get s vars with
    | None => false
    | Some _ => true
    end.

  Fixpoint remove_params {A:Type}(l :smaplist A) (vars : STree.t unit) :=
    match l with
    | nil => vars
    | (p,_) ::l =>  remove_params l (STree.remove p vars)
    end.

  Fixpoint remove_params_r {A:Type}(l :smaplist A) (vars : STree.t unit) :=
    match l with
    | nil => vars
    | (p,_) ::l =>  STree.remove p (remove_params_r l  vars)
    end.

  Lemma remove_params_r_acc_None : forall {A: Type} (params:smaplist A) vars x,
      STree.get x vars = None ->
      STree.get x (remove_params_r params  vars) = None.
  Proof.
    induction params; simpl;auto.
    intros. destruct a.
    rewrite STree.grspec.
    destruct (STree.elt_eq x s); auto.
  Qed.

  Lemma remove_acc : forall {A: Type} (params:smaplist A) vars1 vars2 x
                            (ACC : STree.get x vars1 = STree.get x vars2),
      STree.get x (remove_params_r params  vars1) = STree.get x (remove_params_r params  vars2).
  Proof.
    induction params; simpl;auto.
    intros. destruct a.
    rewrite! STree.grspec.
    destruct (STree.elt_eq x s); auto.
  Qed.


  Lemma remove_params_r_comm : forall {A:Type} (p1 p2:smaplist A) vars x,
      STree.get x (remove_params_r p1 (remove_params_r p2 vars)) =   STree.get x (remove_params_r p2 (remove_params_r p1 vars)).
  Proof.
    induction p1; simpl;auto.
    intros.
    destruct a.
    rewrite STree.grspec.
    destruct (STree.elt_eq x s).
    rewrite remove_params_r_acc_None; auto.
    subst. rewrite STree.grs; auto.
    rewrite IHp1.
    apply remove_acc.
    rewrite STree.gro by auto.
    reflexivity.
  Qed.


  Lemma remove_params_eq : forall {A: Type} (params:smaplist A) vars,
    forall x, STree.get  x (remove_params params vars) =
                STree.get  x (remove_params_r params vars).
  Proof.
    induction params; simpl ; intros.
    - reflexivity.
    - destruct a.
      rewrite IHparams.
      change (STree.remove s vars) with (remove_params_r ((s,a)::nil) vars).
      rewrite remove_params_r_comm.
      simpl. reflexivity.
  Qed.

  Definition vars_of_fun {A:Type} (params : smaplist A) (e:expr) :=
    remove_params params (vars_of_expr STree.empty e).


  Definition generate_def_fun_obligation (arch:archi) (te:Typing.tenv)  (params : smaplist btyp) (tret : btyp) (e : expr) (checked : list propt)
    (prop : value tabs) : option Prop :=
    if MergeSort.nodup String.leb String.eqb (List.map fst params)
    then
      let* tret' := Typing.btyp_to_typ te tret in
      let* params' := map_err (Typing.btyp_to_typ te) params in
      let vars     := vars_of_fun params e in
      let needed_checked := List.filter (fun '(k,_) => has_var k vars) checked in
      let o := forall ge,
          Forall (has_property ge) needed_checked ->
          let v := (eval_fun arch tabs te ge params' tret' e) in
          eq_value tabs prop ((TFun (map (fun x : string * typ => snd x) params') tret')) v in
      ret o
    else fail.



  Fixpoint genv_has_property (ge: genv tabs)  (l:list propt) :=
    match l with
    | nil => ge
    | (k,p)::l' => genv_has_property (STree.set k p ge) l'
    end.

  Definition stree_equal {A B: Type} (s1: STree.t A) (s2: STree.t B) :=
    STree.beq (fun _ _ => true) (STree.map (fun _ _ => tt) s1)
      (STree.map (fun _ _ => tt) s2).

  Lemma stree_equal_sound : forall {A B: Type} (s1: STree.t A) (s2: STree.t B),
      stree_equal s1 s2 = true ->
      forall x, STree.get x s1 <> None <-> STree.get x s2 <> None.
  Proof.
    unfold stree_equal.
    intros.
    apply STree.beq_sound with (x:=x) in H.
    unfold STree.map in *.
    unfold STree.get in *.
    rewrite! PTree.gmap in *.
    destruct (s1 ! (StringIndexed.index x)) ;
      destruct (s2 ! (StringIndexed.index x)); try tauto.
    simpl in H. intuition congruence.
  Qed.


  Definition generate_def_fun_obligation' (arch:archi) (f:ident) (te:Typing.tenv)  (params : smaplist btyp) (tret : btyp) (e : expr) (checked : list propt)
    (prop : value tabs) : option Prop :=
    if MergeSort.nodup String.leb String.eqb (List.map fst params)
    then
      let* tret' := Typing.btyp_to_typ te tret in
      let* params' := map_err (Typing.btyp_to_typ te) params in
      let vars     := vars_of_fun params e in
      let needed_checked := List.filter (fun '(k,_) => has_var k vars) checked in
      let ge := genv_has_property STree.empty needed_checked in
      if stree_equal vars ge
      then
        let o :=
          let v := (eval_fun arch tabs te ge params' tret' e) in
          eq_value tabs prop ((TFun (map (fun x : string * typ => snd x) params') tret')) v in
        ret o
      else None
    else None.

  Definition eq_env (keys: STree.t unit) (le le': genv tabs) (ge ge' : genv tabs) :=
    forall x,
      STree.get x le   = None ->
      STree.get x le'   = None ->
      STree.get x keys = Some tt ->
      option_rel (same_value tabs) (STree.get x ge) (STree.get x ge').

  Definition eq_env_all (ge ge' : genv tabs) :=
    forall x,  option_rel (same_value tabs) (STree.get x ge) (STree.get x ge').

  Lemma eq_env_eq : forall vars le le' ge1 ge1' ge2 ge2',
      (forall x, STree.get x ge1 = STree.get x ge2) ->
      (forall x, STree.get x ge1' = STree.get x ge2') ->
      eq_env vars le le' ge1 ge1' ->
      eq_env vars le le' ge2 ge2'.
  Proof.
    unfold eq_env.
    intros;auto.
    rewrite <- H. rewrite <- H0.
    auto.
  Qed.





  Lemma res_rel_refl : forall {A : Type} (P : A -> A -> Prop),
      (forall x, P x x) ->
      forall x, option_rel P x x.
  Proof.
    intros.
    destruct x; constructor.
    apply H.
  Qed.

  Lemma get_cast_fo_typ : forall  ty t r,
      get_cast tabs ty t = Some r ->
      no_TFun ty = true /\ no_TFun t = true.
  Proof.
    unfold get_cast.
    destruct ty,t; try discriminate; simpl; split; reflexivity.
  Qed.



  Lemma ext_equal_eval_cast : forall ty x y t,
      ext_equal tabs ty x y ->
      option_rel (ext_equal tabs t) (eval_cast tabs ty x t) (eval_cast tabs ty y t).
  Proof.
    unfold eval_cast.
    intros.
    destruct (get_cast tabs ty t) eqn:C; try constructor.
    apply get_cast_fo_typ in C as (F1 & F2).
    simpl.
    apply no_TFun_equal in H; auto.
    subst.
    apply res_rel_refl. intros. apply ext_equal_refl.
    apply no_TFun_fo_typ; auto.
  Qed.

  Lemma res_rel_cast_typ_refl : forall ti tf v,
      fo_typ ti = true ->
      option_rel (ext_equal tabs tf) (@cast_typ tabs ti v tf) (@cast_typ tabs ti v tf).
  Proof.
    intros.
    unfold cast_typ.
    destruct (typ_eq_dec ti tf).
    subst. apply res_rel_refl.
    intros. apply ext_equal_refl. auto.
    constructor.
  Qed.


  Lemma ext_equal_eval_unary_op : forall op ti x y tf,
      ext_equal tabs ti x y ->
      option_rel (ext_equal tabs tf) (eval_unary_op tabs op ti x tf)
        (eval_unary_op tabs op ti y tf).
  Proof.
    intros.
    destruct op,ti; simpl; try constructor.
    apply ext_equal_cast_typ; simpl in *; congruence.
    apply ext_equal_cast_typ; simpl in *; congruence.
    apply ext_equal_cast_typ; simpl in *; congruence.
    apply ext_equal_cast_typ; simpl in *; congruence.
    apply ext_equal_cast_typ; simpl in *; congruence.
    apply ext_equal_cast_typ; simpl in *; congruence.
    apply ext_equal_cast_typ; simpl in *; congruence.
  Qed.




(*  Lemma equal_upd_record_aux :
    forall fields r1 r2 f ty v1 v2,
      equal_record ext_equal fields r1 r2 ->
      ext_equal ty v1 v2 ->
      res_rel (equal_record ext_equal fields) (eval_record_upd_aux tabs fields r1 f ty v1)
        (eval_record_upd_aux tabs fields r2 f ty v2).
  Proof.
    unfold eval_recordtyp.
    intros.
    unfold eval_record_upd_aux.
    {
      revert r1 r2 H.
      induction fields.
      - simpl.
        constructor.
      - simpl.
        intros.
        destruct a as(fd,ty1).
        destruct r1 as (f1 & r1').
        destruct r2 as (f2 & r2').
        simpl in f1,f2.
        simpl.
        destruct (f =?fd).
        destruct (typ_eq_dec ty ty1).
        + subst. constructor.
          simpl in *.
          tauto.
        + constructor.
        + simpl in *.
          destruct H as (FD & RST).
          specialize (IHfields r1' r2' RST).
          inv IHfields.
          constructor.
          simpl. constructor ;auto.
    }
  Qed.
*)


  Fixpoint get_var_of_expr_acc (x:string) (e:expr): forall acc,
      STree.get x acc = Some tt ->
      STree.get x (vars_of_expr acc e) = Some tt.
  Proof.
    destruct e; simpl; auto.
    - intros. rewrite STree.gsspec.
      destruct (STree.elt_eq x i); auto.
    (* - induction l; simpl; auto.
      intros.
      apply IHl.
      destruct a; simpl;auto. *)
    - intros.
      apply get_var_of_expr_acc with (e:=e) in H.
      revert H.
      generalize (vars_of_expr acc e) as acc'.
      induction l; simpl ; auto.
    - intros.
      apply get_var_of_expr_acc with (e:=e) in H.
      revert H.
      generalize (vars_of_expr acc e) as acc'.
      unfold MapList.fold_left.
      induction l; simpl ; auto.
      destruct a. intros.
      apply IHl.
      apply get_var_of_expr_acc. auto.
    - intros.
      destruct (STree.get i acc) eqn:GET.
      + rewrite get_var_of_expr_acc; auto.
      +  destruct (STree.elt_eq x i).
         congruence.
         apply get_var_of_expr_acc.
         rewrite STree.grspec.
         destruct (STree.elt_eq x i);try congruence.
         apply get_var_of_expr_acc;auto.
  Qed.


  Fixpoint get_var_of_expr_case (x:string) (e:expr): forall acc,
      STree.get x (vars_of_expr acc e) = Some tt <->
        (STree.get x acc = Some tt \/
           STree.get x (vars_of_expr STree.empty e) = Some tt).
  Proof.
    destruct e; simpl.
    - intros. rewrite STree.gempty.
      intuition congruence.
    - intros. rewrite STree.gempty.
      intuition congruence.
    - intros. rewrite STree.gempty.
      intuition congruence.
    - intros. rewrite STree.gempty.
      intuition congruence.
    - intros. rewrite STree.gempty.
      intuition congruence.
    - intros. rewrite! STree.gsspec.
      destruct (STree.elt_eq x i).
      tauto.
      rewrite STree.gempty. intuition congruence.
    - intros.
      rewrite get_var_of_expr_case.
      tauto.
    - intros.
      rewrite get_var_of_expr_case.
      tauto.
    - intros.
      rewrite get_var_of_expr_case.
      rewrite get_var_of_expr_case.
      rewrite (get_var_of_expr_case x e2 (vars_of_expr STree.empty e1)).
      tauto.
    - intros.
      rewrite get_var_of_expr_case.
      rewrite get_var_of_expr_case.
      rewrite (get_var_of_expr_case x e2 (vars_of_expr STree.empty e1)).
      tauto.
    - intros.
      rewrite get_var_of_expr_case.
      rewrite get_var_of_expr_case.
      symmetry.
      rewrite get_var_of_expr_case.
      rewrite get_var_of_expr_case.
      rewrite (get_var_of_expr_case x e1 acc).
      tauto.
    - auto.
    - intros.
      rewrite get_var_of_expr_case.
      rewrite get_var_of_expr_case.
      rewrite (get_var_of_expr_case x e2 (vars_of_expr STree.empty e1)).
      tauto.
    - intros.
      assert (forall acc',
                 STree.get x (fold_left vars_of_expr l acc') = Some tt <->
                   (STree.get x acc' = Some tt \/
                      STree.get x (fold_left vars_of_expr l STree.empty) = Some tt)).
      {
        induction l.
        - simpl. rewrite STree.gempty.
          intuition congruence.
        - simpl. intros.
          rewrite IHl.
          symmetry.
          rewrite IHl.
          rewrite (get_var_of_expr_case x a acc').
          tauto.
      }
      rewrite H.
      symmetry.
      rewrite H.
      rewrite (get_var_of_expr_case x e acc).
      tauto.
    - intros.
      rewrite get_var_of_expr_case.
      rewrite get_var_of_expr_case.
      rewrite get_var_of_expr_case.
      rewrite (get_var_of_expr_case x e3 ((vars_of_expr (vars_of_expr STree.empty e1) e2))).
      rewrite (get_var_of_expr_case x e2 (vars_of_expr STree.empty e1)).
      tauto.
    - unfold MapList.fold_left.
      set (F := (fun (a : STree.t unit) '(_, v) => vars_of_expr a v)).
      assert (forall acc', STree.get x (fold_left F l acc') = Some tt <->
                             STree.get x acc' = Some tt \/ STree.get x (fold_left F l STree.empty) = Some tt).
      {
        induction l; simpl ; auto.
        - intros. rewrite STree.gempty. intuition congruence.
        - intros. rewrite IHl.
          unfold F at 1.
          destruct a.
          rewrite get_var_of_expr_case.
          symmetry. rewrite IHl.
          unfold F at 1. tauto.
      }
      intros.
      rewrite H. symmetry.
      rewrite H.
      rewrite (get_var_of_expr_case x e acc).
      tauto.
    - intros.
      destruct (STree.get i acc) eqn:GET1.
      + destruct u.
        rewrite get_var_of_expr_case.
        rewrite get_var_of_expr_case.
        symmetry.
        rewrite get_var_of_expr_case.
        rewrite get_var_of_expr_case.
        rewrite STree.grspec.
        destruct (STree.elt_eq x i).
        { subst.
          rewrite STree.gempty.
          intuition congruence.
        }
        { intuition congruence.
        }
      +
        rewrite get_var_of_expr_case.
        rewrite STree.grspec.
        symmetry.
        rewrite get_var_of_expr_case.
        rewrite STree.grspec.
        destruct (STree.elt_eq x i).
        subst. intuition congruence.
        symmetry.
        rewrite get_var_of_expr_case.
        tauto.
    - apply get_var_of_expr_case.
  Qed.

  Definition eq_env_vars_of_expr_acc (e:expr) : forall acc le le' ge ge',
      eq_env (vars_of_expr acc e) le le' ge ge' ->
      eq_env acc le le' ge ge'.
  Proof.
    unfold eq_env.
    intros.
    apply H; auto.
    apply get_var_of_expr_acc; auto.
  Qed.

  Definition eq_env_vars_of_expr (e:expr) : forall acc le le' ge ge',
      eq_env (vars_of_expr acc e) le le' ge ge' ->
      eq_env (vars_of_expr STree.empty e) le le' ge ge'.
  Proof.
    unfold eq_env.
    intros.
    apply H; auto.
    rewrite get_var_of_expr_case.
    tauto.
  Qed.

  Lemma eq_env_split : forall (e:expr)  acc le le' ge ge',
      eq_env (vars_of_expr acc e) le le' ge ge' ->
      eq_env (vars_of_expr STree.empty e) le le' ge ge' /\
        eq_env acc le le' ge ge'.
  Proof.
    intros.
    split.
    eapply eq_env_vars_of_expr in H; auto.
    apply eq_env_vars_of_expr_acc in H;auto.
  Qed.

  Lemma get_fold_vars_of_expr : forall x args acc,
      STree.get x (fold_left vars_of_expr args acc) = Some tt <->
        (STree.get x (fold_left vars_of_expr args STree.empty) = Some tt \/
           STree.get x acc = Some tt).
  Proof.
    induction args ; simpl.
    -  intros. rewrite STree.gempty. intuition congruence.
    - intros.
      rewrite IHargs.
      rewrite get_var_of_expr_case.
      symmetry.
      rewrite IHargs.
      tauto.
  Qed.

  Lemma eq_env_exprs : forall args acc le le' ge ge',
      eq_env (fold_left vars_of_expr args acc) le le' ge ge' ->
      eq_env (fold_left vars_of_expr args STree.empty) le le' ge ge' /\
        eq_env acc le le' ge ge'.
  Proof.
    unfold eq_env; simpl; split; intros.
    apply H;auto.
    rewrite get_fold_vars_of_expr; tauto.
    apply H;auto.
    rewrite get_fold_vars_of_expr; tauto.
  Qed.

  Lemma vars_of_pattern : forall x cases acc,
      let F := (fun (vars : STree.t unit) (_ : Benum.pattern) (ep : expr) => vars_of_expr vars ep) in
      STree.get x (MapList.fold_left F cases acc) = Some tt <->
        (STree.get x (MapList.fold_left F cases STree.empty) = Some tt  \/ STree.get x acc = Some tt).
  Proof.
    induction cases ; simpl; auto.
    - intros. rewrite STree.gempty.
      intuition congruence.
    - intros.
      rewrite IHcases.
      destruct a. rewrite get_var_of_expr_case.
      symmetry. rewrite IHcases.
      tauto.
  Qed.


  Lemma eq_env_pattern : forall cases acc le le' ge ge',
      eq_env
        (MapList.fold_left (fun (vars : STree.t unit) (_ : Benum.pattern) (ep : expr) => vars_of_expr vars ep) cases
           acc) le le' ge ge' ->
      eq_env (MapList.fold_left (fun (vars : STree.t unit) (_ : Benum.pattern) (ep : expr) => vars_of_expr vars ep) cases STree.empty) le le' ge ge'
      /\
        eq_env acc le le' ge ge'.
  Proof.
    unfold eq_env. intros.
    split; intros.
    apply H;auto.
    rewrite vars_of_pattern. tauto.
    apply H;auto.
    rewrite vars_of_pattern. tauto.
  Qed.

  Lemma eq_env_all_lenv_update : forall le le' k ty v1 v2,
      eq_env_all le le' ->
      ext_equal tabs ty v1 v2 ->
      eq_env_all (lenv_update tabs le k (Val tabs ty v1))
        (lenv_update tabs le' k (Val tabs ty v2)).
  Proof.
    unfold eq_env_all,lenv_update.
    intros.
    rewrite! STree.gsspec.
    destruct (STree.elt_eq x k).
    constructor. apply ext_equal_same_value.
    apply ext_equal_sym. auto.
    apply H.
  Qed.



  Lemma eq_env_remove : forall x e le le' v1 v2 ge ge',
      eq_env (STree.remove x (vars_of_expr STree.empty e)) le le' ge ge' ->
      eq_env (vars_of_expr STree.empty e) (lenv_update tabs le x v1) (lenv_update tabs le' x v2) ge ge'.
  Proof.
    unfold eq_env;intros.
    unfold lenv_update in *.
    rewrite STree.gsspec in *.
    destruct (STree.elt_eq x0 x); try congruence.
    apply H; auto.
    rewrite STree.gro;auto.
  Qed.

  Fixpoint eq_genv_eval_expr (arch:archi) (te:Typing.tenv)  (ge ge':genv tabs) (ty:typ) (e:expr) : forall le le',
      eq_env (vars_of_expr (STree.empty) e) le le' ge ge' ->
      eq_env_all le le'  ->
      option_rel (ext_equal tabs ty) (eval_expr arch tabs te ge le ty e)
        (eval_expr arch tabs te ge' le' ty e).
  Proof.
    specialize (eq_genv_eval_expr arch te ge ge').
    destruct e; intros; simpl; try (apply res_rel_cast_typ_refl;reflexivity).
    - unfold eval_constr. destruct ty; simpl; try constructor.
      apply res_rel_refl; intro; reflexivity.
    - unfold eval_var.
      unfold lenv_get.
      unfold eq_env in H0.
      specialize (H0 i).
      inv H0.
      + rewrite <- H2. rewrite <- H3.
        simpl.
        unfold eq_env in H. unfold genv_get.
        simpl in H.
        specialize (H i).
        rewrite STree.gss in H.
        symmetry in H2. symmetry in H3.
        specialize (H H2 H3 eq_refl).
        inv H.
        * rewrite <- H1. rewrite <- H4.
          constructor.
        * rewrite <- H0. rewrite <- H1.
          simpl.
          apply same_value_cast_value; auto.
      + rewrite <- H1. rewrite <- H2.
        simpl. apply same_value_cast_value; auto.
    - destruct (Typing.btyp_to_typ te b); try reflexivity.
      simpl.
      destruct (Barocq.typof_expr te e); try constructor.
      simpl.
      specialize (eq_genv_eval_expr t0 e le le' H H0).
      inv eq_genv_eval_expr.
      constructor.
      simpl.
      eapply ext_equal_eval_cast with (t:=t)in H3;eauto.
      apply ext_equal_ecast_typ; auto.
      constructor.
    - destruct (Typing.btyp_to_typ te b); try constructor.
      simpl.
      specialize (eq_genv_eval_expr t e le le' H H0).
      inv eq_genv_eval_expr.
      constructor.
      simpl.
      apply ext_equal_eval_unary_op; auto.
    -
      simpl in H.
      destruct (Barocq.typof_expr te e1); try constructor.
      destruct (Barocq.typof_expr te e2); try constructor.
      simpl.
      generalize (eq_genv_eval_expr t e1 le le' (eq_env_vars_of_expr_acc _ _ _ _ _ _ H) H0).
      generalize (eq_genv_eval_expr t0 e2 le le' (eq_env_vars_of_expr _ _ _ _ _ _ H) H0).
      intros E2 E1.
      inv E1 ; try constructor.
      simpl. inv E2 ; try constructor.
      simpl.
      apply ext_equal_eval_binary_op; auto.
    - simpl in H.
      destruct (Barocq.typof_expr te e1); try constructor.
      destruct (Barocq.typof_expr te e2); try constructor.
      simpl.
      generalize (eq_genv_eval_expr t e1 le le' (eq_env_vars_of_expr_acc _ _ _ _ _ _ H) H0).
      generalize (eq_genv_eval_expr t0 e2 le le' (eq_env_vars_of_expr _ _ _ _ _ _ H) H0).
      intros E2 E1.
      inv E1 ; try constructor.
      simpl. inv E2 ; try constructor.
      simpl.
      apply ext_equal_array_get; auto.
    - simpl in H.
      apply eq_env_split in H.
      destruct H as (EQ1 & EQ2).
      apply eq_env_split in EQ2 as (EQ2 & EQ3).
      destruct (Barocq.typof_expr te e1); try constructor.
      destruct (Barocq.typof_expr te e2); try constructor.
      destruct (Barocq.typof_expr te e3); try constructor.
      simpl.
      generalize (eq_genv_eval_expr t e1 le le' EQ3 H0).
      generalize (eq_genv_eval_expr t0 e2 le le' EQ2 H0).
      generalize (eq_genv_eval_expr t1 e3 le le' EQ1 H0).
      intros E3 E2 E1.
      inv E1 ; try constructor.
      simpl. inv E2 ; try constructor.
      simpl. inv E3 ; try constructor.
      simpl.
      apply ext_equal_array_set; auto.
    -
      destruct (Barocq.typof_expr te e); try constructor.
      simpl.
      specialize (eq_genv_eval_expr t e le le' H H0).
      inv eq_genv_eval_expr; try constructor.
      simpl.
      apply ext_equal_eval_record_proj; auto.
    -
      simpl in H.
      apply eq_env_split in H as (EQ1 & EQ2).
      destruct (Barocq.typof_expr te e1);try constructor.
      destruct (Barocq.typof_expr te e2);try constructor.
      simpl.
      generalize (eq_genv_eval_expr t e1 le le' EQ2 H0).
      generalize (eq_genv_eval_expr t0 e2 le le' EQ1 H0).
      intros E2 E1.
      inv E1 ; try constructor.
      simpl. inv E2 ; try constructor.
      simpl.
      apply ext_equal_eval_record_update; auto.
    -
      simpl in H.
      destruct (Barocq.typof_expr te e); try constructor.
      simpl.
      apply eq_env_exprs in H as (EQ1 & EQ2).
      destruct t; try constructor.
      assert (E1 := eq_genv_eval_expr (TFun l0 t) e le le' EQ2  H0).
      inv E1.
      constructor.
      simpl.
      set (Ftyp := fun (ty:typ) => option (eval_typ tabs ty)).
      set (Pred := fun ty => option_rel (ext_equal tabs ty)).
      assert (option_rel (DList.Forall2 Ftyp Pred  _) (DList.map2 (eval_typ tabs) (eval_expr arch tabs te ge le) l l0)
                (DList.map2 (eval_typ tabs) (eval_expr arch tabs te ge' le') l l0)).
      {
        clear H2 H H1 x y.
        revert l0.
        induction l; destruct l0.
        - simpl. constructor. constructor.
        - simpl.
          constructor.
        - simpl. constructor.
        - simpl.
          simpl in EQ1.
          apply eq_env_exprs in EQ1 as (EQ1 & EQ1').
          specialize (eq_genv_eval_expr t0 a le le' EQ1' H0).
          specialize (IHl EQ1 l0).
          inv IHl.
          constructor.
          simpl. constructor.
          constructor ;auto.
      }
      set (l1 := (DList.map2 (eval_typ tabs)
         (eval_expr arch tabs te ge le) l l0)) in *.
      set (l1' := (DList.map2 (eval_typ tabs)
         (eval_expr arch tabs te ge' le') l l0)) in *.
      inv H3; try constructor.
      simpl.
      clear - H2 H6.
      apply ext_equal_eval_app_res; auto.
    - simpl in H.
      apply eq_env_split in H as (EQ1 & EQ2).
      apply eq_env_split in EQ2 as (EQ2 & EQ3).
      generalize (eq_genv_eval_expr TBool e1 _ _ EQ3 H0).
      intros E1 ; inv E1; try constructor.
      simpl.
      destruct (Barocq.typof_expr te e2); try constructor.
      destruct (Barocq.typof_expr te e3); try constructor.
      simpl.
      generalize (eq_genv_eval_expr t e2 _ _ EQ2 H0).
      generalize (eq_genv_eval_expr t0 e3 _ _ EQ1 H0).
      intros E3 E2.
      apply option_rel_ifthenelse; auto.
    - simpl in H.
      apply eq_env_pattern in H.
      destruct (Barocq.typof_expr te e); try constructor.
      destruct H as (EQ1 & EQ2).
      simpl.
      generalize (eq_genv_eval_expr t e _ _ EQ2 H0).
      intro E ; inv E; try constructor.
      simpl.
      apply ext_equal_eval_match; auto.
      revert EQ1.
      induction l.
      + simpl. constructor.
      + simpl.
        destruct a.
        intros.
        apply eq_env_pattern in EQ1.
        constructor.
        simpl. split;auto.
        apply eq_genv_eval_expr.
        destruct EQ1. auto.
        auto.
        apply IHl.
        tauto.
    - simpl in H.
      destruct (Barocq.typof_expr te e1); try constructor.
      simpl.
      apply eq_env_split in H as (EQ1 & EQ2).
      generalize (eq_genv_eval_expr t e1 le le' EQ1 H0).
      intro E1.
      inv E1.
      constructor.
      simpl.
      assert (LE : eq_env_all (lenv_update tabs le i (Val tabs t x))
                     (lenv_update tabs le' i (Val tabs t y))).
      {
        unfold lenv_update.
        unfold eq_env_all.
        intros.
        rewrite! STree.gsspec.
        destruct (STree.elt_eq x0 i).
        constructor ;auto.
        apply ext_equal_same_value.
        apply ext_equal_sym. auto.
        apply H0.
      }
      eapply eq_env_remove in EQ2;eauto.
    - apply eq_genv_eval_expr; tauto.
  Qed.

  Lemma eq_env_all_empty : eq_env_all STree.empty STree.empty.
  Proof.
    unfold eq_env_all.
    intros.
    rewrite STree.gempty.
    constructor.
  Qed.

  Lemma eq_env_lenv_update : forall e le le' s v1 v2 ge ge',
      eq_env (vars_of_expr STree.empty e) le le' ge ge' ->
      eq_env (vars_of_expr STree.empty e) (lenv_update tabs le s v1)
        (lenv_update tabs le' s v2) ge ge'.
  Proof.
    unfold eq_env;intros.
    unfold lenv_update in *.
    rewrite STree.gsspec in *.
    destruct (STree.elt_eq x s); try congruence.
    apply H;auto.
  Qed.

  Lemma eq_env_remove_params : forall {A: Type} (a:A)(lt:smaplist A) s vars le le' ge ge' v1 v2,
      eq_env (remove_params lt (STree.remove s vars)) le le' ge ge' ->
      eq_env (remove_params lt vars) (lenv_update tabs le s v1)
        (lenv_update tabs le' s v2) ge ge'.
  Proof.
    intros.
    unfold eq_env in *;intros.
    unfold lenv_update in *.
    rewrite STree.gsspec in *.
    destruct (STree.elt_eq x s); try discriminate.
    specialize (H _ H0 H1).
    rewrite remove_params_eq in H.
    change (STree.remove s vars) with (remove_params_r ((s,a)::nil) vars) in H.
    rewrite remove_params_r_comm in H.
    simpl in H.
    rewrite STree.gro in H by auto.
    apply H. rewrite remove_params_eq in H2. auto.
  Qed.

  Lemma build_funval_rec_eq : forall arch te ge ge' lt e le le' t,
      eq_env (vars_of_fun lt e) le le' ge ge' ->
      eq_env_all le le' ->
      ext_fun tabs (ext_equal tabs) t (map snd lt) (eval_fun_rec arch tabs te ge le lt t e)
        (eval_fun_rec arch tabs te ge' le' lt t e).
  Proof.
    unfold vars_of_fun.
    induction lt.
    - simpl.
      intros.
      apply  (eq_genv_eval_expr arch te ge ge' t e le le' H H0).
    - change (map snd (a :: lt))
        with  (snd a :: map snd lt).
      intros.
      rewrite ext_fun_rw.
      destruct lt.
      + simpl.
        intros.
        simpl in H. destruct a as (x,tx).
        simpl in H1,v1,v2.
        unfold fst,snd.
        eapply eq_genv_eval_expr.
        eapply eq_env_remove; auto.
        apply eq_env_all_lenv_update; auto.
      +
        intros.
        change (map snd (p :: lt)) with
           (snd p :: map snd lt).
        cbv beta iota.
        rewrite eval_fun_rec_rw.
        eapply IHlt.
       apply eq_env_remove_params;auto.
       simpl in H. destruct a,p.
       simpl. auto.
       apply eq_env_all_lenv_update; auto.
  Qed.





  Lemma genv_has_property_same : forall x ge' l acc v,
      STree.get x (genv_has_property acc l) = Some v ->
      Forall (has_property ge') l ->
      option_rel (same_value tabs) (Some v) (STree.get x ge') \/ STree.get x acc = Some v.
  Proof.
    induction l.
    - simpl.
      tauto.
    - simpl.
      destruct a.
      intros.
      inv H0.
      apply IHl in H; auto.
      destruct H.
      tauto.
      rewrite STree.gsspec in H.
      destruct (STree.elt_eq x s); subst.
      inv H.
      unfold has_property in H3.
      destruct H3 as (v' & GET & SAME).
      unfold genv_get in GET.
      simpl in GET. destruct (STree.get s ge'); try discriminate.
      inv GET. left; constructor ; auto.
      right;assumption.
  Qed.


  Lemma map_err_nil : forall {A B:Type} (F : A -> option B) (l:list (string * A)),
      map_err F l = Some nil -> l = nil.
  Proof.
    induction l; simpl.
    - congruence.
    - intros.
      monadInv H.
  Qed.

  Lemma eq_env_fst : forall {A B:Type} (v1 : smaplist A) (v2:smaplist B) e g1 g2,
      map fst v1 = map fst v2 ->
      eq_env (vars_of_fun v1 e) STree.empty STree.empty g1 g2 ->
      eq_env (vars_of_fun v2 e) STree.empty STree.empty g1 g2.
  Proof.
    intros.
    unfold vars_of_fun in *.
    unfold eq_env in *.
    intros.
    eapply H0 ; eauto.
    revert H3.
    revert H.
    generalize ((vars_of_expr STree.empty e)) as acc.
    clear. revert v2.
    induction v1 ; simpl;auto.
    - destruct v2; simpl;auto.
      discriminate.
    - destruct v2 ; try discriminate.
      simpl;intros.
      inv H;subst.
      destruct p. destruct a. simpl in H1. subst.
      eapply IHv1;eauto.
  Qed.

  Lemma map_err_fst : forall (A B:Type) (F : A -> option B) (l1:smaplist A) (l2:smaplist B),
      map_err F l1  = Some l2 ->
      map fst l1 = map fst l2.
  Proof.
    induction l1;simpl;auto.
    - intros. inv H. reflexivity.
    - intros. monadInv H. monadInv EQ.
      simpl. f_equal;auto.
  Qed.

  Lemma generate_def_fun_obligation_impl : forall arch f te params tret e checked prop o',
      generate_def_fun_obligation' arch f te params tret e checked prop = Some o' ->
      exists o, generate_def_fun_obligation arch te params tret e checked prop = Some o /\
                  (o' -> o).
  Proof.
    unfold generate_def_fun_obligation', generate_def_fun_obligation.
    intros.
    destruct (MergeSort.nodup String.leb String.eqb
                (map fst params)); try discriminate.
    destruct (Typing.btyp_to_typ te tret); try discriminate.
    simpl in *.
    destruct (map_err (Typing.btyp_to_typ te) params)eqn:PARAM; try discriminate.
    simpl in *.
    set (ge :=         (genv_has_property STree.empty
                          (filter (fun '(k, _) => has_var k (vars_of_fun params e))
                             checked))) in *.
    destruct (stree_equal (vars_of_fun params e) ge) eqn:ALLKEY; try discriminate.
    inv H.
    eexists. split. eauto.
    intros.
    eapply eq_value_trans;eauto.
    unfold eval_fun.
    assert (EQENV: eq_env (vars_of_fun params e) STree.empty STree.empty ge ge0).
    {
      unfold eq_env.
      intros.
      apply stree_equal_sound with (x:=x) in ALLKEY.
      destruct (STree.get x ge) eqn:GET.
      - clear ALLKEY.
        apply genv_has_property_same with (ge' := ge0) in GET;auto.
        destruct GET. auto.
        rewrite STree.gempty in H4. discriminate.
      - intuition congruence.
    }
    destruct l.
    - simpl.
      apply map_err_nil in PARAM. subst.
      generalize (eq_genv_eval_expr arch te ge ge0 t e STree.empty STree.empty EQENV eq_env_all_empty).
      intro EEXPR. auto.
    - unfold ext_equal; fold ext_equal.
      unfold map; fold map.
      change ((snd p :: (fix map (l : list (string * typ)) : list typ := match l with
                                                                         | nil => nil
                                                                         | a :: t1 => snd a :: map t1
                                                                         end) l))
        with (map snd (p :: l)).
      eapply build_funval_rec_eq.
      eapply eq_env_fst with (v1 := params).
      eapply map_err_fst;eauto.
      auto.
      apply eq_env_all_empty.
  Qed.

  Definition is_checked (x:Syntax.ident) (checked:list propt) :=
    List.existsb (fun p => string_dec x (fst p)) checked.

  Definition generate_decl_const_obligation (te: Typing.tenv) (checked:list propt) (x:Syntax.ident) (bt:btyp) : option Prop :=
    let* ty := Typing.btyp_to_typ te bt in
    (*  if is_checked x checked then*)
    let* v := find_err string_dec x checked  in
    let P := typeof_value tabs v = ty in
    ret P.

  Definition generate_decl_fun_obligation (te: Typing.tenv) (checked:list propt) (x:Syntax.ident) (params : list (Syntax.param_attr * btyp))
    (tret : btyp) : option Prop :=
    let* tparam := mmap (Typing.btyp_to_typ te) (map snd params)
    in let* tret' := Typing.btyp_to_typ te tret in
       let* v := find_err string_dec x checked  in
       let P := typeof_value tabs v = TFun tparam tret' in
       ret P.

  (* Definition tenv_update_opt (te: Typing.tenv) (x: Syntax.ident) (fields : smaplist typ) :=
  let id := StringIndexed.index x in
  match PTree.get id te.(tenv_defs) with
  | None => eret (PTree.set id fields te)
  | Some _ => fail
  end. *)

  (* Definition obligation_def_type (te: Typing.tenv) (x:Syntax.ident) (fields : SMapList.t btyp) : option Typing.tenv :=
  let* fields' := fields_btyp_to_typ te fields in
  tenv_update_opt te x fields'. *)

  Definition obligation_def_type (te: Typing.tenv) (x: ident) (td: Syntax.type_def field_descr) : option Typing.tenv :=
    eval_def_type te x td.

  Fixpoint generate_obligations (arch:archi)  (te:Typing.tenv)
    (checked : list propt) (vc : list Prop) (p:program) (props : list propt) : option (list Prop) :=
    match p with
    | nil => match props with
             | nil => ret vc
             | _   => fail
             end
    | a :: prog' =>
        match a with
        | DefType a td =>
            let* te' := obligation_def_type te a td in
            generate_obligations arch  te' checked vc prog' props
        | DefConst x l ty    =>
            let* (p,props') := get_prop x props in
            let*  o  := generate_const_obligation te x l ty p in
            generate_obligations arch  te ((x,p)::checked) (o::vc) prog'  props'
        | DefFun y f =>
            let* (p,props') := get_prop y props in
            let*  o   := generate_def_fun_obligation' arch y te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p in
            generate_obligations arch  te ((y,p)::checked) (o::vc) prog'  props'
        | DeclType _ _  => generate_obligations arch  te checked vc prog' props
        | DeclConst y bt =>
            let* o := generate_decl_const_obligation te checked y bt in
            generate_obligations arch  te checked (o::vc) prog' props
        | DeclFun y params tret =>
            let* o := generate_decl_fun_obligation te checked y params tret in
            generate_obligations arch  te checked (o::vc) prog' props
        end
    end.


  Lemma get_prop_inv : forall s p props props',
      get_prop s props = Some (p, props')  ->
      props = (s,p) :: props'.
  Proof.
    unfold get_prop.
    destruct props; try discriminate.
    intros. destruct p0.
    destruct (String.eqb s s0) eqn:EQ.
    rewrite String.eqb_eq in EQ.
    inv H. reflexivity.
    discriminate.
  Qed.



  Definition wf_checked (props : list propt) (prog:program) :=
    forall s p, In (s,p) props -> In s (map ident_of_globdef (filter has_prop prog)) ->  False.

  Definition incr_genv (ge ge': genv tabs) (prog:program) :=
    (forall x v, STree.get x ge = Some v -> STree.get x ge' = Some v)
    /\
      forall x,
        In x (map ident_of_globdef (filter has_prop prog)) ->
        STree.get x ge' = None.

  Lemma incr_genv_def_const : forall x l ty prog ge0 ge,
      incr_genv ge0 ge (DefConst x l ty :: prog) ->
      genv_get tabs ge x = fail.
  Proof.
    unfold incr_genv.
    intros.
    destruct H.
    unfold genv_get.
    rewrite H0. reflexivity.
    simpl. tauto.
  Qed.



  Lemma generate_const_obligation_sound :
    forall te x l ty p (P:Prop) ge
           (GEN : generate_const_obligation te x l ty p = Some P)
           (GET : genv_get tabs ge x = fail)
           (HOLD : P),
    exists ge',
      eval_def_const tabs te ge x l ty = Some ge' /\
        has_property ge' (x,p).
  Proof.
    unfold generate_const_obligation.
    unfold eval_def_const.
    intros.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    simpl in GEN. inv GEN.
    unfold check_value in HOLD.
    destruct (eval_literal tabs te l); try tauto.
    simpl in *.
    destruct (cast_value tabs v t); try tauto.
    simpl.
    unfold genv_update.
    rewrite GET. simpl.
    eexists. split. reflexivity.
    unfold has_property. simpl. eexists.
    unfold genv_get. rewrite STree.gss.
    split. reflexivity.
    apply eq_value_same_value;auto.
  Qed.

  Lemma wf_checked_DefConst : forall checked x l ty prog p ,
      NoDup (x::(map ident_of_globdef prog)) ->
      wf_checked checked (DefConst x l ty :: prog) ->
      wf_checked ((x, p) :: checked) prog.
  Proof.
    unfold wf_checked.
    intros.
    simpl in H1.
    destruct H1; subst.
    inv H1. inv H.
    apply H4.
    rewrite in_map_iff.
    rewrite in_map_iff in H2.
    destruct H2 as (gf & EQ & IN).
    rewrite filter_In in IN.
    destruct IN.
    exists gf; split; auto.
    eapply H0; eauto.
    simpl. tauto.
  Qed.

  Lemma incr_genv_DefConst : forall ge ge' x l ty prog,
      incr_genv ge ge' (DefConst x l ty :: prog) ->
      incr_genv ge ge' prog.
  Proof.
    unfold incr_genv.
    simpl. intros.
    destruct H; split; intros.
    eapply H; eauto.
    eapply H0; eauto.
  Qed.

  Lemma incr_genv_DefFun : forall ge ge' x f prog,
      incr_genv ge ge' (DefFun x f :: prog) ->
      incr_genv ge ge' prog.
  Proof.
    unfold incr_genv.
    simpl. intros.
    destruct H; split; intros.
    eapply H; eauto.
    eapply H0; eauto.
  Qed.

  Lemma SMapList_NoDup : forall (V: Type) (l: smaplist V),
      NoDup (map fst l)  ->
      MapList.nodup string_dec l = true.
  Proof.
    induction l; simpl;auto.
    destruct a.
    simpl.
    intros.
    inv H.
    destruct (MapList.mem string_dec s l) eqn:MEM; auto.
    exfalso.
    {
      apply H2.
      clear - MEM.
      induction l ; simpl; auto.
      discriminate.
      simpl in MEM. destruct a.
      destruct (string_dec s0 s); simpl; try congruence.
      tauto.
      tauto.
    }
  Qed.

  Lemma ascii_compare_lt_trans : forall x y z,
      Ascii.compare x y = Lt ->
      Ascii.compare y z = Lt ->
      Ascii.compare x z = Lt.
  Proof.
    unfold Ascii.compare.
    intros.
    rewrite N.compare_lt_iff   in *.
    lia.
  Qed.


  Lemma String_leb_trans : forall (x y z:string),
      x <=? y = true -> y <=? z = true  -> x <=? z = true.
  Proof.
    unfold String.leb.
    intros.
    destruct (x ?= y) eqn:Cxy; try discriminate;
      destruct (y ?= z) eqn:Cyz; try discriminate;
      destruct (x ?=z) eqn:Cxz; try reflexivity; try congruence.
    + apply compare_eq_iff in Cxy.
      apply compare_eq_iff in Cyz.
      subst.
      generalize (compare_antisym z z).
      intros. rewrite Cxz in H1. discriminate.
    + apply compare_eq_iff in Cxy.
      subst. congruence.
    + apply compare_eq_iff in Cyz.
      subst. congruence.
    + assert (x ?= z = Lt).
      { clear Cxz.
        revert y z Cxy Cyz.
        { induction x ; simpl.
          -  destruct y; simpl; try discriminate.
             intros.
             destruct z; simpl; try discriminate.
             reflexivity.
          -  destruct y; simpl ; try discriminate.
             destruct (Ascii.compare a a0) eqn:AC; try discriminate.
             + destruct z; simpl; auto.
               apply Ascii.compare_eq_iff in AC.
               subst.
               destruct (Ascii.compare a0 a1); auto.
               apply IHx.
             + destruct z; simpl; auto.
               destruct (Ascii.compare a0 a1) eqn:AC1;
                 try discriminate.
               apply Ascii.compare_eq_iff in AC1.
               subst.
               rewrite AC. auto.
               erewrite ascii_compare_lt_trans; eauto.
        }
      }
      congruence.
  Qed.

  Lemma eqb_leb : forall x y,
      (x =? y) = (x <=? y) && (y <=? x).
  Proof.
    intros.
    generalize (leb_antisym x y).
    generalize (String.eqb_spec x y).
    intros. inv H.
    +
      destruct (leb_total y y).
      rewrite H; reflexivity.
      rewrite H; reflexivity.
    + destruct (x <=?y) eqn:LEX; try reflexivity.
      destruct (y <=?x) eqn:LEY; try reflexivity.
      intuition congruence.
  Qed.



  Lemma nodup_eq : forall (V: Type) (l: smaplist V) ,
      MergeSort.nodup String.leb String.eqb (map fst l) = true ->
      MapList.nodup string_dec l = true.
  Proof.
    intros. apply SMapList_NoDup.
    apply MergeSort.nodup_NoDup in H; auto.
    - apply leb_total.
    - intros.  apply eqb_leb.
    - apply String.leb_antisym.
    - unfold RelationClasses.Transitive.
      intros.
      eapply String_leb_trans; eauto.
  Qed.

  Lemma nodup_NoDup : forall (l:list string),
      MergeSort.nodup String.leb String.eqb l = true ->
      NoDup l.
  Proof.
    intro.
    eapply MergeSort.nodup_NoDup with (leb:=String.leb) (eqb:=String.eqb).
    apply leb_total. apply eqb_leb.
    apply String.leb_antisym.
    unfold RelationClasses.Transitive.
    intros.
    eapply String_leb_trans; eauto.
  Qed.



  Lemma has_property_set : forall x v p ge,
      same_value tabs v p ->
      has_property (STree.set x v ge) (x, p).
  Proof.
    unfold has_property.
    intros.
    unfold genv_get.
    simpl. rewrite STree.gss. exists v.
    split. reflexivity.
    apply same_value_sym. assumption.
  Qed.

  (** For each program declaration,
    if the proof obligation holds then the evaluation succeeds and
    the declaration has the property *)

  Lemma generate_def_fun_obligation_sound :
    forall arch te x f checked ge p o
           (GEN : generate_def_fun_obligation arch te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p = Some o)
           (GET : genv_get tabs ge x = fail)
           (ALL : Forall (has_property ge) checked)
           (HAS : o)
    ,
    exists ge',
      eval_def_fun arch tabs te ge x f = Some ge' /\
        has_property ge' (x,p).
  Proof.
    unfold generate_def_fun_obligation.
    unfold eval_def_fun.
    unfold mk_fun_value.
    intros.
    destruct (@MergeSort.nodup string String.leb String.eqb
                (@map (prod string btyp) string
                   (@fst string btyp)
                   (@Syntax.fn_params expr btyp f))
             ) eqn:DUP; try discriminate.
    apply nodup_eq in DUP. unfold Ident.eq_dec. rewrite DUP.
    destruct (Typing.btyp_to_typ te (Syntax.fn_return f)); try discriminate.
    simpl in GEN.
    simpl.
    destruct (map_err (Typing.btyp_to_typ te) (Syntax.fn_params f)); try discriminate.
    simpl in GEN; simpl.
    inv GEN.
    unfold genv_update.
    rewrite GET.
    simpl. eexists.
    split.  reflexivity.
    apply has_property_set; auto.
    apply same_value_sym.
    apply eq_value_same_value.
    apply HAS.
    rewrite Forall_forall.
    intros.
    rewrite filter_In in H.
    destruct H.
    rewrite Forall_forall in ALL. auto.
  Qed.

  Lemma has_property_find_err : forall ge x checked,
      Forall (has_property ge) checked   ->
      forall v, find_err string_dec x checked = Some v ->
                has_property ge (x,v).
  Proof.
    intros ge x checked ALL.
    induction ALL.
    - simpl. discriminate.
    - simpl.
      destruct x0.
      intros. destruct (string_dec s x); subst.
      + inv H0. auto.
      + eapply IHALL;auto.
  Qed.


  Lemma has_property_equal :
    forall te ge0 ge s t v prog
           (EVAL: eval_prog Ptr64 tabs ge0 prog = Some (te,ge))
           (FO : fo_typ t = true)
           (HASP : has_property  ge  (s,Val tabs t v)),
    exists
      v' : eval_typ tabs t,
      (let* (_, ge0):= eval_prog Ptr64 tabs ge0 prog
       in genv_get tabs ge0 s) =
        Some (Val tabs t v') /\ ext_equal_fo tabs t v' v.
  Proof.
    intros.
    unfold has_property in HASP.
    destruct HASP as (v' & GET & SV).
    simpl in GET. unfold snd in SV.
    destruct v'. simpl in SV.
    destruct (typ_eq_dec t0 t); try tauto.
    subst.
    change (cast eq_refl v0) with v0 in SV.
    apply ext_equal_fo_equal in SV;auto.
    rewrite EVAL. simpl. exists v0; split;auto.
  Qed.



  Lemma generate_decl_const_obligation_sound :
    forall te x bt checked ge P
           (GEN : generate_decl_const_obligation  te checked x bt = Some P)
           (ALL : Forall (has_property ge) checked)
           (HOLD: P)
    ,
    exists ge',
      eval_decl_const tabs  te ge x bt = Some ge'.
  Proof.
    unfold generate_decl_const_obligation.
    unfold eval_decl_const.
    intros.
    destruct (Typing.btyp_to_typ te bt); try discriminate.
    simpl in GEN.
    destruct (find_err string_dec x checked) eqn:FIND ; try discriminate.
    simpl in GEN. inv GEN.
    apply has_property_find_err with (ge:=ge) in FIND;auto.
    simpl. unfold has_property in FIND.
    destruct FIND as (v' & GET& SV).
    simpl in SV. simpl in GET. rewrite GET.
    simpl. assert (typeof_value tabs v' = t).
    { unfold same_value in SV.
      destruct v,v'. destruct (typ_eq_dec t1 t0); try tauto.
      simpl in *. congruence.
    }
    rewrite H. destruct (typ_eq_dec t t); try congruence.
    eexists ; reflexivity.
  Qed.

  Lemma generate_decl_fun_obligation_sound :
    forall te x tparams tret checked ge P
           (GEN : generate_decl_fun_obligation  te checked x tparams tret  = Some P)
           (ALL : Forall (has_property ge) checked)
           (HOLD: P)
    ,
    exists ge',
      eval_decl_fun tabs  te ge x tparams tret = Some ge'.
  Proof.
    unfold generate_decl_fun_obligation.
    unfold eval_decl_fun.
    intros.
    destruct (mmap (Typing.btyp_to_typ te) (map snd tparams)); try discriminate.
    destruct (Typing.btyp_to_typ te tret); try discriminate.
    simpl in GEN.
    destruct (find_err string_dec x checked) eqn:FIND.
    simpl in GEN. inv GEN.
    unfold bind. unfold Res.bind.
    apply has_property_find_err with (ge:=ge)  in FIND; auto.
    destruct FIND as (v' & GET & HAS).
    simpl in GET.
    rewrite GET.
    assert (typeof_value tabs v' = (TFun l t)).
    {
      simpl in HAS. destruct v,v'; simpl in *.
      destruct (typ_eq_dec t1 t0); try congruence.
      tauto.
    }
    unfold bind, Res.bind.
    rewrite H.
    destruct (typ_eq_dec (TFun l t) (TFun l t)); try congruence.
    eexists.
    reflexivity.
    discriminate.
  Qed.


  Definition has_def (g:globdef) :=
    match g with
    | DefConst _ _ _ | DefFun _ _ => true
    | _ => false
    end.

  Definition wf_env (ge: genv tabs) (prog: program) :=
    forall d, In d prog -> has_def d = true -> genv_get tabs ge (ident_of_globdef d) = fail.

  Lemma wf_env_tail : forall ge d prog,
      wf_env ge (d :: prog) ->
      wf_env ge prog.
  Proof.
    unfold wf_env ; simpl in *.
    intros.
    apply H; auto.
  Qed.

  Lemma genv_gsspec : forall x v ge y,
      genv_get tabs (STree.set x v ge) y =
        if string_dec x y
        then Some v else genv_get tabs ge y.
  Proof.
    unfold genv_get, STree.get,STree.set.
    intros.
    rewrite PTree.gsspec.
    destruct (string_dec x y).
    - subst.
      destruct (peq (StringIndexed.index y) (StringIndexed.index y));try congruence.
    - destruct (peq (StringIndexed.index y) (StringIndexed.index x)); try discriminate; auto.
      apply Ctypesdefs.ident_of_string_injective in e.
      congruence.
  Qed.

  Lemma wf_env_DefConst :
    forall te ge ge' x l ty prog
           (DUP : NoDup (map ident_of_globdef (DefConst x l ty :: prog)))
           (WF : wf_env ge (DefConst x l ty :: prog))
           (EVAL : eval_def_const tabs te ge x l ty = Some ge'),
      wf_env ge' prog.
  Proof.
    unfold eval_def_const.
    intros.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    simpl in EVAL.
    destruct (eval_literal tabs te l) eqn:EL; try discriminate.
    simpl in EVAL.
    destruct (cast_value tabs v t); try discriminate.
    unfold wf_env in *.
    intros.
    unfold genv_update in EVAL.
    destruct (genv_get tabs ge x) eqn:GET; try discriminate.
    inv EVAL.
    rewrite genv_gsspec.
    destruct (string_dec x (ident_of_globdef d)).
    simpl in DUP.
    subst. inv DUP.
    exfalso.
    apply H3.
    rewrite in_map_iff.
    exists d. split; auto.
    apply WF; auto.
    simpl. tauto.
  Qed.

  Lemma wf_env_DefFun :
    forall arch te ge ge' x f prog
           (DUP : NoDup (map ident_of_globdef (DefFun x f :: prog)))
           (WF : wf_env ge (DefFun x f :: prog))
           (EVAL : eval_def_fun arch tabs te ge x f = Some ge'),
      wf_env ge' prog.
  Proof.
    unfold eval_def_fun.
    intros.
    unfold mk_fun_value in EVAL.
    destruct (MapList.nodup Ident.eq_dec (Syntax.fn_params f)); try discriminate.
    destruct (Typing.btyp_to_typ te (Syntax.fn_return f)); try discriminate.
    simpl in EVAL.
    destruct (map_err (Typing.btyp_to_typ te) (Syntax.fn_params f)); try discriminate.
    simpl in EVAL.
    unfold wf_env in *.
    intros.
    unfold genv_update in EVAL.
    destruct (genv_get tabs ge x) eqn:GET; try discriminate.
    inv EVAL.
    rewrite genv_gsspec.
    destruct (string_dec x (ident_of_globdef d)).
    simpl in DUP.
    subst. inv DUP.
    exfalso.
    apply H3.
    rewrite in_map_iff.
    exists d. split; auto.
    apply WF; auto.
    simpl. tauto.
  Qed.


  Lemma generate_obligations_incl :
    forall arch prog te checked props ol vc
           (GEN : generate_obligations arch  te checked vc prog props = Some ol),
    forall x, In x vc -> In x ol.
  Proof.
    induction prog.
    - simpl. destruct props. intros.
      inv GEN. auto.
      discriminate.
    - simpl.
      destruct a; intros.
      + destruct (obligation_def_type te i t); try discriminate.
        simpl in GEN.
        eapply IHprog; eauto.
      +  destruct (get_prop i props) eqn:GP; try discriminate.
         destruct p as (p,props').
         simpl in GEN.
         apply get_prop_inv in GP.
         subst.
         destruct (generate_const_obligation te i l b p); try discriminate.
         simpl in GEN.
         eapply IHprog in GEN;eauto.
         simpl. tauto.
      + destruct (get_prop i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        subst.
        destruct (generate_def_fun_obligation' arch i te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p);
          try discriminate.
        simpl in GEN.
        eapply IHprog in GEN;eauto.
        simpl. tauto.
      + eapply IHprog;eauto.
      +
        destruct (generate_decl_const_obligation te checked i b); try discriminate.
        simpl in GEN.
        eapply IHprog in GEN;eauto.
        simpl. tauto.
      +
        destruct (generate_decl_fun_obligation te checked i l b); try discriminate.
        simpl in GEN.
        eapply IHprog in GEN;eauto.
        simpl. tauto.
  Qed.

  Lemma obligation_def_type_eq : forall te tid fields ,
      obligation_def_type te tid fields = eval_def_type te tid fields.
  Proof.
    reflexivity.
  Qed.



  Lemma generate_obligations_sound :
    forall arch prog te checked props ol vc
           (ND : NoDup (map ident_of_globdef prog))
           (GEN : generate_obligations arch  te checked vc prog props = Some ol)
           (OBL : Forall (fun p => p) ol)
    ,
    forall ge,
      wf_env ge prog ->
      Forall (has_property ge) checked ->
      exists te' ge', eval_prog_rec arch tabs te ge prog = Some (te',ge') /\
                        Forall (has_property ge') props.
  Proof.
    induction prog.
    - simpl.
      intros. destruct props ; try discriminate.
      do 2 eexists. split. reflexivity.
      constructor.
    - simpl.
      destruct a.
      + intros.
        rewrite obligation_def_type_eq in GEN.
        destruct (eval_def_type te i t); try discriminate.
        simpl in *.
        eapply IHprog in GEN ; eauto.
        inv ND ; auto.
        apply wf_env_tail in H; auto.
      + intros.
        destruct (get_prop i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        destruct (generate_const_obligation te i l b p) eqn:CO; try discriminate.
        simpl in GEN.
        destruct  (generate_const_obligation_sound _ _ _ _ _ _ ge CO) as (ge' & EF & HP ).
        { unfold wf_env in H.
          apply (H (DefConst i l b)).
          simpl. tauto. reflexivity.
        }
        {
          apply generate_obligations_incl with (x:= P) in GEN.
          rewrite Forall_forall in OBL.
          apply OBL;auto.
          simpl. tauto.
        }
        rewrite EF. simpl.
        apply IHprog with (ge:=ge') in GEN; auto.
        destruct GEN as (te2 & ge2 & EQ & ALL).
        do 2 eexists ; split; eauto.
        subst.
        constructor.
        apply eval_prog_rec_preserve_properties with (props := (i,p)::nil) in EQ.
        inv EQ ; auto.
        constructor ; auto.
        auto.
        inv ND ; auto.
        eapply wf_env_DefConst; eauto.
        constructor ;auto.
        eapply eval_prog_rec_preserve_properties with (prog := (DefConst i l b)::nil).
        apply H0. simpl. rewrite EF. reflexivity.
        Unshelve. apply arch.
      + intros.
        destruct (get_prop i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        destruct (generate_def_fun_obligation'  arch i te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p) eqn:CO; try discriminate.
        simpl in GEN.
        apply generate_def_fun_obligation_impl in CO.
        destruct CO as (o & CO & IMPL).
        destruct  (generate_def_fun_obligation_sound _ _ i _ _  ge _ _ CO) as (ge' & EF & HP ).
        { unfold wf_env in H.
          apply (H (DefFun i f )).
          simpl. tauto. reflexivity.
        }
        auto.
        { apply generate_obligations_incl with (x:=P) in GEN.
          rewrite Forall_forall in OBL. apply IMPL.  apply OBL;auto.
          simpl. tauto.
        }
        rewrite EF. simpl.
        apply IHprog with (ge:=ge') in GEN; auto.
        destruct GEN as (te2 & ge2 & EQ & ALL).
        do 2 eexists ; split; eauto.
        subst.
        constructor.
        apply eval_prog_rec_preserve_properties with (props := (i,p)::nil) in EQ.
        inv EQ ; auto.
        constructor ; auto.
        auto.
        inv ND ; auto.
        eapply wf_env_DefFun; eauto.
        constructor ;auto.
        eapply eval_prog_rec_preserve_properties with (prog := (DefFun i f)::nil).
        apply H0. simpl. rewrite EF. reflexivity.
      + intros.
        eapply IHprog;eauto.
        inv ND;auto.
        eapply wf_env_tail;eauto.
      + intros.
        destruct (generate_decl_const_obligation te checked i b) eqn:DECL ; try discriminate.
        destruct (generate_decl_const_obligation_sound te i b checked ge P DECL); auto.
        simpl in GEN.
        { apply generate_obligations_incl with (x:=P) in GEN.
          rewrite Forall_forall in OBL. apply OBL;auto.
          simpl. tauto.
        }
        rewrite H1. simpl.
        simpl in GEN.
        apply IHprog with (ge:=ge) in GEN; auto.
        inv ND ; auto.
        eapply wf_env_tail; eauto.
      + intros.
        destruct (generate_decl_fun_obligation te checked i l b) eqn:DECL ; try discriminate.
        destruct (generate_decl_fun_obligation_sound te i l b checked ge P DECL); auto.
        simpl in GEN.
        { apply generate_obligations_incl with (x:=P) in GEN.
          rewrite Forall_forall in OBL. apply OBL;auto.
          simpl. tauto.
        }
        rewrite H1. simpl.
        simpl in GEN.
        apply IHprog with (ge:=ge) in GEN; auto.
        inv ND ; auto.
        eapply wf_env_tail; eauto.
  Qed.

  Lemma eval_prog_rec_app : forall arch abs_types_impl p1 p2 te ge te1 ge1 te2 ge2,
      eval_prog_rec arch abs_types_impl te ge p1 = Some (te1, ge1) ->
      eval_prog_rec arch abs_types_impl te1 ge1 p2 = Some (te2, ge2) ->
      eval_prog_rec arch abs_types_impl te ge (p1++p2)%list = Some (te2, ge2).
  Proof.
    induction p1; simpl.
    - intros. inv H. auto.
    - destruct a; intros.
      + destruct (eval_def_type te i t); try discriminate.
        simpl in H. simpl. eapply IHp1;eauto.
      + destruct (eval_def_const abs_types_impl te ge i l b); try discriminate.
        eapply IHp1;eauto.
      + destruct (eval_def_fun arch abs_types_impl te ge i f); try discriminate.
        eapply IHp1;eauto.
      + eauto.
      + destruct (eval_decl_const abs_types_impl te ge i b); try discriminate.
        eauto.
      + destruct (eval_decl_fun abs_types_impl te ge i l b); try discriminate.
        eauto.
  Qed.

  Inductive globdef_kind : Type :=
  | KindType (* Declaration of types *)
  | KindDef (* Definition *)
  | KindDecl (* Declaration *).

  Definition kind_of_globdef (gd:globdef) :=
    match gd with
    | DefType _ _ | DeclType _ _ => KindType
    | DeclConst _ _ | DeclFun _ _ _ => KindDecl
    | DefFun _ _ | DefConst _ _  _  => KindDef
    end.

  Fixpoint partition_props (prog:program) (props : list propt) :=
    match prog with
    | nil => match props with
             | nil => ret (nil,nil)
             |  _  => fail
             end
    | a :: prog' => match kind_of_globdef a with
                    | KindType => partition_props prog' props
                    | KindDecl => match props with
                                  | nil => fail
                                  | p1::props' => let* (decl,defs) := partition_props prog' props' in
                                                  ret (p1::decl,defs)
                                  end
                    | KindDef  => match props with
                                  | nil => fail
                                  | p1::props' => let* (decl,defs) := partition_props prog' props' in
                                                  ret (decl,p1::defs)
                                  end
                    end
    end.


End S.
