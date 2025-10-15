(**  Generation of verification conditions to prove equivalence between
     Shallow and Deep embedding. *)

From Coq Require Import String List.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Target Ident Monads Error Barray Brecord Types Barocq Maps2 MergeSort Utils.
From compcert Require Import Coqlib.
From Coq Require Import ZifyBool.

Open Scope string_scope.
Import Typed.

(** [typ_eqb : typ -> typ -> bool] mayb be faster than [typ_eq_dec] *)
Definition signedness_eqb (s1 s2: signedness) : bool:=
  match s1 , s2 with
  | Unsigned , Unsigned => true
  | Signed , Signed => true
  | _ , _ => false
  end.

Fixpoint typ_eqb (t1 t2:typ) :=
  match t1 , t2 with
  | TBool , TBool => true
  | TInt32 s1 , TInt32 s2 => signedness_eqb s1 s2
  | TInt64 s1 , TInt64 s2 => signedness_eqb s1 s2
  | TArray t1 , TArray t2 => typ_eqb t1 t2
  | TRecord i1 l1 , TRecord i2 l2 => if String.eqb i1 i2
                                     then forall2b (fun '(x,t1) '(y,t2) => if String.eqb x y then typ_eqb t1 t2 else false) l1 l2
                                     else false
  | TFun a1 r1 , TFun a2 r2 => if typ_eqb r1 r2
                               then forall2b typ_eqb a1 a2
                               else false
  | TAbs i1 , TAbs i2 => String.eqb i1 i2
  | _ , _ => false
  end.

Lemma signedness_eqb_true : forall s s',
    signedness_eqb s s' = true -> s =  s'.
Proof.
  destruct s, s'; simpl; congruence.
Qed.

Fixpoint typ_eqb_true (t1 t2:typ) {struct t1} : typ_eqb t1 t2 = true -> t1 = t2.
Proof.
  destruct t1; destruct t2; simpl; try congruence.
  -  intros.
     apply signedness_eqb_true in H; congruence.
  -  intros. apply signedness_eqb_true in H; congruence.
  - intros.
    f_equal ; apply typ_eqb_true;assumption.
  - destruct (i =? i0) eqn:EQ ; try discriminate.
    intro.
    f_equal.
    rewrite String.eqb_eq in EQ. assumption.
    revert l0 H.
    induction l.
    +  simpl. destruct l0. reflexivity.
       discriminate.
    + simpl.
      destruct l0; try discriminate.
      destruct a,p.
      destruct (i1 =? i2) eqn:EQ1 ; try discriminate.
      destruct (typ_eqb t t0) eqn:TYP.
      apply typ_eqb_true in TYP.
      intros.
      f_equal.
      rewrite String.eqb_eq in EQ1.
      congruence.
      apply IHl;auto.
      discriminate.
  -  destruct (typ_eqb t1 t2) eqn:TB; try discriminate.
     intro.
     f_equal.
     revert l0 H.
     induction l; destruct l0; simpl; try discriminate.
     auto.
     destruct (typ_eqb a t) eqn:TB'.
     apply typ_eqb_true in TB'.
     intro.
     f_equal; auto. discriminate.
     apply typ_eqb_true; auto.
  - intros. f_equal.
    rewrite String.eqb_eq in H.
    assumption.
Qed.



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
  Variable abs_typ_impl : Maps.PMap.t Type.

  Local Notation "# X" := (Types.eval_typ abs_typ_impl X) (at level 90).



  Section EQUAL_FUN.
    Variable PRED : forall (t:typ), # t -> # t -> Prop.

    (** [ext_fun f1 f2] holds if the functions [f1] and [f2] are extentionnaly equal *)
    Fixpoint ext_fun (tret: typ) (targs : list typ)  {struct targs}:
      forall (f1 f2 : eval_funtyp (eval_typ abs_typ_impl) targs (eval_typ abs_typ_impl tret)), Prop:=
      match targs with
      | nil => fun f1 f2 => res_rel (PRED tret) (f1 tt) (f2 tt)
      | t :: l =>
      fun f1 f2 =>   forall v1 v2 : # t,
          PRED t v1 v2 ->
          match
            l as l0
            return
            ((forall (f1 f2: eval_funtyp (eval_typ abs_typ_impl) l0 (# tret)), Prop) ->
             (forall f1 f2 : eval_funtyp (eval_typ abs_typ_impl) (t::l0) (# tret), Prop))
          with
          | nil => fun _  (f3 f4 : # t -> res (# tret)) =>
                     res_rel (PRED tret) (f3 v1) (f4 v2)
          | t0 :: l0 => fun ext_fun f3 f4 => ext_fun (f3 v1) (f4 v2)
          end (ext_fun tret l) f1 f2
      end.



    Lemma ext_fun_rw : forall(tret: typ) (targs : list typ),
        forall (f1 f2 : eval_funtyp (eval_typ abs_typ_impl) targs (eval_typ abs_typ_impl tret)),
          (ext_fun tret targs f1 f2) =
            ((      match targs with
      | nil => fun f1 f2 => res_rel (PRED tret) (f1 tt) (f2 tt)
      | t :: l =>
      fun f1 f2 =>   forall v1 v2 : # t,
          PRED t v1 v2 ->
          match
            l as l0
            return
            ((forall (f1 f2: eval_funtyp (eval_typ abs_typ_impl) l0 (# tret)), Prop) ->
             (forall f1 f2 : eval_funtyp (eval_typ abs_typ_impl) (t::l0) (# tret), Prop))
          with
          | nil => fun _  (f3 f4 : # t -> res (# tret)) =>
                     res_rel (PRED tret) (f3 v1) (f4 v2)
          | t0 :: l0 => fun ext_fun f3 f4 => ext_fun (f3 v1) (f4 v2)
          end (ext_fun tret l) f1 f2
      end : eval_funtyp (eval_typ abs_typ_impl) targs (eval_typ abs_typ_impl tret) -> eval_funtyp (eval_typ abs_typ_impl) targs (eval_typ abs_typ_impl tret) -> Prop) f1 f2).
    Proof.
      destruct targs;auto.
    Qed.


  End EQUAL_FUN.

  Section EQUAL_RECORD.
    Variable PRED : forall (t:typ), # t -> # t -> Prop.

    Fixpoint equal_record (fields : list (ident * typ))  {struct fields} : forall (r1 r2: eval_recordtyp (eval_typ abs_typ_impl) fields), Prop :=
      match fields with
      | nil => fun _ _ => True
      | (i,t) :: lt => fun r1 r2 => PRED t (proj_field (fst r1)) (proj_field (fst r2)) /\
                                      equal_record lt (snd r1) (snd r2)
      end.
  End EQUAL_RECORD.



  (** [ext_equal v1 v2] holds if the values are equal. For function types, it uses ext_fun (but not recursively) *)
  Fixpoint ext_equal (t :typ) : forall (v1 v2 : # t), Prop :=
    match t as t0 return (# t0 -> # t0 -> Prop) with
    | TFun l t0 => fun f1 f2 => ext_fun ext_equal t0 l f1 f2
    | TArray t1 => fun a1 a2 =>  forall x, option_rel (ext_equal t1) (nth_error a1 x) (nth_error a2 x)
    | TRecord id l => fun r1 r2 => equal_record ext_equal l r1 r2
    | _ => eq
    end.


    (** [ext_fun_fo f1 f2] holds if the functions [f1] and [f2] are extentionnaly equal *)
  Fixpoint ext_fun_fo (tret: typ) (targs : list typ)  {struct targs}: forall (f1 f2 : eval_funtyp (eval_typ abs_typ_impl) targs (#tret)), Prop :=
      match targs with
      | nil => fun f1 f2 =>  (f1 tt) = (f2 tt)
      | t :: l =>
      fun f1 f2 =>   forall v,
          match
            l as l0
            return
            ((forall (f1 f2: eval_funtyp (eval_typ abs_typ_impl) l0 (# tret)), Prop) ->
             (forall f1 f2 : eval_funtyp (eval_typ abs_typ_impl) (t::l0) (# tret), Prop))
          with
          | nil => fun _  (f3 f4 : # t -> res (# tret)) =>
                     (f3 v) = (f4 v)
          | t0 :: l0 => fun ext_fun f3 f4 => ext_fun (f3 v) (f4 v)
          end (ext_fun_fo tret l) f1 f2
      end.


  (** [ext_equal_fo v1 v2]  encodes functional extensionality of functions (it is more restricted than ext_equal) *)
  Definition ext_equal_fo (ty:typ)  : eval_typ abs_typ_impl ty -> eval_typ abs_typ_impl ty -> Prop:=
    match ty with
    | TFun params ret => fun f1 f2 => ext_fun_fo ret params f1 f2
    |  _ =>  eq
    end.


  Fixpoint ext_equal_sym (t:typ): forall v1 v2,
      ext_equal t v1 v2 ->
      ext_equal t v2 v1.
  Proof.
    destruct t; try (simpl; intros; congruence).
    - simpl. intros.
      specialize (H x).
      inv H; auto.
      constructor.
      constructor. apply ext_equal_sym;auto.
    - simpl; intros. unfold eval_recordtyp.
      induction l.
      + simpl. auto.
      + simpl. destruct a. simpl.
        intros.
        destruct H. split.
        apply ext_equal_sym;auto.
        apply IHl;auto.
    -  unfold eval_typ; fold eval_typ.
        unfold ext_equal; fold ext_equal.
        intros.
        induction l.
        { simpl.
          apply res_rel_sym; auto.
        }
        { simpl.
          destruct l.
          + intros.
            simpl in H.
            apply res_rel_sym;auto.
          + intros.
            rewrite ext_fun_rw in H.
            apply IHl.
            apply H.
            apply ext_equal_sym;auto.
        }
  Qed.


  Definition ext_eq_array (t:typ) (a1 a2 : array (# t)) :=
    forall x, option_rel (ext_equal t) (nth_error a1 x) (nth_error a2 x).

  Lemma ext_equal_length : forall ty a1 a2,
      ext_eq_array ty a1 a2 ->
      length a1 = length a2.
  Proof.
    unfold ext_eq_array.
    induction a1; destruct a2; auto.
    -  intros.
       specialize (H O) ; simpl in H.
       inv H.
    - intros.
      specialize (H O). inv H.
    - intros.
      simpl.
      f_equal.
      apply IHa1.
      intros.
      specialize (H (S x)).
      simpl in H. auto.
  Qed.

  Lemma ext_equal_valid_index : forall ty a1 a2,
      ext_eq_array ty a1 a2 ->
      forall i,
        valid_index a1 i = valid_index a2 i.
  Proof.
    intros.
    apply ext_equal_length in H.
    unfold valid_index.
    unfold Barray.length.
    rewrite H. reflexivity.
  Qed.

  Lemma ext_eq_array_sym : forall t a1 a2,
      ext_eq_array t a1 a2 ->
      ext_eq_array t a2 a1.
  Proof.
    unfold ext_eq_array.
    intros.
    specialize (H x).
    inv H. constructor.
    constructor ;auto.
    apply ext_equal_sym;auto.
  Qed.

  Fixpoint no_TFun_equal (t:typ) :
    no_TFun t = true ->
    forall v1 v2, ext_equal t v1 v2 -> v1 = v2.
  Proof.
    destruct t; simpl; try auto.
    - intros.
      revert v1 v2 H0.
      induction v1 ; destruct v2 ; simpl; intros.
      + reflexivity.
      + specialize (H0 O); simpl in H0.
        inv H0.
      + specialize (H0 O); simpl in H0.
        inv H0.
      + f_equal. specialize (H0 O).
        simpl in H0. inv H0; auto.
        apply IHv1; auto.
        intros.
        specialize (H0 (S x)); simpl in H0; auto.
    - unfold eval_recordtyp.
      induction l ; simpl.
      intros. destruct v1,v2;auto.
      rewrite andb_true_iff.
      intros. destruct H; destruct a.
      destruct H0.
      destruct v1,v2.
      simpl in *.
      f_equal.
      destruct f,f0;f_equal.
      simpl in H0. apply no_TFun_equal;auto.
      eapply IHl; eauto.
    - discriminate.
  Qed.

  Lemma no_TFun_fo_typ (ty:typ):  no_TFun ty = true -> fo_typ ty = true.
  Proof.
    destruct ty; simpl; auto; try discriminate.
  Qed.


  Fixpoint ext_equal_refl (t:typ): forall  v,
      fo_typ t = true ->
      ext_equal t v v.
  Proof.
    destruct t; try reflexivity.
    - (* array *)
      simpl.
      intros.
      fold eval_typ.
      destruct (nth_error  v x); try constructor.
      apply ext_equal_refl;auto.
      apply no_TFun_fo_typ; auto.
    - (* record *)
      simpl.
      unfold eval_recordtyp.
      induction l.
      + simpl. auto.
      + simpl.
        destruct a. simpl.
        intros.
        rewrite andb_true_iff in H.
        destruct H as (FT & FR).
        split; auto.
        apply ext_equal_refl;auto.
        apply no_TFun_fo_typ; auto.
    - (* function *)
      intros.
      unfold eval_typ in v ; fold eval_typ in v.
      unfold ext_equal; fold ext_equal.
      unfold eval_typ ; fold eval_typ.
      simpl in H.
      rewrite andb_true_iff in H.
      destruct H as (TA & TR).
      induction l.
      {
        apply res_rel_refl.
        repeat intro. apply ext_equal_refl.
        apply no_TFun_fo_typ; auto.
        }
        {
          rewrite ext_fun_rw.
          destruct l.
          - intros.
            simpl in TA.
            rewrite andb_comm in TA.
            apply no_TFun_equal in H; auto.
            subst.
            apply res_rel_refl.
            repeat intro.
            apply ext_equal_refl.
            apply no_TFun_fo_typ; auto.
          - intros.
            simpl in TA.
            rewrite andb_true_iff in TA.
            destruct TA as (TA & TRST).
            apply no_TFun_equal in H; auto.
            subst.
            apply IHl.
            auto.
        }
  Qed.


  Lemma ext_equal_fo_equal :forall (ty:typ),
    forall v1 v2
           (FO: fo_typ ty = true)
           (EQ : ext_equal  ty v1 v2), ext_equal_fo ty v1 v2.
  Proof.
    destruct ty; try (simpl; auto; fail).
    - intros.
      simpl.
      simpl in FO.
      change (no_TFun (TArray ty) = true) in FO.
      apply (no_TFun_equal _ FO v1 v2 EQ).
    - intros.
      change (no_TFun (TRecord i l) = true) in FO.
      apply (no_TFun_equal _ FO). simpl. apply EQ.
    -   unfold fo_typ.
        unfold eval_typ ; fold eval_typ.
        unfold ext_equal_fo.
        unfold ext_equal; fold ext_equal.
        induction l.
        {
          simpl. intros.
          inv EQ. constructor.
          f_equal.
          eapply no_TFun_equal;auto.
        }
        {
          intros.
          simpl.
          destruct l.
          + intros.
            simpl in EQ.
            assert (ext_equal a v v).
            {
              apply ext_equal_refl.
              simpl in FO. apply no_TFun_fo_typ. rewrite andb_true_iff in FO.
              rewrite andb_true_iff in FO. tauto.
            }
            apply EQ in H.
            inv H. constructor.
            f_equal.
            apply no_TFun_equal; auto.
            rewrite andb_true_iff in FO. tauto.
          +
            intro.
            apply IHl.
            simpl in FO.
            simpl.
            rewrite! andb_true_iff in *. tauto.
            rewrite ext_fun_rw in EQ.
            apply EQ.
            apply ext_equal_refl.
            rewrite! andb_true_iff in FO.
            apply no_TFun_fo_typ. simpl in FO.
            rewrite andb_true_iff in FO.
            tauto.
        }
  Qed.


  Definition propt : Type := string * value abs_typ_impl.

  Definition cast {t1 t2: typ} := @Types.typ_cast t1 t2 abs_typ_impl.

  Definition same_value (v1 v2 : value abs_typ_impl) :=
    match v1 , v2 with
    | Val _ ty vty , Val _ t2 v2 =>
        match typ_eq_dec t2 ty with
        | left EQ => ext_equal ty (cast EQ v2) vty
        | _   => False
        end
    end.


  Definition has_property (ge : genv abs_typ_impl) (p : propt) :=
    exists v', genv_get abs_typ_impl ge (fst p) = OK v' /\ same_value (snd p) v'.

  (** Prove that [eval_prog_rec] only updates the global environment.
      However, existing definitions are never  overwritten. *)

  Definition env_preserve_defs (ge1 ge2: genv abs_typ_impl) :=
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
      genv_update abs_typ_impl ge k v = OK ge' ->
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
      eval_def_const abs_typ_impl te ge x l ty = OK ge' ->
      env_preserve_defs ge ge'.
  Proof.
    unfold eval_def_const.
    intros.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    destruct (eval_literal abs_typ_impl te l); try discriminate.
    simpl in H.
    destruct (cast_value abs_typ_impl v t); try discriminate.
    simpl in H.
    eapply genv_update_preserve_defs;eauto.
  Qed.

  Lemma eval_def_fun_preserve_defs : forall arch te ge x f ge',
      eval_def_fun arch abs_typ_impl te ge x f = OK ge' ->
      env_preserve_defs ge ge'.
  Proof.
    unfold eval_def_fun.
    intros.
    destruct (build_fun_value arch abs_typ_impl te ge (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f)); try discriminate.
    simpl in H.
    eapply genv_update_preserve_defs;eauto.
  Qed.


  Lemma eval_prog_rec_preserve_defs :
    forall arch prog te ge  te' ge'
           (EVAL: eval_prog_rec arch abs_typ_impl te ge prog = OK (te', ge')),
      env_preserve_defs ge ge'.
  Proof.
    induction prog.
    - simpl; intros. inv EVAL. apply env_preserve_defs_refl.
    - simpl; intros.
      destruct a.
      + destruct (eval_def_type te i a); try discriminate.
        simpl in EVAL.
        eapply IHprog in EVAL;eauto.
      + destruct (eval_def_const abs_typ_impl te ge i l b) eqn:EQN; try discriminate.
        simpl in EVAL.
        eapply IHprog in EVAL;eauto.
        eapply eval_decl_const_preserve_defs in EQN; eauto.
        eapply env_preserve_defs_trans; eauto.
      +  destruct (eval_def_fun arch abs_typ_impl te ge i f) eqn:EQN; try discriminate.
         simpl in EVAL.
         eapply IHprog in EVAL;eauto.
         eapply eval_def_fun_preserve_defs in EQN;eauto.
         eapply env_preserve_defs_trans;eauto.
      + eauto.
      + destruct (eval_decl_const abs_typ_impl te ge i b); try discriminate.
        simpl in EVAL ; eauto.
      + destruct (eval_decl_fun abs_typ_impl te ge i l b); try discriminate.
        simpl in EVAL; eauto.
  Qed.

  Lemma genv_update_gss : forall ge ge' id v,
      genv_update abs_typ_impl ge id v = OK ge' ->
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
           (EVAL: eval_prog_rec arch abs_typ_impl te ge prog = OK (te', ge'))
           (GET : genv_get abs_typ_impl ge x = OK v),
      genv_get abs_typ_impl ge' x = OK v.
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
      eval_prog_rec arch abs_typ_impl te ge prog = OK (te', ge') ->
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
      eval_prog_rec arch abs_typ_impl te' ge' p2 = OK (te'',ge'') ->
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


  Definition val_of_value (v: value abs_typ_impl) : # (typeof_value abs_typ_impl v) :=
    match v with
    | Val _ _ v => v
    end.

  Definition eq_value (vl: value abs_typ_impl) (t:typ) (v: #t) :=
    same_value vl (Val _ t v).

  Definition check_value (v: res (value abs_typ_impl)) (ty:typ) (prop : value abs_typ_impl) :=
    match v with
    | OK v' => match cast_value abs_typ_impl v' ty with
               | OK v' => eq_value prop ty v'
               |  _    => False
               end
    | _    => False
    end.


  Definition generate_const_obligation (te : Typing.tenv) (x:ident) (l:Syntax.literal) (ty:btyp)
    (prop : value abs_typ_impl) : res Prop :=
    let* ty' := Typing.btyp_to_typ te ty in
    eret (check_value (eval_literal abs_typ_impl te l) ty' prop).


  Definition get_prop (s:ident) (props : list propt) :=
    match props with
    | nil => fail
    | (s',p)::props' => if String.eqb s s' then
                          eret (p,props')
                        else fail
    end.


  Fixpoint vars_of_expr (vars : STree.t unit) (e:expr)  : STree.t unit :=
    match e with
    | ETrue  | EFalse  |EInt32 _ _ | EInt64 _ _ | EConstr _ _ => vars
    | EVar id _ => STree.set id tt vars
    | ECast e _ => vars_of_expr vars e
    | EUnaryOp _ e _ => vars_of_expr vars e
    | EBinaryOp _ e1 e2 _ | EArrayGet e1 e2 _ => vars_of_expr (vars_of_expr vars e1) e2
    | EArraySet e1 e2 e3 _ => vars_of_expr (vars_of_expr (vars_of_expr vars e1) e2) e3
    | ERecordProj e _ _ => vars_of_expr vars e
    | ERecordUpdate e1 _ e2 _ => vars_of_expr (vars_of_expr vars e1) e2
    | EDeepAccess e acc _ => vars_of_expr (List.fold_left vars_of_access acc vars) e
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
    end
  with vars_of_access (vars: STree.t unit) (acc:access) : STree.t unit :=
         match acc with
         | AcRecordField _ _ => vars
         | AcArrayIndex e _ => vars_of_expr vars e
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
    (prop : value abs_typ_impl) : res Prop :=
    if MergeSort.nodup String.leb String.eqb (List.map fst params)
    then
      let* tret' := Typing.btyp_to_typ te tret in
      let* params' := MapList.map_err (Typing.btyp_to_typ te) params in
      let vars     := vars_of_fun params e in
      let needed_checked := List.filter (fun '(k,_) => has_var k vars) checked in
      let o := forall ge,
          Forall (has_property ge) needed_checked ->
          let v := (build_funval arch abs_typ_impl te ge params' tret' e) in
          eq_value prop _ v in
      eret o
    else fail.

  Fixpoint genv_has_property (ge: genv abs_typ_impl)  (l:list propt) :=
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
    (prop : value abs_typ_impl) : res Prop :=
    if MergeSort.nodup String.leb String.eqb (List.map fst params)
    then
      let* tret' := Typing.btyp_to_typ te tret in
      let* params' := MapList.map_err (Typing.btyp_to_typ te) params in
      let vars     := vars_of_fun params e in
      let needed_checked := List.filter (fun '(k,_) => has_var k vars) checked in
      let ge := genv_has_property STree.empty needed_checked in
      if stree_equal vars ge
      then
        let o :=
          let v := (build_funval arch abs_typ_impl te ge params' tret' e) in
          eq_value prop _ v in
        eret o
      else Error (MSG "Def fun " :: MSG f :: nil)
    else Error (MSG "Def fun " :: MSG f :: nil).

  Definition eq_env (keys: STree.t unit) (le le': genv abs_typ_impl) (ge ge' : genv abs_typ_impl) :=
    forall x,
      STree.get x le   = None ->
      STree.get x le'   = None ->
      STree.get x keys = Some tt ->
      option_rel same_value (STree.get x ge) (STree.get x ge').

  Definition eq_env_all (ge ge' : genv abs_typ_impl) :=
    forall x,  option_rel same_value (STree.get x ge) (STree.get x ge').

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




  Lemma same_value_sym : forall v1 v2,
      same_value v1 v2 ->
      same_value v2 v1.
  Proof.
    unfold same_value.
    destruct v1,v2;auto.
    destruct (typ_eq_dec t0 t); try tauto.
    subst. destruct (typ_eq_dec t t); try congruence.
    intros.
    apply ext_equal_sym.
    assert (e = eq_refl) by (apply Eqdep_dec.UIP_dec ; apply typ_eq_dec).
    subst. assumption.
  Qed.

  Fixpoint ext_equal_trans (t:typ) : forall v1 v2 v3,
      ext_equal t v1 v2 -> ext_equal t v2 v3 -> ext_equal t v1 v3.
  Proof.
    destruct t; try congruence.
    - simpl;intros.
      specialize (H x).
      specialize (H0 x).
      inv H ; inv H0; try congruence.
      + constructor.
      + constructor ;auto.
        rewrite <- H2 in H. inv H.
        eapply ext_equal_trans;eauto.
    - simpl; intros.
      unfold eval_recordtyp in *.
      induction l ; simpl in *.
      +  auto.
      + destruct a.
        simpl in *.
        split.
        destruct H,H0.
        eapply ext_equal_trans;eauto.
        eapply IHl with (v2:=snd v2).
        tauto. tauto.
    - unfold eval_typ ; fold eval_typ.
      unfold ext_equal; fold ext_equal.
      induction l.
      { simpl.
        intros.
        eapply res_rel_trans;eauto.
        }
        {
          intros.
          destruct l.
          - simpl in *.
            intros.
            specialize (H _ _ H1).
            eapply res_rel_trans; eauto.
            eapply H0.
            eapply ext_equal_trans.
            apply ext_equal_sym. apply H1. apply H1.
          - rewrite ext_fun_rw.
            rewrite ext_fun_rw in H.
            rewrite ext_fun_rw in H0.
            intros.
            specialize (H _ _ H1).
            eapply IHl;eauto.
            apply H0.
            eapply ext_equal_trans. apply ext_equal_sym. apply H1.
            auto.
        }
  Qed.

  Lemma same_value_refl : forall x,
      fo_typ (typeof_value abs_typ_impl x) = true ->
      same_value x x.
  Proof.
    unfold same_value.
    destruct x.
    destruct (typ_eq_dec t t);try congruence.
    assert (e = eq_refl).
    { apply Eqdep_dec.UIP_dec.
      apply typ_eq_dec.
    } subst.
    unfold cast,typ_cast, eq_rect_r,eq_rect. simpl.
    apply ext_equal_refl.
  Qed.

  Lemma same_value_refl' : forall x y,
      fo_typ (typeof_value abs_typ_impl x) = true ->
      x = y ->
      same_value x y.
  Proof.
    intros. subst.
    apply same_value_refl.
    auto.
  Qed.


  Lemma same_value_trans : forall v1 v2 v3,
      same_value v1 v2 -> same_value v2 v3 ->
      same_value v1 v3.
  Proof.
    unfold same_value.
    destruct v1,v2,v3.
    destruct (typ_eq_dec t0 t); try tauto.
    subst.
    destruct (typ_eq_dec t1 t); try tauto.
    subst.
    change (cast eq_refl v0) with v0.
    change (cast eq_refl v1) with v1.
    intros.
    eapply ext_equal_trans;eauto.
  Qed.

  Lemma res_rel_refl : forall {A : Type} (P : A -> A -> Prop),
      (forall x, P x x) ->
      forall x, res_rel P x x.
  Proof.
    intros.
    destruct x; constructor.
    apply H.
  Qed.



  Lemma get_cast_fo_typ : forall  ty t r,
      get_cast abs_typ_impl ty t = OK r ->
      no_TFun ty = true /\ no_TFun t = true.
  Proof.
    unfold get_cast.
    destruct ty,t; try discriminate; simpl; split; reflexivity.
  Qed.



  Lemma ext_equal_eval_cast : forall ty x y t,
      ext_equal ty x y ->
      res_rel (ext_equal t) (eval_cast abs_typ_impl ty x t) (eval_cast abs_typ_impl ty y t).
  Proof.
    unfold eval_cast.
    intros.
    destruct (get_cast abs_typ_impl ty t) eqn:C; try constructor.
    apply get_cast_fo_typ in C as (F1 & F2).
    simpl.
    apply no_TFun_equal in H; auto.
    subst.
    apply res_rel_refl. intros. apply ext_equal_refl.
    apply no_TFun_fo_typ; auto.
  Qed.

  Lemma res_rel_cast_typ_refl : forall ti tf v,
      fo_typ ti = true ->
      res_rel (ext_equal tf) (@cast_typ abs_typ_impl ti v tf) (@cast_typ abs_typ_impl ti v tf).
  Proof.
    intros.
    unfold cast_typ.
    destruct (typ_eq_dec tf ti).
    subst. apply res_rel_refl.
    intros. apply ext_equal_refl. auto.
    constructor.
  Qed.

  Lemma ext_equal_cast_typ : forall ti tf v1 v2,
      ext_equal ti v1 v2 ->
      res_rel (ext_equal tf) (cast_typ abs_typ_impl v1 tf) (cast_typ abs_typ_impl v2 tf).
  Proof.
    unfold cast_typ.
    intros. destruct (typ_eq_dec tf ti); try constructor.
    subst.
    constructor. auto.
  Qed.


  Lemma ext_equal_eval_unary_op : forall op ti x y tf,
      ext_equal ti x y ->
      res_rel (ext_equal tf) (eval_unary_op abs_typ_impl op ti x tf)
        (eval_unary_op abs_typ_impl op ti y tf).
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

  Lemma ext_equal_bool_op : forall op t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf) (bool_op abs_typ_impl op t1 t2 v1 v2 tf) (bool_op abs_typ_impl op t1 t2 v1' v2' tf).
  Proof.
    unfold bool_op.
    destruct t1,t2; try constructor.
    intros. simpl in *. subst.
    apply ext_equal_cast_typ. reflexivity.
  Qed.

  Lemma ext_equal_int_op : forall op32 op64 t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf) (int_op abs_typ_impl op32 op64 t1 t2 v1 v2 tf) (int_op abs_typ_impl op32 op64 t1 t2 v1' v2' tf).
  Proof.
    unfold int_op.
    destruct t1,t2; try constructor.
    - intros. simpl in *. subst.
      destruct signedness_eq_dec.
      apply ext_equal_cast_typ. reflexivity.
      constructor.
    - intros. simpl in *. subst.
      destruct signedness_eq_dec.
      apply ext_equal_cast_typ. reflexivity.
      constructor.
  Qed.

  Lemma ext_equal_ecast_typ : forall ti tf v1 v2,
      res_rel (ext_equal ti) v1 v2 ->
      res_rel (ext_equal tf) (@ecast_typ abs_typ_impl ti v1 tf) (@ecast_typ abs_typ_impl ti v2 tf).
  Proof.
    intros.
    unfold ecast_typ.
    destruct (typ_eq_dec tf ti). subst.
    apply H.
    constructor.
  Qed.

  Lemma ext_equal_int_ops : forall op32s op32u op64s op64u t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf) (int_op_s abs_typ_impl op32s op32u op64s op64u t1 t2 v1 v2 tf)
        (int_op_s abs_typ_impl op32s op32u op64s op64u t1 t2 v1' v2' tf).
  Proof.
    unfold int_op_s.
    destruct t1,t2; try constructor.
    - intros.
      destruct s,s0; try constructor.
      apply ext_equal_ecast_typ.
      simpl in *. subst.
      apply res_rel_refl; auto.
      apply ext_equal_ecast_typ.
      simpl in *. subst.
      apply res_rel_refl; auto.
    - intros.
      destruct s,s0; try constructor.
      apply ext_equal_ecast_typ.
      simpl in *. subst.
      apply res_rel_refl; auto.
      apply ext_equal_ecast_typ.
      simpl in *. subst.
      apply res_rel_refl; auto.
  Qed.


  Lemma ext_equal_int_eq_neq : forall (b:bool) t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf)
        (int_eq_neq abs_typ_impl b eqb Int.eq Int64.eq
           (fun (elems : list Syntax.ident) (v0 v3 : Benum.enum elems) =>
              if Benum.enum_eq_dec v0 v3 then true else false) t1 t2 v1 v2 tf)
        (int_eq_neq abs_typ_impl b eqb Int.eq Int64.eq
           (fun (elems : list Syntax.ident) (v0 v3 : Benum.enum elems) =>
              if Benum.enum_eq_dec v0 v3 then true else false) t1 t2 v1' v2'
           tf).
  Proof.
    destruct t1,t2; try constructor.
    - simpl. intros; subst.
      apply ext_equal_cast_typ.
      simpl. reflexivity.
    - simpl. intros; subst.
      destruct (signedness_eq_dec s s0).
      apply ext_equal_cast_typ.
      simpl. reflexivity.
      constructor.
    - simpl. intros; subst.
      destruct (signedness_eq_dec s s0).
      apply ext_equal_cast_typ.
      simpl. reflexivity.
      constructor.
    - intros.
      unfold int_eq_neq.
      destruct (typ_eq_dec (TEnum i l) (TEnum i0 l0)); try constructor.
      apply ext_equal_cast_typ.
      simpl in *. subst.
      reflexivity.
  Qed.


  Lemma ext_equal_cmp_op : forall cmp32s cmp32u cmp64s cmp64u t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf) (cmp_op abs_typ_impl cmp32s cmp32u cmp64s cmp64u t1 t2 v1 v2 tf)
        (cmp_op abs_typ_impl cmp32s cmp32u cmp64s cmp64u t1 t2 v1' v2' tf).
  Proof.
    intros.
    destruct t1,t2; try constructor.
    - unfold cmp_op.
      destruct s,s0;simpl; try constructor.
      simpl in *. subst.
      apply ext_equal_cast_typ;reflexivity.
      simpl in *. subst.
      apply ext_equal_cast_typ;reflexivity.
    - unfold cmp_op.
      destruct s,s0;simpl; try constructor.
      simpl in *. subst.
      apply ext_equal_cast_typ;reflexivity.
      simpl in *. subst.
      apply ext_equal_cast_typ;reflexivity.
  Qed.


  Lemma ext_equal_eval_binary_op : forall op t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf) (eval_binary_op abs_typ_impl op t1 t2 v1 v2 tf) (eval_binary_op abs_typ_impl op t1 t2 v1' v2' tf).
  Proof.
    intros.
    unfold eval_binary_op; destruct op.
    - apply ext_equal_bool_op; auto.
    - apply ext_equal_bool_op; auto.
    - apply ext_equal_bool_op; auto.
    - apply ext_equal_int_op; auto.
    - apply ext_equal_int_op; auto.
    - apply ext_equal_int_op; auto.
    - apply ext_equal_int_ops; auto.
    - apply ext_equal_int_ops; auto.
    - apply ext_equal_int_op; auto.
    - apply ext_equal_int_op; auto.
    - apply ext_equal_int_op; auto.
    - apply ext_equal_int_op; auto.
    - apply ext_equal_int_ops; auto.
    - apply ext_equal_int_eq_neq; auto.
    - apply ext_equal_int_eq_neq; auto.
    - apply ext_equal_cmp_op;auto.
    - apply ext_equal_cmp_op;auto.
    - apply ext_equal_cmp_op;auto.
    - apply ext_equal_cmp_op;auto.
  Qed.


  Lemma ext_equal_array_get : forall arch ta a1 a2  ti i1 i2 ty,
      ext_equal ta a1 a2 ->
      ext_equal ti i1 i2 ->
      res_rel (ext_equal ty)
        (eval_array_get arch abs_typ_impl ta a1 ti i1 ty)
        (eval_array_get arch abs_typ_impl ta a2 ti i2 ty).
  Proof.
    intros.
    unfold eval_array_get.
    destruct ta; try constructor.
    destruct arch.
    - destruct (typ_eq_dec ti (TInt32 Unsigned)); subst; try constructor.
      simpl in *.
      subst.
      unfold eq_rect_r, eq_rect; simpl.
      eapply ext_equal_ecast_typ.
      unfold Barray.get.
      rewrite ext_equal_valid_index with (a2:= a2).
      destruct (valid_index a2 (Intop.U64.of_u32 i2)).
      specialize (H (Intop.U64.to_nat (Intop.U64.of_u32 i2))).
      fold eval_typ in *.
      inv H; simpl.  constructor.
      constructor;auto.
      constructor.
      repeat intro. auto.
    - destruct (typ_eq_dec ti (TInt64 Unsigned)); subst; try constructor.
      simpl in *.
      subst.
      unfold eq_rect_r, eq_rect; simpl.
      eapply ext_equal_ecast_typ.
      unfold Barray.get.
      rewrite ext_equal_valid_index with (a2:= a2).
      destruct (valid_index a2  i2).
      specialize (H (Intop.U64.to_nat i2)).
      fold eval_typ in *.
      inv H; simpl ; try constructor.
      auto. constructor.
      repeat intro. auto.
  Qed.

  Lemma nth_error_set_rec : forall {T:Type}  n (a:list T) v x,
      nth_error (set_rec a n v) x =
        if (Nat.eq_dec x  n) && (n <? length a)%nat then Some v
        else nth_error a x.
  Proof.
    induction n.
    - simpl.
      destruct a; intros.
      destruct (Nat.eq_dec x 0); auto.
      destruct (Nat.eq_dec x 0); auto.
      simpl. subst. reflexivity.
      simpl. destruct x; simpl; auto.
      congruence.
    - simpl.
      intros.
      destruct a.
      + simpl.
        rewrite nth_error_nil.
        rewrite andb_comm.
        reflexivity.
      + destruct x.
        simpl. reflexivity.
        simpl.
        rewrite IHn.
        destruct (Nat.eq_dec x n).
        simpl. subst.
        assert ((n <? Datatypes.length a)%nat = (S n <? S (Datatypes.length a))%nat).
        {
          lia.
        }
        rewrite H. reflexivity.
        simpl. reflexivity.
  Qed.


  Lemma ext_eq_array_set : forall te a1 a2 v1 v2 i,
      ext_eq_array te a1 a2 ->
      ext_equal te v1 v2 ->
      res_rel (ext_eq_array te) (set a1 i v1) (set a2 i v2).
  Proof.
    unfold set.
    intros.
    rewrite (ext_equal_valid_index _ _ _ H i).
    destruct (valid_index a2 i); try constructor.
    unfold ext_eq_array.
    intros.
    generalize (Intop.U64.to_nat i) as n.
    assert (LEN : length a1 = length a2).
    {
      apply ext_equal_length; auto.
    }
    specialize (H x).
    intros.
    rewrite! nth_error_set_rec.
    rewrite LEN.
    destruct (Nat.eq_dec x n && (n <? Datatypes.length a2)%nat).
    constructor ; auto.
    apply H.
  Qed.


  Lemma ext_equal_array_set : forall arch ta a1 a2 ti i1 i2 tv v1 v2 ty,
      ext_equal ta a1 a2 ->
      ext_equal ti i1 i2 ->
      ext_equal tv v1 v2 ->
      res_rel (ext_equal ty) (eval_array_set arch abs_typ_impl ta a1 ti i1 tv v1 ty)
        (eval_array_set arch abs_typ_impl ta a2 ti i2 tv v2 ty).
  Proof.
    intros.
    unfold eval_array_set.
    destruct ta; try constructor.
    destruct arch.
    - destruct (typ_eq_dec ti (TInt32 Unsigned));
        try constructor.
      destruct (typ_eq_dec ta tv); try constructor.
      subst.
      unfold eq_rect_r,eq_rect. simpl.
      simpl in H0. subst.
      simpl in H.
      apply ext_equal_ecast_typ.
      change (ext_eq_array tv a1 a2) in H.
      apply ext_eq_array_set with (v1:=v1) (v2:=v2) (i:= (Intop.U64.of_u32 i2)) in H; auto.
    - destruct (typ_eq_dec ti (TInt64 Unsigned));
        try constructor.
      destruct (typ_eq_dec ta tv); try constructor.
      subst.
      unfold eq_rect_r,eq_rect. simpl.
      simpl in H0. subst.
      simpl in H.
      change (ext_eq_array tv a1 a2) in H.
      apply ext_equal_ecast_typ.
      apply ext_eq_array_set with (v1:=v1) (v2:=v2) (i:= i2) in H; auto.
  Qed.


  Lemma ext_equal_same_value : forall t x y,
      ext_equal t x y ->
      same_value (Val abs_typ_impl t y) (Val abs_typ_impl t x).
  Proof.
    unfold same_value.
    intros. destruct (typ_eq_dec t t); try congruence.
    assert (e = eq_refl) by (apply Eqdep_dec.UIP_dec ; apply typ_eq_dec).
    subst. apply H.
  Qed.

  Lemma ext_equal_eval_record_proj : forall tr x y f ty,
      ext_equal tr x y ->
      res_rel (ext_equal ty) (eval_record_project abs_typ_impl tr x f ty) (eval_record_project abs_typ_impl tr y f ty).
  Proof.
    intros.
    unfold eval_record_project.
    destruct tr; try constructor.
    simpl in H.
    revert x y H.
    induction l.
    - constructor.
    - intros.
      simpl in x,y.
      destruct a.
      destruct x,y.
      destruct f0,f1.
      simpl in H.
      destruct (String.eqb f i0) eqn:EQ.
      + unfold eval_record_project_aux.
        simpl.
        unfold good_proj,cast_typof_field.
        simpl.
        rewrite EQ.
        simpl. apply ext_equal_cast_typ;auto.
        tauto.
      + unfold eval_record_project_aux.
        simpl.
        unfold good_proj,cast_typof_field.
        simpl.
        rewrite EQ.
        simpl. apply IHl; auto.
        tauto.
  Qed.



  Lemma equal_upd_record_aux :
    forall fields r1 r2 f ty v1 v2,
      equal_record ext_equal fields r1 r2 ->
      ext_equal ty v1 v2 ->
      res_rel (equal_record ext_equal fields) (eval_record_upd_aux abs_typ_impl fields r1 f ty v1)
        (eval_record_upd_aux abs_typ_impl fields r2 f ty v2).
  Proof.
    unfold eval_recordtyp.
    intros.
    unfold eval_record_upd_aux.
    repeat match goal with
           | |- context[bool_dec ?B1 ?B2] => destruct (bool_dec B1 B2)
           end ; try constructor.
    destruct (typeof_field_typ abs_typ_impl f ty  fields e1) ; try constructor.
    apply no_TFun_equal in H0; auto.
    change  (ext_equal (TRecord "" fields) r1 r2) in H.
    apply no_TFun_equal in H.
    subst.
    change  (equal_record ext_equal fields)
      with (ext_equal (TRecord "" fields)).
    apply ext_equal_refl.
    simpl.
    clear - e.
    { induction fields;simpl;auto.
      simpl in *.
      rewrite andb_true_iff in *.
      destruct e.
      split; auto.
    }
    simpl.
    { clear - e. induction  fields ; simpl in * ;auto.
      rewrite andb_true_iff in *.
      intuition.
    }
  Qed.




  Lemma ext_equal_eval_record_update : forall tr r1 r2 tv v1 v2 f ty,
      ext_equal tr r1 r2 ->
      ext_equal tv v1 v2 ->
      res_rel (ext_equal ty)
        (eval_record_update abs_typ_impl tr r1 f tv v1 ty)
        (eval_record_update abs_typ_impl tr r2 f tv v2 ty).
  Proof.
    intros.
    unfold eval_record_update.
    destruct tr; try constructor.
    simpl in H.
    eapply equal_upd_record_aux with (f:= f) in H; eauto.
    eapply ext_equal_ecast_typ;eauto.
  Qed.



  Inductive eq_access_value (arch:archi): access_value arch abs_typ_impl -> access_value arch abs_typ_impl -> Prop :=
  | eq_access_field : forall k, eq_access_value arch (AcvalRecordField arch abs_typ_impl k) (AcvalRecordField arch abs_typ_impl k)
  | eq_access_index : forall v1 v2, res_rel (ext_equal (typof_index arch)) v1 v2 -> eq_access_value arch (AcvalArrayIndex arch abs_typ_impl v1)
                                                                                      (AcvalArrayIndex arch abs_typ_impl v2).

  Lemma res_rel_ifthenelse : forall x y t1 t2 v1 v2  v1' v2' tr,
      ext_equal TBool x y ->
      res_rel (ext_equal t1) v1 v1' ->
      res_rel (ext_equal t2) v2 v2' ->
      res_rel (ext_equal tr)
        (eval_ifthenelse abs_typ_impl x t1 v1 t2 v2 tr)
        (eval_ifthenelse abs_typ_impl y t1 v1' t2 v2' tr).
  Proof.
    intros.
    unfold eval_ifthenelse.
    simpl in H. subst.
    destruct y.
    apply ext_equal_ecast_typ;auto.
    apply ext_equal_ecast_typ;auto.
  Qed.


  Fixpoint get_var_of_expr_acc (x:string) (e:expr): forall acc,
      STree.get x acc = Some tt ->
      STree.get x (vars_of_expr acc e) = Some tt.
  Proof.
    destruct e; simpl; auto.
    - intros. rewrite STree.gsspec.
      destruct (STree.elt_eq x i); auto.
    - induction l; simpl; auto.
      intros.
      apply IHl.
      destruct a; simpl;auto.
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
      rewrite get_var_of_expr_case.
      symmetry. rewrite get_var_of_expr_case.
      symmetry.
      assert (STree.get x (fold_left vars_of_access l acc) = Some tt
              <->
                (STree.get x acc = Some tt \/
                   STree.get x (fold_left vars_of_access l STree.empty) = Some tt)).
      revert acc.
      induction l ; simpl; auto.
      + intros. rewrite STree.gempty.
        intuition congruence.
      + intros.
        rewrite IHl.
        symmetry.
        rewrite IHl.
        destruct a; simpl.
        rewrite STree.gempty.
        intuition congruence.
        rewrite (get_var_of_expr_case x e0 acc).
        intuition congruence.
      + tauto.
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
  Qed.




  Lemma get_vars_of_access : forall acs acc,
    forall x, STree.get x (fold_left vars_of_access  acs acc ) = Some tt <->
                (STree.get x (fold_left vars_of_access acs STree.empty) = Some tt
                 \/ STree.get x acc = Some tt).
  Proof.
    induction acs.
    - simpl.
      intros. rewrite STree.gempty.
      intuition congruence.
    - simpl.
      intros.
      rewrite IHacs.
      symmetry.
      rewrite IHacs.
      destruct a; simpl.
      rewrite! STree.gempty.
      intuition congruence.
      symmetry.
      rewrite get_var_of_expr_case.
      tauto.
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


  Lemma eq_env_of_access : forall acs acc le le' ge ge',
      eq_env (fold_left vars_of_access  acs acc ) le le' ge ge' ->
      eq_env (fold_left vars_of_access acs STree.empty) le le' ge ge' /\
        eq_env acc le le' ge ge'.
  Proof.
    unfold eq_env.
    split; intros.
    apply H; auto.
    rewrite get_vars_of_access.
    tauto.
    apply H;auto.
    rewrite get_vars_of_access.
    tauto.
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
      ext_equal ty v1 v2 ->
      eq_env_all (lenv_update abs_typ_impl le k (Val abs_typ_impl ty v1))
        (lenv_update abs_typ_impl le' k (Val abs_typ_impl ty v2)).
  Proof.
    unfold eq_env_all,lenv_update.
    intros.
    rewrite! STree.gsspec.
    destruct (STree.elt_eq x k).
    constructor. apply ext_equal_same_value.
    apply ext_equal_sym. auto.
    apply H.
  Qed.

  Lemma  ext_equal_eval_match : forall te x y tr l1 l2,
      ext_equal te x y ->
      Forall2 (fun x y => fst x = fst y /\ res_rel (ext_equal tr) (snd x) (snd y))  l1 l2 ->
      res_rel (ext_equal tr) (eval_match abs_typ_impl te x tr l1) (eval_match abs_typ_impl te y tr l2).
  Proof.
    intros.
    unfold eval_match.
    destruct te; try constructor.
    simpl in H. subst.
    induction H0.
    - simpl. constructor.
    - simpl.
      destruct x,y0.
      simpl in *. destruct H; subst.
      destruct p0.
      destruct (Benum.make_enum l i0); simpl.
      + destruct (Benum.enum_eq e y); auto.
      + constructor.
      + exact H1.
  Qed.


  Lemma eq_env_remove : forall x e le le' v1 v2 ge ge',
      eq_env (STree.remove x (vars_of_expr STree.empty e)) le le' ge ge' ->
      eq_env (vars_of_expr STree.empty e) (lenv_update abs_typ_impl le x v1) (lenv_update abs_typ_impl le' x v2) ge ge'.
  Proof.
    unfold eq_env;intros.
    unfold lenv_update in *.
    rewrite STree.gsspec in *.
    destruct (STree.elt_eq x0 x); try congruence.
    apply H; auto.
    rewrite STree.gro;auto.
  Qed.





  Lemma res_rel_ecast_typ_refl : forall ti tf v,
      fo_typ ti = true ->
      res_rel (ext_equal tf) (@ecast_typ abs_typ_impl ti v tf) (@ecast_typ abs_typ_impl ti v tf).
  Proof.
    intros.
    unfold ecast_typ.
    destruct (typ_eq_dec tf ti).
    subst. destruct v.
    constructor. apply ext_equal_refl; auto.
    constructor. constructor.
  Qed.

  Lemma same_value_cast_value : forall x y ty,
      same_value x y ->
      res_rel (ext_equal ty) (cast_value abs_typ_impl x ty) (cast_value abs_typ_impl y ty).
  Proof.
    unfold same_value. destruct x,y.
    intros. destruct (typ_eq_dec t0 t); try discriminate.
    subst. unfold cast_value.
    change (cast eq_refl v0) with v0 in H.
    unfold cast_typ.
    destruct (typ_eq_dec ty t); try constructor.
    subst.  unfold eq_rect_r,eq_rect.
    simpl. constructor;auto. apply ext_equal_sym. auto.
    tauto.
  Qed.

  Lemma ext_equal_eval_app_res :
    let Ftyp := fun ty : typ => res (# ty) in
    let Pred := fun ty : typ => res_rel (ext_equal ty) in
    forall l0 t x y x0 y0 ty,
      ext_equal (TFun l0 t) x y ->
      DList.Forall2 Ftyp Pred l0 x0 y0 ->
      res_rel (ext_equal ty) (eval_app_res abs_typ_impl l0 t x x0 ty)
        (eval_app_res abs_typ_impl l0 t y y0 ty).
  Proof.
    intros.
    unfold ext_equal in H ; fold ext_equal in H.
    unfold eval_typ in x,y; fold eval_typ in x,y.
    revert x y H.
      induction H0.
      - simpl. intros. apply ext_equal_ecast_typ;auto.
      - simpl.
        destruct lt.
        + intros.
          unfold Pred in H.
          inv H. constructor.
          simpl. apply ext_equal_ecast_typ.
          apply H1. auto.
        + intros.
          unfold Pred in H. inv H.
          constructor.
          simpl.
          apply IHForall2.
          auto.
  Qed.




  Fixpoint eq_genv_eval_expr (arch:archi) (te:Typing.tenv)  (ge ge':genv abs_typ_impl) (ty:typ) (e:expr) : forall le le',
      eq_env (vars_of_expr (STree.empty) e) le le' ge ge' ->
      eq_env_all le le'  ->
      res_rel (ext_equal ty) (eval_expr arch abs_typ_impl te ge le ty e)
        (eval_expr arch abs_typ_impl te ge' le' ty e).
  Proof.
    specialize (eq_genv_eval_expr arch te ge ge').
    destruct e; intros; simpl; try (apply res_rel_cast_typ_refl;reflexivity).
    - unfold eval_constr.
      destruct (Typing.tenv_get_constr_typ te i); try constructor.
      simpl. destruct (Typing.tenv_get_edef te i0); try constructor.
      simpl. destruct (bool_dec (existsb (String.eqb i) l) true);try constructor.
      apply res_rel_cast_typ_refl;reflexivity.
    - unfold eval_var.
      unfold lenv_get.
      unfold eq_env in H0.
      specialize (H0 i).
      inv H0.
      simpl.
      unfold eq_env in H. unfold genv_get.
      simpl in H.
      specialize (H i).
      rewrite STree.gss in H.
      symmetry in H2. symmetry in H3.
      specialize (H H2 H3 eq_refl).
      inv H.
      constructor.
      simpl. apply same_value_cast_value; auto.
      simpl. apply same_value_cast_value; auto.
    - destruct (Typing.btyp_to_typ te b); try reflexivity.
      simpl.
      destruct (typof_expr te e); try constructor.
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
      destruct (typof_expr te e1); try constructor.
      destruct (typof_expr te e2); try constructor.
      simpl.
      generalize (eq_genv_eval_expr t e1 le le' (eq_env_vars_of_expr_acc _ _ _ _ _ _ H) H0).
      generalize (eq_genv_eval_expr t0 e2 le le' (eq_env_vars_of_expr _ _ _ _ _ _ H) H0).
      intros E2 E1.
      inv E1 ; try constructor.
      simpl. inv E2 ; try constructor.
      simpl.
      apply ext_equal_eval_binary_op; auto.
    - simpl in H.
      destruct (typof_expr te e1); try constructor.
      destruct (typof_expr te e2); try constructor.
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
      destruct (typof_expr te e1); try constructor.
      destruct (typof_expr te e2); try constructor.
      destruct (typof_expr te e3); try constructor.
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
      destruct (typof_expr te e); try constructor.
      simpl.
      specialize (eq_genv_eval_expr t e le le' H H0).
      inv eq_genv_eval_expr; try constructor.
      simpl.
      apply ext_equal_eval_record_proj; auto.
    -
      simpl in H.
      apply eq_env_split in H as (EQ1 & EQ2).
      destruct (typof_expr te e1);try constructor.
      destruct (typof_expr te e2);try constructor.
      simpl.
      generalize (eq_genv_eval_expr t e1 le le' EQ2 H0).
      generalize (eq_genv_eval_expr t0 e2 le le' EQ1 H0).
      intros E2 E1.
      inv E1 ; try constructor.
      simpl. inv E2 ; try constructor.
      simpl.
      apply ext_equal_eval_record_update; auto.
    - simpl in H.
      apply eq_env_split in H as (EQ1 & EQ2).
      destruct (typof_expr te e);try constructor.
      simpl.
      generalize (eq_genv_eval_expr t e le le' EQ1 H0).
      intro E1.
      assert (ALL : Forall2 (eq_access_value arch)
                      (map (eval_access_expr arch abs_typ_impl te ge le) l)
                      (map (eval_access_expr arch abs_typ_impl te ge' le') l)).
      {
        induction l.
        -  simpl. constructor.
        - simpl.
          constructor.
          {
            destruct a.
            - simpl.
              constructor.
            - simpl.
              simpl in EQ2.
              apply eq_env_of_access in EQ2 as (EQ0 & EQACC).
              specialize (eq_genv_eval_expr (typof_index arch) e0 le le' EQACC H0).
              inv eq_genv_eval_expr.
              constructor.
              simpl. constructor.
              constructor. constructor;auto.
          }
          simpl in EQ2.
          apply eq_env_of_access in EQ2 as (EQ2 & EQ3).
          apply IHl; auto.
      }
      clear - E1 ALL.
      revert E1.
      generalize (eval_expr arch abs_typ_impl te ge le t e) as e1.
      generalize (eval_expr arch abs_typ_impl te ge' le' t e) as e2.
      revert t.
      induction ALL.
      +  simpl. intros.
         apply ext_equal_ecast_typ;auto.
      + simpl.
        intros.
        inv H.
        * destruct (typof_record_project t k);try constructor.
          simpl.
          inv E1. constructor.
          simpl.
          apply IHALL.
          apply ext_equal_eval_record_proj; auto.
        * destruct (typof_array t) ; try constructor.
          simpl.
          inv E1. constructor.
          simpl. inv H0. constructor.
          simpl.
          apply IHALL.
          apply ext_equal_array_get. auto.
          auto.
    -
      simpl in H.
      destruct (typof_expr te e); try constructor.
      simpl.
      apply eq_env_exprs in H as (EQ1 & EQ2).
      destruct t; try constructor.
      assert (E1 := eq_genv_eval_expr (TFun l0 t) e le le' EQ2  H0).
      inv E1.
      constructor.
      simpl.
      set (Ftyp := fun (ty:typ) => res (eval_typ abs_typ_impl ty)).
      set (Pred := fun ty => res_rel (ext_equal ty)).
      assert (res_rel (DList.Forall2 Ftyp Pred  _) (DList.map2 (eval_typ abs_typ_impl) (eval_expr arch abs_typ_impl te ge le) l l0)
                (DList.map2 (eval_typ abs_typ_impl) (eval_expr arch abs_typ_impl te ge' le') l l0)).
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
      inv H3; try constructor.
      simpl.
      clear - H2 H6.
      (*
    eapply ext_equal_ecast_typ.
    destruct l0.
    { simpl.
      assert (XO : x0 = DList.DNIL abs_typ_impl).
      { apply DList.dlist_nil. }
      assert (YO : y0 = DList.DNIL abs_typ_impl).
      { apply DList.dlist_nil. }
      rewrite XO. rewrite YO.
      apply H2.
    }
    {
      unfold ext_equal in H2 ; fold ext_equal in H2.
      unfold eval_typ in x,y; fold eval_typ in x,y.
      unfold eval_app.
      revert x y H2.
      induction H6.
      - simpl. auto.
      - simpl.
        intros.
        apply IHForall2.
        auto.
    } *)
      apply ext_equal_eval_app_res; auto.
    - simpl in H.
      apply eq_env_split in H as (EQ1 & EQ2).
      apply eq_env_split in EQ2 as (EQ2 & EQ3).
      generalize (eq_genv_eval_expr TBool e1 _ _ EQ3 H0).
      intros E1 ; inv E1; try constructor.
      simpl.
      destruct (typof_expr te e2); try constructor.
      destruct (typof_expr te e3); try constructor.
      simpl.
      generalize (eq_genv_eval_expr t e2 _ _ EQ2 H0).
      generalize (eq_genv_eval_expr t0 e3 _ _ EQ1 H0).
      intros E3 E2.
      apply res_rel_ifthenelse; auto.
    - simpl in H.
      apply eq_env_pattern in H.
      destruct (typof_expr te e); try constructor.
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
      destruct (typof_expr te e1); try constructor.
      simpl.
      apply eq_env_split in H as (EQ1 & EQ2).
      generalize (eq_genv_eval_expr t e1 le le' EQ1 H0).
      intro E1.
      inv E1.
      constructor.
      simpl.
      assert (LE : eq_env_all (lenv_update abs_typ_impl le i (Val abs_typ_impl t x))
                     (lenv_update abs_typ_impl le' i (Val abs_typ_impl t y))).
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
  (*    generalize (eq_genv_eval_expr e2 _ _ EQ1 LE).
    intro.
    inv H3. constructor.
    constructor ;auto.*)
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
      eq_env (vars_of_expr STree.empty e) (lenv_update abs_typ_impl le s v1)
        (lenv_update abs_typ_impl le' s v2) ge ge'.
  Proof.
    unfold eq_env;intros.
    unfold lenv_update in *.
    rewrite STree.gsspec in *.
    destruct (STree.elt_eq x s); try congruence.
    apply H;auto.
  Qed.

  Lemma eq_env_remove_params : forall {A: Type} (a:A)(lt:smaplist A) s vars le le' ge ge' v1 v2,
      eq_env (remove_params lt (STree.remove s vars)) le le' ge ge' ->
      eq_env (remove_params lt vars) (lenv_update abs_typ_impl le s v1)
        (lenv_update abs_typ_impl le' s v2) ge ge'.
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
      ext_fun ext_equal t (map snd lt) (build_funval_rec arch abs_typ_impl te ge le lt t e)
        (build_funval_rec arch abs_typ_impl te ge' le' lt t e).
  Proof.
    unfold vars_of_fun.
    induction lt.
    - simpl.
      intros.
      specialize (eq_genv_eval_expr arch te ge ge' t e le le' H H0).
      intro E1.
      inv E1.
      constructor.
      constructor.
      auto.
    -
      change (map snd (a :: lt))
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
        rewrite build_funval_rec_rw.
        eapply IHlt.
       apply eq_env_remove_params;auto.
       simpl in H. destruct a,p.
       simpl. auto.
       apply eq_env_all_lenv_update; auto.
  Qed.




  Lemma eq_value_trans : forall v ty v1 v2,
      eq_value v ty v1  ->
      ext_equal ty v1 v2 ->
      eq_value v ty v2.
  Proof.
    unfold eq_value.
    intros.
    unfold same_value in *.
    destruct v.
    destruct (typ_eq_dec ty t); try tauto.
    subst.
    change (cast eq_refl v1) with v1 in H.
    change (cast eq_refl v2) with v2.
    eapply ext_equal_trans; eauto.
    apply ext_equal_sym; auto.
  Qed.

  Lemma ext_fun_trans : forall t l f1 f2 f3,
      ext_fun ext_equal t l f1 f2 -> ext_fun ext_equal t l f2 f3 -> ext_fun ext_equal t l f1 f3.
  Proof.
    intros.
    change (ext_equal (TFun l t) f1 f3).
    eapply ext_equal_trans;eauto.
  Qed.

  Lemma genv_has_property_same : forall x ge' l acc v,
      STree.get x (genv_has_property acc l) = Some v ->
      Forall (has_property ge') l ->
      option_rel same_value (Some v) (STree.get x ge') \/ STree.get x acc = Some v.
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

  Lemma same_value_cast_typ_M : forall x y t,
      same_value x y ->
      res_rel (ext_equal t) (cast_typ_M abs_typ_impl t x) (cast_typ_M abs_typ_impl t y).
  Proof.
    unfold same_value.
    intros. destruct x,y.
    destruct (typ_eq_dec t1 t0); try tauto.
    subst.
    unfold cast_typ_M.
    destruct (typ_eq_dec t0 t); try constructor.
    subst. apply ext_equal_sym in H.
    apply H.
  Qed.

  Lemma map_err_nil : forall {A B:Type} (F : A -> res B) (l:list (string * A)),
      MapList.map_err F l = OK nil -> l = nil.
  Proof.
    induction l; simpl.
    - congruence.
    - intros.
      destruct a. destruct (F a); try discriminate.
      simpl in H.
      destruct (MapList.map_err F l) eqn:MR.
      simpl in H. inv H. discriminate.
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

  Lemma map_err_fst : forall (A B:Type) (F : A -> res B) (l1:smaplist A) (l2:smaplist B),
      MapList.map_err F l1  = OK l2 ->
      map fst l1 = map fst l2.
  Proof.
    induction l1;simpl;auto.
    - intros. inv H. reflexivity.
    - intros. destruct a.
      simpl. destruct (F a); try discriminate.
      simpl in H. destruct (MapList.map_err F l1) eqn:M;try discriminate.
      simpl in H. inv H.
      simpl. f_equal ;auto.
  Qed.

  Lemma generate_def_fun_obligation_impl : forall arch f te params tret e checked prop o',
      generate_def_fun_obligation' arch f te params tret e checked prop = OK o' ->
      exists o, generate_def_fun_obligation arch te params tret e checked prop = OK o /\
                  (o' -> o).
  Proof.
    unfold generate_def_fun_obligation', generate_def_fun_obligation.
    intros.
    destruct (MergeSort.nodup String.leb String.eqb
                (map fst params)); try discriminate.
    destruct (Typing.btyp_to_typ te tret); try discriminate.
    simpl in *.
    destruct (MapList.map_err (Typing.btyp_to_typ te) params)eqn:PARAM; try discriminate.
    simpl in *.
    set (ge :=         (genv_has_property STree.empty
                          (filter (fun '(k, _) => has_var k (vars_of_fun params e))
                             checked))) in *.
    destruct (stree_equal (vars_of_fun params e) ge) eqn:ALLKEY; try discriminate.
    inv H.
    eexists. split. eauto.
    intros.
    eapply eq_value_trans;eauto.
    unfold build_funval.
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
    destruct t0.
    - simpl.
      apply map_err_nil in PARAM. subst.
      generalize (eq_genv_eval_expr arch te ge ge0 t e STree.empty STree.empty EQENV eq_env_all_empty).
      intro EEXPR. inv EEXPR.
      constructor.
      constructor.
      assumption.
    - unfold ext_equal; fold ext_equal.
      unfold map; fold map.
      change ((snd p :: (fix map (l : list (string * typ)) : list typ := match l with
                                                                         | nil => nil
                                                                         | a :: t1 => snd a :: map t1
                                                                         end) t0))
        with (map snd (p :: t0)).
      eapply build_funval_rec_eq.
      eapply eq_env_fst with (v1 := params).
      eapply map_err_fst;eauto.
      auto.
      apply eq_env_all_empty.
  Qed.

  Definition is_checked (x:Syntax.ident) (checked:list propt) :=
    List.existsb (fun p => string_dec x (fst p)) checked.

  Definition generate_decl_const_obligation (te: Typing.tenv) (checked:list propt) (x:Syntax.ident) (bt:btyp) : res Prop :=
    let* ty := Typing.btyp_to_typ te bt in
    (*  if is_checked x checked then*)
    let* v := MapList.find_err string_dec x checked  in
    let P := typeof_value abs_typ_impl v = ty in
    eret P.

  Definition generate_decl_fun_obligation (te: Typing.tenv) (checked:list propt) (x:Syntax.ident) (params : list (Syntax.param_attr * btyp))
    (tret : btyp) : res Prop :=
    let* tparam := mmap (Typing.btyp_to_typ te) (map snd params)
    in let* tret' := Typing.btyp_to_typ te tret in
       let* v := MapList.find_err string_dec x checked  in
       let P := typeof_value abs_typ_impl v = TFun tparam tret' in
       eret P.

  (* Definition tenv_update_opt (te: Typing.tenv) (x: Syntax.ident) (fields : smaplist typ) :=
  let id := StringIndexed.index x in
  match PTree.get id te.(tenv_defs) with
  | None => eret (PTree.set id fields te)
  | Some _ => fail
  end. *)

  (* Definition obligation_def_type (te: Typing.tenv) (x:Syntax.ident) (fields : SMapList.t btyp) : res Typing.tenv :=
  let* fields' := fields_btyp_to_typ te fields in
  tenv_update_opt te x fields'. *)

  Definition obligation_def_type (te: Typing.tenv) (x: ident) (adt: adt_definition btyp) : res Typing.tenv :=
    eval_def_type te x adt.

  Fixpoint generate_obligations (arch:archi)  (te:Typing.tenv)
    (checked : list propt) (vc : list Prop) (p:program) (props : list propt) : res (list Prop) :=
    match p with
    | nil => match props with
             | nil => eret vc
             | _   => fail
             end
    | a :: prog' =>
        match a with
        | DefType a adt =>
            let* te' := obligation_def_type te a adt in
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
      get_prop s props = OK (p, props')  ->
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

  Definition incr_genv (ge ge': genv abs_typ_impl) (prog:program) :=
    (forall x v, STree.get x ge = Some v -> STree.get x ge' = Some v)
    /\
      forall x,
        In x (map ident_of_globdef (filter has_prop prog)) ->
        STree.get x ge' = None.

  Lemma incr_genv_def_const : forall x l ty prog ge0 ge,
      incr_genv ge0 ge (DefConst x l ty :: prog) ->
      genv_get abs_typ_impl ge x = fail.
  Proof.
    unfold incr_genv.
    intros.
    destruct H.
    unfold genv_get.
    rewrite H0. reflexivity.
    simpl. tauto.
  Qed.

  Lemma has_property_set : forall x v p ge,
      same_value v p ->
      has_property (STree.set x v ge) (x, p).
  Proof.
    unfold has_property.
    intros.
    unfold genv_get.
    simpl. rewrite STree.gss. exists v.
    split. reflexivity.
    apply same_value_sym. assumption.
  Qed.

  Lemma eq_value_same_value : forall p t v,
      eq_value p t v ->
      same_value p (Val abs_typ_impl t v).
  Proof.
    unfold eq_value,same_value.
    intros.
    destruct p; auto.
  Qed.


  Lemma generate_const_obligation_sound :
    forall te x l ty p (P:Prop) ge
           (GEN : generate_const_obligation te x l ty p = OK P)
           (GET : genv_get abs_typ_impl ge x = fail)
           (HOLD : P),
    exists ge',
      eval_def_const abs_typ_impl te ge x l ty = OK ge' /\
        has_property ge' (x,p).
  Proof.
    unfold generate_const_obligation.
    unfold eval_def_const.
    intros.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    simpl in GEN. inv GEN.
    unfold check_value in HOLD.
    destruct (eval_literal abs_typ_impl te l); try tauto.
    simpl in *.
    destruct (cast_value abs_typ_impl v t); try tauto.
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


  Lemma res_rel_ext_equal_eq : forall t v1 v2,
      fo_typ t = true ->
      v1 = v2 ->
      res_rel (ext_equal  t)
        v1 v2.
  Proof.
    intros.
    subst.
    destruct v2.
    constructor. apply ext_equal_refl; auto.
    constructor.
  Qed.


  (** For each program declaration,
    if the proof obligation holds then the evaluation succeeds and
    the declaration has the property *)

  Lemma generate_def_fun_obligation_sound :
    forall arch te x f checked ge p o
           (GEN : generate_def_fun_obligation arch te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p = OK o)
           (GET : genv_get abs_typ_impl ge x = fail)
           (ALL : Forall (has_property ge) checked)
           (HAS : o)
    ,
    exists ge',
      eval_def_fun arch abs_typ_impl te ge x f = OK ge' /\
        has_property ge' (x,p).
  Proof.
    unfold generate_def_fun_obligation.
    unfold eval_def_fun.
    unfold build_fun_value.
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
    destruct (@MapList.map_err string btyp typ (Typing.btyp_to_typ te) (Syntax.fn_params f)); try discriminate.
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
      forall v, MapList.find_err string_dec x checked = OK v ->
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
           (EVAL: eval_prog Ptr64 abs_typ_impl ge0 prog = OK (te,ge))
           (FO : fo_typ t = true)
           (HASP : has_property  ge  (s,Val abs_typ_impl t v)),
    exists
      v' : eval_typ abs_typ_impl t,
      (let* (_, ge0):= eval_prog Ptr64 abs_typ_impl ge0 prog
       in genv_get abs_typ_impl ge0 s) =
        OK (Val abs_typ_impl t v') /\ ext_equal_fo  t v' v.
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
           (GEN : generate_decl_const_obligation  te checked x bt = OK P)
           (ALL : Forall (has_property ge) checked)
           (HOLD: P)
    ,
    exists ge',
      eval_decl_const abs_typ_impl  te ge x bt = OK ge'.
  Proof.
    unfold generate_decl_const_obligation.
    unfold eval_decl_const.
    intros.
    destruct (Typing.btyp_to_typ te bt); try discriminate.
    simpl in GEN.
    destruct (MapList.find_err string_dec x checked) eqn:FIND ; try discriminate.
    simpl in GEN. inv GEN.
    apply has_property_find_err with (ge:=ge) in FIND;auto.
    simpl. unfold has_property in FIND.
    destruct FIND as (v' & GET& SV).
    simpl in SV. simpl in GET. rewrite GET.
    simpl. assert (typeof_value abs_typ_impl v' = t).
    { unfold same_value in SV.
      destruct v,v'. destruct (typ_eq_dec t1 t0); try tauto.
      simpl in *. congruence.
    }
    rewrite H. destruct (typ_eq_dec t t); try congruence.
    eexists ; reflexivity.
  Qed.

  Lemma generate_decl_fun_obligation_sound :
    forall te x tparams tret checked ge P
           (GEN : generate_decl_fun_obligation  te checked x tparams tret  = OK P)
           (ALL : Forall (has_property ge) checked)
           (HOLD: P)
    ,
    exists ge',
      eval_decl_fun abs_typ_impl  te ge x tparams tret = OK ge'.
  Proof.
    unfold generate_decl_fun_obligation.
    unfold eval_decl_fun.
    intros.
    destruct (mmap (Typing.btyp_to_typ te) (map snd tparams)); try discriminate.
    destruct (Typing.btyp_to_typ te tret); try discriminate.
    simpl in GEN.
    destruct (MapList.find_err string_dec x checked) eqn:FIND.
    simpl in GEN. inv GEN.
    unfold bind. unfold Errors.bind.
    apply has_property_find_err with (ge:=ge)  in FIND; auto.
    destruct FIND as (v' & GET & HAS).
    simpl in GET.
    rewrite GET.
    assert (typeof_value abs_typ_impl v' = (TFun l t)).
    {
      simpl in HAS. destruct v,v'; simpl in *.
      destruct (typ_eq_dec t1 t0); try congruence.
      tauto.
    }
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

  Definition wf_env (ge: genv abs_typ_impl) (prog: program) :=
    forall d, In d prog -> has_def d = true -> genv_get abs_typ_impl ge (ident_of_globdef d) = fail.

  Lemma wf_env_tail : forall ge d prog,
      wf_env ge (d :: prog) ->
      wf_env ge prog.
  Proof.
    unfold wf_env ; simpl in *.
    intros.
    apply H; auto.
  Qed.

  Lemma genv_gsspec : forall x v ge y,
      genv_get abs_typ_impl (STree.set x v ge) y =
        if string_dec x y
        then OK v else genv_get abs_typ_impl ge y.
  Proof.
    unfold genv_get, STree.get,STree.set.
    intros.
    rewrite PTree.gsspec.
    destruct (string_dec x y).
    - subst.
      destruct (peq (StringIndexed.index y) (StringIndexed.index y));try congruence.
      reflexivity.
    - destruct (peq (StringIndexed.index y) (StringIndexed.index x)); try discriminate; auto.
      apply Ctypesdefs.ident_of_string_injective in e.
      congruence.
  Qed.

  Lemma wf_env_DefConst :
    forall te ge ge' x l ty prog
           (DUP : NoDup (map ident_of_globdef (DefConst x l ty :: prog)))
           (WF : wf_env ge (DefConst x l ty :: prog))
           (EVAL : eval_def_const abs_typ_impl te ge x l ty = OK ge'),
      wf_env ge' prog.
  Proof.
    unfold eval_def_const.
    intros.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    simpl in EVAL.
    destruct (eval_literal abs_typ_impl te l) eqn:EL; try discriminate.
    simpl in EVAL.
    destruct (cast_value abs_typ_impl v t); try discriminate.
    unfold wf_env in *.
    intros.
    unfold genv_update in EVAL.
    destruct (genv_get abs_typ_impl ge x) eqn:GET; try discriminate.
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
           (EVAL : eval_def_fun arch abs_typ_impl te ge x f = OK ge'),
      wf_env ge' prog.
  Proof.
    unfold eval_def_fun.
    intros.
    unfold build_fun_value in EVAL.
    destruct (MapList.nodup Ident.eq_dec (Syntax.fn_params f)); try discriminate.
    destruct (Typing.btyp_to_typ te (Syntax.fn_return f)); try discriminate.
    simpl in EVAL.
    destruct (@MapList.map_err string btyp typ (Typing.btyp_to_typ te) (Syntax.fn_params f)); try discriminate.
    simpl in EVAL.
    unfold wf_env in *.
    intros.
    unfold genv_update in EVAL.
    destruct (genv_get abs_typ_impl ge x) eqn:GET; try discriminate.
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

  (*
Lemma generate_obligations_sound :
  forall arch prog te checked props ol
         (ND : NoDup (map ident_of_globdef prog))
         (GEN : generate_obligations arch  te checked vc prog props = OK ol)
         (OBL : Forall (fun p => p) ol)
  ,
  forall ge,
    wf_env ge prog ->
    Forall (has_property ge) checked ->
    exists te' ge', eval_prog_rec arch abs_typ_impl te ge prog = OK (te',ge') /\
                      Forall (has_property ge') props.
Proof.
  induction prog.
  - simpl.
    intros. destruct props ; try discriminate.
    do 2 eexists. split. reflexivity.
    constructor.
  - simpl.
    destruct a.
    + intros. destruct (eval_def_type te tid fields); try discriminate.
      simpl in *.
      eapply IHprog in GEN ; eauto.
      inv ND ; auto.
      apply wf_env_tail in H; auto.
    + intros.
      destruct (get_prop x props) eqn:GP; try discriminate.
      destruct p as (p,props').
      simpl in GEN.
      apply get_prop_inv in GP.
      destruct (generate_const_obligation te x l ty p) eqn:CO; try discriminate.
      simpl in GEN.
      destruct (generate_obligations arch te ((x, p) :: checked) prog props') eqn:GO; try discriminate.
      simpl in GEN. inv GEN.
      destruct  (generate_const_obligation_sound _ _ _ _ _ _ ge CO) as (ge' & EF & HP ).
      { unfold wf_env in H.
        apply (H (DefConst x l ty)).
        simpl. tauto. reflexivity.
      }
      { inv  OBL ; auto. }
      rewrite EF. simpl.
      apply IHprog with (ge:=ge') in GO; auto.
      destruct GO as (te2 & ge2 & EQ & ALL).
      do 2 eexists ; split; eauto.
      constructor.
      apply eval_prop_rec_preserve_props with (p1' := (x,p)::nil) in EQ.
      inv EQ ; auto.
      constructor ; auto.
      auto.
      inv ND ; auto.
      inv OBL; auto.
      eapply wf_env_DefConst; eauto.
      constructor ;auto.
      eapply eval_prop_rec_preserve_props with (p1 := (DefConst x l ty)::nil).
      apply H0. simpl. rewrite EF. reflexivity.
      Unshelve. apply arch.
    + intros.
      destruct (get_prop x props) eqn:GP; try discriminate.
      destruct p as (p,props').
      simpl in GEN.
      apply get_prop_inv in GP.
      destruct (generate_def_fun_obligation  arch te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p) eqn:CO; try discriminate.
      simpl in GEN.
      destruct (generate_obligations arch te ((x, p) :: checked) prog props') eqn:GO; try discriminate.
      simpl in GEN. inv GEN.
      destruct  (generate_def_fun_obligation_sound _ _ x _ _  ge _ _ CO) as (ge' & EF & HP ).
      { unfold wf_env in H.
        apply (H (DefFun x f )).
        simpl. tauto. reflexivity.
      }
      auto.
      { inv  OBL ; auto. }
      rewrite EF. simpl.
      apply IHprog with (ge:=ge') in GO; auto.
      destruct GO as (te2 & ge2 & EQ & ALL).
      do 2 eexists ; split; eauto.
      constructor.
      apply eval_prop_rec_preserve_props with (p1' := (x,p)::nil) in EQ.
      inv EQ ; auto.
      constructor ; auto.
      auto.
      inv ND ; auto.
      inv OBL; auto.
      eapply wf_env_DefFun; eauto.
      constructor ;auto.
      eapply eval_prop_rec_preserve_props with (p1 := (DefFun x f)::nil).
      apply H0. simpl. rewrite EF. reflexivity.
    + intros.
      eapply IHprog;eauto.
      inv ND;auto.
      eapply wf_env_tail;eauto.
    + intros.
      destruct (generate_decl_const_obligation te checked x ty) eqn:DECL ; try discriminate.
      simpl in GEN.
      destruct (generate_obligations arch te checked prog props) eqn:GO; try discriminate.
      simpl in GEN; inv GEN.
      destruct (generate_decl_const_obligation_sound te x ty checked ge P DECL); auto.
      inv OBL; auto.
      rewrite H1. simpl.
      eapply IHprog;eauto.
      inv ND;auto.
      inv OBL;auto.
      eapply wf_env_tail;eauto.
    + intros.
      destruct (generate_decl_fun_obligation  te checked x tparams tret) eqn:DECL ; try discriminate.
      simpl in GEN.
      destruct (generate_obligations arch te checked prog props) eqn:GO; try discriminate.
      simpl in GEN; inv GEN.
      destruct (generate_decl_fun_obligation_sound te x tparams tret checked ge P DECL); auto.
      inv OBL; auto.
      rewrite H1. simpl.
      eapply IHprog;eauto.
      inv ND;auto.
      inv OBL;auto.
      eapply wf_env_tail;eauto.
Qed.
   *)


  Lemma generate_obligations_incl :
    forall arch prog te checked props ol vc
           (GEN : generate_obligations arch  te checked vc prog props = OK ol),
    forall x, In x vc -> In x ol.
  Proof.
    induction prog.
    - simpl. destruct props. intros.
      inv GEN. auto.
      discriminate.
    - simpl.
      destruct a; intros.
      + destruct (obligation_def_type te i a); try discriminate.
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
  (* unfold obligation_def_type,eval_def_type.
  intros. destruct (fields_btyp_to_typ te fields); try reflexivity.
  simpl. unfold tenv_update_opt, Typing.tenv_update.
  unfold Typing.tenv_get. unfold STree.get.
  destruct (te ! (StringIndexed.index tid)); simpl; auto. *)
  Qed.



  Lemma generate_obligations_sound :
    forall arch prog te checked props ol vc
           (ND : NoDup (map ident_of_globdef prog))
           (GEN : generate_obligations arch  te checked vc prog props = OK ol)
           (OBL : Forall (fun p => p) ol)
    ,
    forall ge,
      wf_env ge prog ->
      Forall (has_property ge) checked ->
      exists te' ge', eval_prog_rec arch abs_typ_impl te ge prog = OK (te',ge') /\
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
        destruct (eval_def_type te i a); try discriminate.
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
      eval_prog_rec arch abs_types_impl te ge p1 = OK (te1, ge1) ->
      eval_prog_rec arch abs_types_impl te1 ge1 p2 = OK (te2, ge2) ->
      eval_prog_rec arch abs_types_impl te ge (p1++p2)%list = OK (te2, ge2).
  Proof.
    induction p1; simpl.
    - intros. inv H. auto.
    - destruct a; intros.
      + destruct (eval_def_type te i a); try discriminate.
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
             | nil => eret (nil,nil)
             |  _  => fail
             end
    | a :: prog' => match kind_of_globdef a with
                    | KindType => partition_props prog' props
                    | KindDecl => match props with
                                  | nil => fail
                                  | p1::props' => let* (decl,defs) := partition_props prog' props' in
                                                  eret (p1::decl,defs)
                                  end
                    | KindDef  => match props with
                                  | nil => fail
                                  | p1::props' => let* (decl,defs) := partition_props prog' props' in
                                                  eret (decl,p1::defs)
                                  end
                    end
    end.


End S.
