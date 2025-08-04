(**  Generation of verification conditions to prove equivalence between
     Shallow and Deep embedding. *)

From Coq Require Import String List.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Target Monads Error Barray Brecord Types Barocq Maps2 MergeSort.
From compcert Require Import Coqlib.
Open Scope string_scope.

Section S.
  (** is-it already defined elsewhere? *)
  Context {A B: Type}.
  Variable f : A -> B -> bool.

  Fixpoint forall2b  (l1: list A) (l2: list B) {struct l1} : bool :=
    match l1 , l2 with
  | nil , nil => true
  | e1::l1, e2::l2 => if f e1 e2 then forall2b l1 l2 else false
  | _ , _ => false
  end.

End S.

(** Use [nodup] using MergeSort
Fixpoint nodup {A: Type} (eqb: A -> A -> bool) (l:list A) : bool :=
  match l with
  | nil => true
  | e::l => match nodup eqb l with
            | true => List.forallb (fun x =>  negb (eqb e x)) l
            | false => false
            end
  end.

Lemma nodup_NoDup :
  forall A eqb
         (EQB : forall x, eqb x x = true)
         (l:list A),
    nodup eqb l = true -> NoDup l.
Proof.
  induction l.
  -  constructor.
  - simpl.
    destruct (nodup eqb l); try discriminate.
    intros.
    constructor; auto.
    rewrite forallb_forall in H.
    intro.
    specialize (H _ H0).
    rewrite EQB in H. discriminate.
Qed.
*)



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

  Definition propt : Type := string * (forall t : typ, # t -> Prop).

  Definition has_property (ge : genv abs_typ_impl) (p : propt) :=
    exists t (v: #t), genv_get abs_typ_impl ge (fst p) = OK (Val _ t v) /\ (snd p) t v.

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
    intros. destruct (eval_literal abs_typ_impl te l); try discriminate.
    simpl in H. destruct v.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    simpl in H. destruct (typ_eq_dec t t0); try discriminate.
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
      + destruct (eval_def_type te tid fields); try discriminate.
        simpl in EVAL.
        eapply IHprog in EVAL;eauto.
      + destruct (eval_def_const abs_typ_impl te  ge x l ty) eqn:EQN; try discriminate.
        simpl in EVAL.
        eapply IHprog in EVAL;eauto.
        eapply eval_decl_const_preserve_defs in EQN; eauto.
        eapply env_preserve_defs_trans; eauto.
    +  destruct (eval_def_fun arch abs_typ_impl te  ge x f) eqn:EQN; try discriminate.
       simpl in EVAL.
       eapply IHprog in EVAL;eauto.
       eapply eval_def_fun_preserve_defs in EQN;eauto.
       eapply env_preserve_defs_trans;eauto.
    + eauto.
    + destruct (eval_decl_const abs_typ_impl te ge x ty); try discriminate.
      simpl in EVAL ; eauto.
    + destruct (eval_decl_fun abs_typ_impl te ge x tparams tret); try discriminate.
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
  destruct H0 as (t&v&GET &SND).
  do 2 eexists. split.
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


Definition generate_const_obligation (te : Typing.tenv) (x:ident) (l:Syntax.literal) (ty:btyp)
  (prop : (forall (t:typ), # t -> Prop)) : res Prop :=
  let* ty' := Typing.btyp_to_typ te ty in
  eret (forall (u:unit),
        match eval_literal abs_typ_impl te l with
        | OK vv =>
            let 'Val _ tv v := vv in
            if typ_eqb tv ty' then
              prop tv v else False
        | _    => False
    end).

Definition get_prop (s:ident) (props : list propt) :=
  match props with
  | nil => fail
  | (s',p)::props' => if String.eqb s s' then
                        eret (p,props')
                      else fail
  end.


Fixpoint vars_of_expr (vars : STree.t unit) (e:expr)  : STree.t unit :=
  match e with
  | ETrue | EFalse |EInt32 _ _ | EInt64 _ _ => vars
  | EVar id => STree.set id tt vars
  | ECast e _ => vars_of_expr vars e
  | EUnaryOp _ e => vars_of_expr vars e
  | EBinaryOp _ e1 e2 | EArrayGet e1 e2 => vars_of_expr (vars_of_expr vars e1) e2
  | EArraySet e1 e2 e3 => vars_of_expr (vars_of_expr (vars_of_expr vars e1) e2) e3
  | ERecordProj e _ => vars_of_expr vars e
  | ERecordUpdate e1 _ e2 => vars_of_expr (vars_of_expr vars e1) e2
  | EDeepAccess e acc => vars_of_expr (List.fold_left vars_of_access acc vars) e
  | EApp e l   => List.fold_left vars_of_expr l (vars_of_expr vars e)
  | EIfThenElse e1 e2 e3 => vars_of_expr (vars_of_expr (vars_of_expr vars e1) e2) e3
  | ELetIn x e1 e2 => (* Ignore scopes - should remove x from e2 *)
      vars_of_expr (vars_of_expr vars e1) e2
  end
  with vars_of_access (vars: STree.t unit) (acc:access) : STree.t unit :=
         match acc with
         | AcRecordField _ => vars
         | AcArrayIndex e => vars_of_expr vars e
         end.

Definition has_var (s:string) (vars:STree.t unit) :=
  match STree.get s vars with
  | None => false
  | Some _ => true
  end.


Definition generate_def_fun_obligation (arch:archi) (te:Typing.tenv)  (params : SMapList.t btyp) (tret : btyp) (e : expr) (checked : list propt)
  (prop : (forall (t:typ), # t -> Prop)) : res Prop :=
  if MergeSort.nodup String.leb String.eqb (List.map fst params)
  then
    let* tret' := Typing.btyp_to_typ te tret in
    let* params' := SMapList.map_err (Typing.btyp_to_typ te) params in
    let vars     := vars_of_expr STree.empty e in
    let needed_checked := List.filter (fun '(k,_) => has_var k vars) checked in
    let o := forall ge,
        Forall (has_property ge) needed_checked ->
        let v := (build_funval arch abs_typ_impl te ge params' tret' e) in
        prop _ v in
    eret o
  else fail.

Definition is_checked (x:Syntax.ident) (checked:list propt) :=
  List.existsb (fun p => string_dec x (fst p)) checked.

Definition generate_decl_const_obligation (te: Typing.tenv) (checked:list propt) (x:Syntax.ident) (bt:btyp) : res Prop :=
  let* ty := Typing.btyp_to_typ te bt in
(*  if is_checked x checked then*)
  let P := forall ge, Forall (has_property ge) checked -> has_property ge (x, fun ty' v => ty' =  ty) in
  eret P.

Definition generate_decl_fun_obligation (te: Typing.tenv) (checked:list propt) (x:Syntax.ident) (params : list (Syntax.param_attr * btyp))
  (tret : btyp) : res Prop :=
  let* tparam := mmap (Typing.btyp_to_typ te) (map snd params)
  in let* tret' := Typing.btyp_to_typ te tret in
  let P := forall ge, Forall (has_property ge) checked -> has_property ge (x, fun ty' v => ty' = TFun tparam tret') in
  eret P.

Definition tenv_update_opt (te: Typing.tenv) (x: Syntax.ident) (fields : SMapList.t typ) :=
  let id := StringIndexed.index x in
  match PTree.get id te with
  | None => eret (PTree.set id fields te)
  | Some _ => fail
  end.

Definition obligation_def_type (te: Typing.tenv) (x:Syntax.ident) (fields : SMapList.t btyp) : res Typing.tenv :=
  let* fields' := fields_btyp_to_typ te fields in
  tenv_update_opt te x fields'.


Fixpoint generate_obligations (arch:archi)  (te:Typing.tenv)
  (checked : list propt) (vc : list Prop) (p:program) (props : list propt) : res (list Prop) :=
    match p with
    | nil => match props with
             | nil => eret vc
             | _   => fail
             end
    | a :: prog' =>
        match a with
        | DefType a fields  => let* te' := obligation_def_type te a fields in generate_obligations arch  te' checked vc prog' props
        | DefConst x l ty    =>
            let* (p,props') := get_prop x props in
            let*  o  := generate_const_obligation te x l ty p in
            generate_obligations arch  te ((x,p)::checked) (o::vc) prog'  props'
        | DefFun y f =>
            let* (p,props') := get_prop y props in
            let*  o   := generate_def_fun_obligation arch te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p in
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

Lemma has_property_set : forall x ty v p ge,
    p ty v ->
    has_property (STree.set x (Val abs_typ_impl ty v) ge) (x, p).
Proof.
  unfold has_property.
  intros.
  unfold genv_get.
  unfold STree.get.
  simpl.
  unfold STree.set.
  rewrite PTree.gss.
  simpl. do 2 eexists ; split; eauto.
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
  simpl in *.
  inv GEN.
  specialize (HOLD tt).
  destruct (eval_literal abs_typ_impl te l); try discriminate.
  destruct v. simpl.
  destruct (typ_eqb t0 t) eqn:EQ; try discriminate.
  apply typ_eqb_true in EQ. subst.
  destruct (typ_eq_dec t t); try congruence.
  unfold genv_update.
  rewrite GET.
  simpl. eexists.
  split.  reflexivity.
  apply has_property_set; auto.
  tauto. tauto.
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

Lemma SMapList_NoDup : forall (V: Type) (l: SMapList.t V),
    NoDup (map fst l)  ->
    SMapList.nodup l = true.
Proof.
  induction l; simpl;auto.
  destruct a.
  simpl.
  intros.
  inv H.
  destruct (SMapList.mem k l) eqn:MEM; auto.
  exfalso.
  {
    apply H2.
    clear - MEM.
    induction l ; simpl; auto.
    discriminate.
    simpl in MEM. destruct a.
    destruct (SMapList.key_eq k0 k); simpl; try congruence.
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

  

Lemma nodup_eq : forall (V: Type) (l:SMapList.t V) ,
    MergeSort.nodup String.leb String.eqb (map fst l) = true ->
    SMapList.nodup l = true.
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
          (@map (prod SMapList.key btyp) SMapList.key
             (@fst SMapList.key btyp)
             (@Syntax.fn_params expr f))
) eqn:DUP; try discriminate.
  apply nodup_eq in DUP. rewrite DUP.
  destruct (Typing.btyp_to_typ te (Syntax.fn_return f)); try discriminate.
  simpl in GEN.
  simpl.
  destruct (SMapList.map_err (Typing.btyp_to_typ te) (Syntax.fn_params f)); try discriminate.
  simpl in GEN; simpl.
  inv GEN.
  unfold genv_update.
  rewrite GET.
  simpl. eexists.
  split.  reflexivity.
  apply has_property_set; auto.
  apply HAS.
  rewrite Forall_forall.
  intros.
  rewrite filter_In in H.
  destruct H.
  rewrite Forall_forall in ALL. auto.
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
  inv GEN.
  simpl.
  apply HOLD in ALL.
  destruct ALL as (ty & v & GET & ALL).
  simpl in GET.
  rewrite GET.
  simpl in ALL. subst.
  simpl.
  destruct (typ_eq_dec t t); try discriminate.
  eexists;eauto.
  congruence.
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
  inv GEN.
  unfold bind. unfold Errors.bind.
  apply HOLD in ALL.
  destruct ALL as (ty & v & GET & ALL).
  simpl in GET.
  rewrite GET.
  simpl in ALL. subst.
  unfold Barocq.typeof_value.
  destruct (typ_eq_dec (TFun l t) (TFun l t)); try congruence.
  eexists.
  reflexivity.
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
  destruct (eval_literal abs_typ_impl te l) eqn:EL; try discriminate.
  simpl in EVAL.
  destruct v.
  destruct (Typing.btyp_to_typ te ty); try discriminate.
  simpl in EVAL.
  destruct (typ_eq_dec t t0); try discriminate.
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
  destruct (SMapList.nodup (Syntax.fn_params f)); try discriminate.
  destruct (Typing.btyp_to_typ te (Syntax.fn_return f)); try discriminate.
  simpl in EVAL.
  destruct (SMapList.map_err (Typing.btyp_to_typ te) (Syntax.fn_params f)); try discriminate.
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
    + destruct (obligation_def_type te tid fields); try discriminate.
      simpl in GEN.
      eapply IHprog; eauto.
    +       destruct (get_prop x props) eqn:GP; try discriminate.
      destruct p as (p,props').
      simpl in GEN.
      apply get_prop_inv in GP.
      subst.
      destruct (generate_const_obligation te x l ty p); try discriminate.
      simpl in GEN.
      eapply IHprog in GEN;eauto.
      simpl. tauto.
    + destruct (get_prop x props) eqn:GP; try discriminate.
      destruct p as (p,props').
      simpl in GEN.
      apply get_prop_inv in GP.
      subst.
      destruct (generate_def_fun_obligation arch te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p); try discriminate.
      simpl in GEN.
      eapply IHprog in GEN;eauto.
      simpl. tauto.
    + eapply IHprog;eauto.
    +
      destruct (generate_decl_const_obligation te checked x ty); try discriminate.
      simpl in GEN.
      eapply IHprog in GEN;eauto.
      simpl. tauto.
    +
      destruct (generate_decl_fun_obligation te checked x tparams tret); try discriminate.
      simpl in GEN.
      eapply IHprog in GEN;eauto.
      simpl. tauto.
Qed.

Lemma obligation_def_type_eq : forall te tid fields ,
    obligation_def_type te tid fields = eval_def_type te tid fields.
Proof.
  unfold obligation_def_type,eval_def_type.
  intros. destruct (fields_btyp_to_typ te fields); try reflexivity.
  simpl. unfold tenv_update_opt, Typing.tenv_update.
  unfold Typing.tenv_get. unfold STree.get.
  destruct (te ! (StringIndexed.index tid)); simpl; auto.
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
      destruct (eval_def_type te tid fields); try discriminate.
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
      destruct  (generate_const_obligation_sound _ _ _ _ _ _ ge CO) as (ge' & EF & HP ).
      { unfold wf_env in H.
        apply (H (DefConst x l ty)).
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
      apply eval_prog_rec_preserve_properties with (props := (x,p)::nil) in EQ.
      inv EQ ; auto.
      constructor ; auto.
      auto.
      inv ND ; auto.
      eapply wf_env_DefConst; eauto.
      constructor ;auto.
      eapply eval_prog_rec_preserve_properties with (prog := (DefConst x l ty)::nil).
      apply H0. simpl. rewrite EF. reflexivity.
      Unshelve. apply arch.
    + intros.
      destruct (get_prop x props) eqn:GP; try discriminate.
      destruct p as (p,props').
      simpl in GEN.
      apply get_prop_inv in GP.
      destruct (generate_def_fun_obligation  arch te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p) eqn:CO; try discriminate.
      simpl in GEN.
      destruct  (generate_def_fun_obligation_sound _ _ x _ _  ge _ _ CO) as (ge' & EF & HP ).
      { unfold wf_env in H.
        apply (H (DefFun x f )).
        simpl. tauto. reflexivity.
      }
      auto.
      { apply generate_obligations_incl with (x:=P) in GEN.
        rewrite Forall_forall in OBL. apply OBL;auto.
        simpl. tauto.
      }
      rewrite EF. simpl.
      apply IHprog with (ge:=ge') in GEN; auto.
      destruct GEN as (te2 & ge2 & EQ & ALL).
      do 2 eexists ; split; eauto.
      subst.
      constructor.
      apply eval_prog_rec_preserve_properties with (props := (x,p)::nil) in EQ.
      inv EQ ; auto.
      constructor ; auto.
      auto.
      inv ND ; auto.
      eapply wf_env_DefFun; eauto.
      constructor ;auto.
      eapply eval_prog_rec_preserve_properties with (prog := (DefFun x f)::nil).
      apply H0. simpl. rewrite EF. reflexivity.
    + intros.
      eapply IHprog;eauto.
      inv ND;auto.
      eapply wf_env_tail;eauto.
    + intros.
      destruct (generate_decl_const_obligation te checked x ty) eqn:DECL ; try discriminate.
      destruct (generate_decl_const_obligation_sound te x ty checked ge P DECL); auto.
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
      destruct (generate_decl_fun_obligation te checked x tparams tret) eqn:DECL ; try discriminate.
      destruct (generate_decl_fun_obligation_sound te x tparams tret checked ge P DECL); auto.
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

End S.
