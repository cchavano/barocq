(** Must alias for imp1 *)
From compcert Require Import Coqlib Maps.
Require Import Uint63.
Require Import String FMapInterface FMapList ZArith Int ListSet.
From BarocqComp Require Import Error DList Maps2 Types Imp1 Graph Typing Utils Pp.
From Coq Require Import FMapPositive.
Require Import Syntax.
From BarocqComp Require Import Imp1Imp Imp1ElimAlias.
Import Typed.
Import Imp1.Typed.


Section TREE.
  Variable Edge : forall ty (p1:ptr ty) (e:cedge) ty' (p2:ptr ty'), Prop.

  Definition is_global_tree : Prop :=
    forall ty1 p1 ty1' p1' e1 e1' ty2 p2,
      Edge ty1 p1 e1 ty2 p2 ->
      Edge ty1' p1' e1' ty2 p2 ->
      exists EQ, cast (f_equal ptr EQ) p1' = p1.


(*  Inductive is_tree : forall (ty:typ) (p1:ptr ty), Prop :=
  | MkTree : forall ty1 p1,
          (forall ty2 e p2, Edge ty1 p1 e ty2 p2 -> unique_parent ty1 p1 ty2 p2 -> is_tree ty2 p2) ->
          is_tree ty1 p1. *)

  Inductive clo : forall (tyi : typ) (pi:ptr tyi)  (tyr:typ) (pr:ptr tyr), Prop :=
  | clo_refl : forall tyi (pi:ptr tyi), clo tyi pi tyi pi
  | clo_step : forall tyi (pi:ptr tyi) e tyr (pr:ptr tyr),
      Edge tyi pi e tyr pr -> clo tyi pi  tyr pr
  | clo_trans : forall tyi pi ty' p' tyr pr,
      clo tyi pi ty' p' ->
      clo ty' p' tyr pr ->
      clo tyi pi tyr pr.

  Definition disjoint (ty1:typ) (p1: ptr ty1) (ty2: typ) (p2 : ptr ty2) : Prop :=
    forall ty p, clo ty1 p1 ty p -> clo ty2 p2 ty p -> False.

End TREE.

Inductive le_KVar : KVar -> KVar -> Prop :=
| leKDead : forall x, le_KVar x KDead
| le_Keq  : forall x, le_KVar x x.


Section S.

  Variable arch: Target.archi.
  Variable abs : Maps.PMap.t Type.
  Variable te  : tenv.

  Section GAMMA.

  Variable ge  : genv abs.

    Fixpoint eval_expr  (ge:genv abs) (ev:env) (m:mem abs) (tyr : typ) (e:GEXPR.t) : res (val tyr) :=
    match e with
(*    | GEXPR.Atm a    => eval_atom arch abs te ge ev m tyr a*)
    | GEXPR.Var id   => get_lvar ev id tyr
    | GEXPR.Get e lb => let* e := eval_expr ge ev m tyr e in
                        match lb with
                        | EdgeLabel.Top => fail
                        | EdgeLabel.Field fid =>
                            eval_mem_access abs m e (CField fid) tyr
                        | EdgeLabel.Index i  =>
                            let* i := eval_atom arch abs te ge ev m tyr i in
                            let* i  := index_of_val arch i in
                            eval_mem_access  abs m e (CIndex i) tyr
                        end
    end.

  Definition empty_genv : genv abs := fun _ => fail.



  Inductive ptr_of_memval : forall (ty:typ) (mv:mval abs ty) (e:cedge) (ty': typ) (p:ptr ty'), Prop :=
  | PtrArray : forall ty a i vl p, Barray.get a i = OK vl -> isptr vl = OK p ->
                                 ptr_of_memval (TArray ty) (MArray abs ty a) (CIndex i) ty p
  | PtrRecord : forall tyl k nm r ty' vl p,
      Brecord.gprojT r k = OK (existT _ ty' vl) ->
      isptr vl = OK p ->
      ptr_of_memval (TRecord nm tyl) (MRecord abs nm tyl r) (CField k) ty' p.

  Definition graph_of_memory (m:mem abs) : forall ty (p1:ptr ty) (e:cedge) ty' (p2:ptr ty'), Prop :=
    fun ty p1 e ty' p2 =>
      exists mv, get abs p1 m = OK mv /\ ptr_of_memval _ mv e ty' p2.


  Definition disjoint_args (m: mem abs) {targs:list typ} (args : DList.dlist val targs)  : Prop :=
    forall ty1 (vl1:val ty1)
           ty2 (vl2:val ty2) p1 p2 i1 i2,
      i1 <> i2 ->
      DList.nth_error args i1 = OK (existT _ ty1 vl1) ->
      DList.nth_error args i2 = OK (existT _ ty2 vl2) ->
      isptr vl1 = OK p1 ->
      isptr vl2 = OK p2 ->
      disjoint (graph_of_memory m) ty1 p1 ty2 p2 .

  Fixpoint app_fun (targs: list typ)  (tret:typ)  (args : DList.dlist val targs) : forall (f:typ_of_fun abs targs tret), res (val tret * mem abs).
  Proof.
    destruct args.
    - simpl. apply (fun f => f tt).
    - simpl.
      specialize (app_fun l tret args).
      destruct l.
      intro.
      apply (f e).
      apply (fun f => app_fun (f e)).
  Defined.

  Definition same_ptr_val (ty:typ) (v1: val ty) (v2: val ty) : Prop :=
    match isptr v1 , isptr v2 with
    | OK p1 , OK p2 => p1 = p2
    |  _    , _     => False
    end.


  Definition same_ptr_mval (ty:typ) : forall (mv1 : mval abs ty) (mv2: mval abs ty), Prop :=
      match ty with
      | TArray ty' =>
          fun mv1 mv2 =>
            forall2 (same_ptr_val ty') (decomp_mval abs (TArray ty') mv1)
              (decomp_mval abs (TArray ty') mv2)
      | TRecord _ lty => fun mv1 mv2 =>
                         Brecord.grecord_rel same_ptr_val (decomp_mval abs _ mv1) (decomp_mval abs _ mv2)
      | TAbs ty => fun mv1 mv2 => decomp_mval abs _ mv1 = decomp_mval abs _ mv2
      |  _      => fun mv1 mv2 => False
      end.


  Definition same_ptr_mem (m1 m2:mem abs) := forall ty (p:ptr ty),
      res_rel (same_ptr_mval ty) (get abs p m1) (get abs p m2) /\
        _fresh abs m1 = _fresh abs m2.


  Definition is_function  (args: list typ) (tret : typ) (f: Fun abs args tret) : Prop :=
    forall (args : DList.dlist val args) (m:mem abs),
    forall r m',
      disjoint_args m args  ->
      app_fun _ _ args (f m) = OK (r,m') ->
      same_ptr_mem m m'.

  Fixpoint make_env (l:list ident) {targs:list typ} (args: DList.dlist val targs) : env :=
    match l with
    | nil => (fun _ => fail)
    | id::l => match args with
               | DNIL _ => (fun _ => fail)
               | DCONS _ e dl =>   env_set id e (make_env l dl)
               end
    end.

  Definition gamma_sfunction  (fargs : list ident) (args : list typ) (rt:typ) (f:sfunction) (fct : Fun abs args rt) : Prop :=
    is_function args rt fct /\
      match f with
      | RPrim => typ_is_prim rt = true
      | RDeep a => forall (args: DList.dlist val args) (m:mem abs) r m',
          app_fun _ _ args (fct m) = OK (r,m') ->
          eval_expr empty_genv  (make_env fargs args) m' rt a = OK r
      end.


  Definition gamma_afunction (af:afunction) (targs : list typ) (rt:typ) (f:Fun abs targs rt) :=
    targs = List.map snd (fn_params af) /\
      rt    = fn_return af /\
      gamma_sfunction (List.map fst (fn_params af)) targs rt (fst (fn_body af)) f.

  Inductive gamma_defs : aglobdef -> defs abs -> Prop :=
  | IsLit : forall ty vl, gamma_defs (ALit (typ_is_prim ty)) (DeclLit abs ty vl)
  | IsFun : forall (af:afunction) (targs : list typ) (rt:typ) (f: Fun abs targs rt),
      gamma_afunction af targs rt f ->
      gamma_defs (AFun af) (DeclFun abs targs rt f).


  Definition gamma_genv (ae:aenv) (ge: genv abs) : Prop :=
    forall k,
    match STree.get k ae , ge k with
    | Some gd    , OK d => gamma_defs gd d
    | None       , Error _ => True
    |  _         ,  _      => False
    end.


  (** Mapping from abstract nodes to pointers *)
  Definition ptr_memT (g:G.t) := forall (n:int) (ty: typ), G.has_node_label n ty (G.edges g) -> ptr ty.

  Definition gamma_KVar (g: G.t) (ptr_mem : ptr_memT g) (age:aenv) (v:KVar) : forall (ty:typ), val ty -> Prop :=
    match v with
    | KDead => fun _ _ => True
    | KPrim => fun ty v => is_primitive_val ty v = true
    | KFun f => fun ty v => ty = typ_of_afunction f /\
                              exists p,
                                isptr v = OK p /\
                                  exists id, get_addr_of_ptr p = inr id /\
                                               STree.get id age = Some (AFun f)
    | KNode n => fun ty v => exists (P: G.has_node_label n ty (G.edges g)), v = Vptr ty (ptr_mem n ty P)
    end.


  Definition gamma_vars (g:G.t) (ptr_mem: ptr_memT g) (age:aenv) (aenv:Vars.t) (e: env)  : Prop :=
    forall v, match e v, Vars.get v aenv with
              | OK evl , Some kv => let 'existT _ ty vl := evl in
                                    gamma_KVar g ptr_mem age kv ty vl
              | Error _  , None => True
              |  _   , _ => False
              end.

  Definition gamma_edge (e:env) (m:mem abs) (el:EdgeLabel.t) (ce:cedge) : Prop :=
    match el with
    | EdgeLabel.Field fd => ce = CField fd
    | EdgeLabel.Top      => False (* because it is used for must alias *)
    | EdgeLabel.Index i  =>
        exists pv i',
        eval_atom arch abs te ge e m (arr_index_typ arch) i = OK (Vprim (arr_index_typ arch) pv) /\
          index_of_pval arch pv = OK i' /\ ce = CIndex i'
    end.

  Definition is_get_field (e:env) (m:mem abs) (ty:typ) (mv: mval abs ty) (el:cedge) (ty':typ) (v:val ty') : Prop :=
    match el with
    | CField id => (* So ty is a record type *)
        match mv with
        | MRecord _ nm lty g => Brecord.gprojT g id  = OK (existT _ ty' v)
        |  _               => False
        end
    | CIndex i =>
        match mv with
        | MArray _ tye a =>
            match typ_eq_dec ty' tye with
            | left E => Barray.get a i = OK (cast (f_equal val E) v)
            | _       => False
            end
        | _              => False
        end
    end.

  Definition is_injective (g:G.t) (ptr_mem : ptr_memT g) :=
    forall i t1 j t2 P1 P2, get_addr_of_ptr (ptr_mem i t1 P1) =
                              get_addr_of_ptr (ptr_mem j t2 P2) -> i = j /\ t1 = t2.

  Definition gamma_must (g:G.t) (ptr_mem: ptr_memT g) (e:env)  (m:mem abs) : Prop :=
    forall n el ce n' ty  ty',
      G.root g <> n ->
      G.has_edge n el n' (G.edges g) ->
      forall (NL1 : G.has_node_label n ty (G.edges g))
             (NL2 : G.has_node_label n' ty' (G.edges g)),
      gamma_edge e m el ce ->
      graph_of_memory m ty (ptr_mem n ty NL1) ce ty' (ptr_mem n' ty' NL2).

  Definition leaf_node (g: G.t) (n:int)  :=
    forall o n', ~ G.has_edge n o n' (G.edges g).

(*  Definition gamma_sep (g:G.t) (ptr_mem: ptr_memT g) (e:env) (m:mem abs) : Prop :=
    forall n ty n' ty'
           (LEAF : leaf_node g n)
           (N : G.has_node_label n ty (G.edges g))
           (N': G.has_node_label n' ty' (G.edges g)),
      clo (graph_of_memory m) ty (ptr_mem n ty N) ty' (ptr_mem n' ty' N') -> False.
*)

(*  Record gamma_mem (g:G.t) (ptr_mem: ptr_memT g) (e:env) (m:mem abs) : Prop :=
    {
      gmust : gamma_must g ptr_mem e m;
    }.
*)



  End GAMMA.

  Definition wf_edges (g:G.t) (atms:SMap.t (list atom)) :=
    forall o a d, G.has_edge o (EdgeLabel.Index a) d (G.edges g) ->
    forall i, List.In i (AtomOrdered.vars_of_atom a) ->
              List.In a (SMap.get i atms ).

  
  Record wf_domain (d:domain) : Prop :=
    mk_wfd {
        wf_vars : Vars.wf (Vars d);
        wf_graph : G.wf EdgeLabel.next_label (Pto d);
        wf_atoms : wf_edges (Pto d) (Atoms d)
      }.

  Definition is_tree_mem (m:mem abs) :=
    is_global_tree (graph_of_memory m).

  Definition le_vars (v1 v2: Vars.t) : Prop :=
    forall x, option_rel le_KVar (Vars.get x v1) (Vars.get x v2).

  Record le_domain (d1 d2:domain) :=
    mk_le_domain {
        le_Vars : le_vars (Vars d1) (Vars d2);
        le_Pto : G.le_graph (Pto d1) (Pto d2);
      }.


  Record gamma  (age: aenv) (d:domain) (ptr_mem : ptr_memT (Pto d)) (ge:genv abs) (e:env) (m:mem abs) : Prop :=
    mk_gamma {
        gwf   : wf_domain d;
        gtree : is_tree_mem m;
        (*is_inj  : is_injective (Pto d) ptr_mem ;*)
        gvars   : gamma_vars (Pto d) ptr_mem age (Vars d) e;
        gmem    : gamma_must ge (Pto d) ptr_mem e m
      }.

  Definition gamma_with_var (age:aenv) (d:domain) (ptr_mem' : ptr_memT (Pto d)) (ge:genv abs) (e:env) (m:mem abs) (kv:KVar) (ty:typ) (v:val ty) : Prop :=
    gamma age d ptr_mem' ge e m /\ gamma_KVar (Pto d) ptr_mem' age kv ty v.


(*  Inductive eval_deep (ge:genv abs) (e:env) (m:mem abs) : forall (ty:typ) (p :ptr ty) (l:list EdgeLabel.t) (r:typ) (pr:ptr r), Prop :=
  | Deep_nil : forall ty p, eval_deep ge e m ty p nil ty p
  | Deep_cons : forall ty p el ce l ty' vl' p' tr pr mv,
      gamma_edge ge e m el ce ->
      get abs p m = OK mv ->
      is_get_field e m ty mv ce ty' vl' ->
      isptr vl' = OK p' ->
      eval_deep ge e  m ty' p' l tr pr ->
      eval_deep ge e m ty p (el::l) tr pr.
*)



  (** START THE PROOF *)

  Lemma cast_pval_OK : forall ty (p:pval ty),
      cast_pval p ty = OK p.
  Proof.
    unfold cast_pval.
    intros. destruct (typ_eq_dec ty ty); try congruence.
    f_equal.
    assert (e = eq_refl).
    { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
    subst. reflexivity.
  Qed.

  Lemma cast_pval_fail : forall ty (p:pval ty) ty',
      ty <> ty' ->
      cast_pval p ty' = efail.
  Proof.
    unfold cast_pval.
    intros. destruct (typ_eq_dec ty ty'); try congruence.
  Qed.

  Lemma has_ecast : forall (P: forall ty, val ty -> Prop)
                           ty v tyr vr,
      P ty v ->
      ecast v tyr = OK vr ->
      P tyr  vr.
  Proof.
    unfold ecast. intros.
    destruct (typ_eq_dec ty tyr); try discriminate.
    inv H0.
    apply H.
  Qed.

  Lemma gamma_KVar_KPrim : forall g ptr_mem age tyr vl,
      typ_is_prim tyr = true ->
      gamma_KVar g ptr_mem age KPrim tyr vl.
  Proof.
    simpl.
    intros.
    destruct vl.
    reflexivity.
    exfalso.
    destruct p; discriminate.
  Qed.


  Lemma get_var_correct :
    forall pto ptr_mem bt age avr ge e v av tyr vl
           (GAMMAE : gamma_genv age ge)
           (GAMMA : gamma_vars pto ptr_mem age avr e)
           (AEVAL : eval_var age avr v = OK av)
           (EVAL  : get_var abs te ge e v bt tyr = OK vl),
      gamma_KVar pto ptr_mem age av tyr vl.
  Proof.
    intros.
    unfold get_var in EVAL.
    destruct (btyp_to_typ te bt) eqn:BT ; try discriminate.
    unfold bind,Errors.bind in EVAL.
    destruct (typ_eq_dec t tyr); try discriminate.
    subst.
    specialize (GAMMA v).
    destruct (e v) eqn:GLVAR.
    - (* local var *)
      unfold eval_var in AEVAL.
      destruct (Vars.get v avr); try discriminate;
        try tauto.
      destruct s; simpl in GLVAR.
      inv AEVAL.
      eapply has_ecast; eauto.
    - (* global var *)
      unfold eval_var in AEVAL.
      destruct (Vars.get v avr); try tauto.
      specialize (GAMMAE v).
      destruct (STree.get v age) eqn:G, (ge v); try discriminate ; try tauto.
      inv GAMMAE.
      + (* this is a primitive *)
        destruct (typ_eq_dec ty tyr); try discriminate.
        subst. inv EVAL.
        destruct (typ_is_prim tyr) eqn:PRIM; try discriminate.
        inv AEVAL.
        apply gamma_KVar_KPrim; auto.
      + (* this is a function *)
        inv AEVAL.
        destruct (typ_eq_dec (TFun targs rt) tyr);
          try discriminate.
        subst.
        inv EVAL.
        simpl.
        unfold gamma_afunction in H.
        split.
        unfold typ_of_afunction.
        intuition congruence.
        eexists.
        split. reflexivity.
        eexists. split. reflexivity.
        auto.
  Qed.

  Lemma get_cast_typ_is_prim : forall ty t r,
      Barocq.get_cast abs ty t = OK r ->
      typ_is_prim t = true.
  Proof.
    unfold Barocq.get_cast.
    destruct ty,t; simpl; try discriminate; auto.
  Qed.

  Lemma cast_typ_ok : forall t1 (v1:eval_typ abs t1) t2 v2,
      Barocq.cast_typ abs v1 t2 = OK v2 -> t1 = t2.
  Proof.
    unfold Barocq.cast_typ.
    intros.
    destruct (typ_eq_dec t1 t2); try discriminate.
    auto.
  Qed.


  Lemma eval_unary_op_typ_is_prim : forall u t e1 tyr e2,
      Barocq.eval_unary_op abs u t e1 tyr = OK e2 ->
      typ_is_prim tyr = true.
  Proof.
    unfold Barocq.eval_unary_op.
    destruct u,t; simpl; intros;
      (try discriminate; try (apply cast_typ_ok in H; subst ; reflexivity)).
  Qed.

  Lemma bool_op_bool : forall b t1 t2 e1 e2 tyr v,
      Barocq.bool_op abs b t1 t2 e1 e2 tyr = OK v ->
      tyr = TBool.
  Proof.
    intros.
    destruct t1,t2 ; try discriminate.
    simpl in H.
    apply cast_typ_ok in H. congruence.
  Qed.

  Lemma int_op_int : forall f1 f2 t1 t2 e1 e2 tyr v,
      Barocq.int_op abs f1 f2 t1 t2 e1 e2 tyr = OK v ->
      exists s, tyr = TInt32 s \/ tyr = TInt64 s.
  Proof.
    intros.
    destruct t1,t2 ; try discriminate;
    simpl in H;
    destruct (signedness_eq_dec s s0);
    subst; exists s0; try discriminate.
    - apply cast_typ_ok in H. intuition congruence.
    - apply cast_typ_ok in H. intuition congruence.
  Qed.

  Lemma ecast_typ_OK : forall t1 (v1:res (eval_typ abs t1)) t2 v2,
      Barocq.ecast_typ abs v1 t2 = OK v2 -> t1 = t2.
  Proof.
    unfold Barocq.ecast_typ.
    intros. destruct (typ_eq_dec t1 t2); auto.
    discriminate.
  Qed.

  Lemma int_op_int_s : forall f1 f2 f3 f4 t1 t2 e1 e2 tyr v,
      Barocq.int_op_s abs f1 f2 f3 f4 t1 t2 e1 e2 tyr = OK v ->
      exists s, tyr = TInt32 s \/ tyr = TInt64 s.
  Proof.
    intros.
    destruct t1,t2 ; try discriminate;
    simpl in H;
    destruct s,s0; try discriminate.
    - exists Signed.
      apply ecast_typ_OK in H.
      intuition congruence.
    - exists Unsigned.
      apply ecast_typ_OK in H.
      intuition congruence.
    - exists Signed.
      apply ecast_typ_OK in H.
      intuition congruence.
    - exists Unsigned.
      apply ecast_typ_OK in H.
      intuition congruence.
  Qed.

  Lemma int_eq_neq_TBool : forall b eq1 eq2 eq3 eq4 t1 t2 e1 e2 tyr v,
      Barocq.int_eq_neq abs b eq1 eq2 eq3 eq4
        t1 t2 e1 e2 tyr = OK v ->
      tyr = TBool.
  Proof.
    unfold Barocq.int_eq_neq.
    destruct t1,t2 ; try discriminate.
    - intros.
      apply cast_typ_ok in H. subst; reflexivity.
    - intros.
      destruct (signedness_eq_dec s s0).
      apply cast_typ_ok in H. subst; reflexivity.
      discriminate.
    - intros.
      destruct (signedness_eq_dec s s0).
      apply cast_typ_ok in H. subst; reflexivity.
      discriminate.
    - intros.
      destruct (typ_eq_dec (TEnum i l) (TEnum i0 l0)); try discriminate.
      apply cast_typ_ok in H. subst; reflexivity.
  Qed.


  Lemma cmp_op_TBool : forall c1 c2 c3 c4 t1 t2 e1 e2 tyr v,
      Barocq.cmp_op abs c1 c2 c3 c4 t1 t2 e1 e2 tyr = OK v ->
      tyr = TBool.
  Proof.
    unfold Barocq.cmp_op.
    destruct t1,t2 ; try discriminate.
    - intros.
      destruct s,s0; try discriminate.
      apply cast_typ_ok in H. subst; reflexivity.
      apply cast_typ_ok in H. subst; reflexivity.
    - intros.
      destruct s,s0; try discriminate.
      apply cast_typ_ok in H. subst; reflexivity.
      apply cast_typ_ok in H. subst; reflexivity.
  Qed.



  Lemma eval_binary_op_typ_is_prim : forall b t1 t2 e1 e2 tyr v,
      Barocq.eval_binary_op abs b t1 t2 e1 e2 tyr = OK v ->
      typ_is_prim tyr = true.
  Proof.
    unfold Barocq.eval_binary_op.
    destruct b; simpl; intros; simpl in H.
    - apply bool_op_bool in H ; subst.
      reflexivity.
    - apply bool_op_bool in H ; subst.
      reflexivity.
    - apply bool_op_bool in H ; subst.
      reflexivity.
    - apply int_op_int in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_op_int in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_op_int in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_op_int_s in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_op_int_s in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_op_int in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_op_int in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_op_int in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_op_int in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_op_int_s in H.
      destruct H as (s & [T1 | T2]); subst; reflexivity.
    - apply int_eq_neq_TBool in H; subst; reflexivity.
    - apply int_eq_neq_TBool in H; subst; reflexivity.
    - apply cmp_op_TBool in H ; subst; reflexivity.
    - apply cmp_op_TBool in H ; subst; reflexivity.
    - apply cmp_op_TBool in H ; subst; reflexivity.
    - apply cmp_op_TBool in H ; subst; reflexivity.
  Qed.


  Lemma cast_val_OK : forall t1 (v1:val t1) t2 v,
      cast_val v1 t2 = OK v ->
      exists EQ, v = cast (f_equal val EQ) v1.
  Proof.
    intros. unfold cast_val in H.
    destruct (typ_eq_dec t1 t2); try discriminate.
    eexists. inv H. reflexivity.
  Qed.

  Lemma val_of_pval_is_primitive_val : forall tyr (pv:res (pval tyr))  (v:val tyr),
      val_of_pval pv = OK v ->
      is_primitive_val tyr v = true.
  Proof.
    intros.
    destruct pv.
    simpl in H. inv H.
    reflexivity.
    discriminate.
  Qed.

  Lemma gamma_with_var_gamma : forall ae d ptr_mem ge e m kv ty v,
      gamma_with_var ae d ptr_mem ge e m kv ty v ->
      gamma ae d ptr_mem ge e m.
  Proof.
    intros.
    destruct H. auto.
  Qed.


(*  Lemma compat_pto_refl : forall g ptr_mem,
      compat_pto g ptr_mem ptr_mem.
  Proof.
    unfold compat_pto. reflexivity.
  Qed.
*)

  Lemma gamma_with_var_typing : forall ae d ptr_mem ge e m n ty v,
      gamma_with_var ae d ptr_mem ge e m (KNode n) ty v ->
      G.has_node_label n ty (G.edges (Pto d)).
  Proof.
    intros.
    destruct H.
    simpl in H0.
    destruct H0 ; auto.
  Qed.

  (*
  Lemma graph_of_memory_next_label : forall ge m ty pt1 ce e i ty' pt2,
      graph_of_memory m ty pt1 ce ty' pt2 ->
      gamma_edge ge e m i ce ->
      EdgeLabel.next_label ty i = OK ty'.
  Proof.



  Lemma pto_typed : forall ae d ge e m n ty i n' ce
    ,
      gamma  ae d ge e m ->
      G.has_node_label n ty (G.edges (Pto d)) ->
      G.has_edge n i n' (G.edges (Pto d)) ->
      gamma_edge ge e m i ce ->
      exists ty',
        G.has_node_label n' ty' (G.edges (Pto d)) /\
          EdgeLabel.next_label ty i = OK ty'.
  Proof.
    intros.
    destruct H.
    unfold gamma_mem in gmem.
    assert (exists t1, G.has_node_label n' t1 (G.edges (Pto d))).
    {
      eapply G.wf_lb; eauto.
      destruct gwf0 ; auto.
    }
    destruct H as (t1 & NL2).
    apply gmem  with (ce:=ce) (NL1 := H0) (NL2 := NL2) in H1; eauto.
    eexists ; split; eauto.



gamma ae d1 ge e m

   *)

(*  Lemma stable_node_label : forall ae d1 d2 ge e m n lb,
      gamma ae d1 ge e m ->
      gamma ae d2 ge e m ->
      G.has_node_label n lb (G.edges (Pto d1)) ->
      G.has_node_label n lb (G.edges (Pto d2)).
  Proof.
    intros.
    destruct H,H0.
    clear - gmem gmem0.
*)

  Definition is_augmented (g1: G.t) (ptr_mem1 : ptr_memT g1)
    (g2: G.t) (ptr_mem2 : ptr_memT g2) : Prop :=
    forall n ty (N1: G.has_node_label n ty (G.edges g1))
           (N2 : G.has_node_label n ty (G.edges g2)),
      ptr_mem1 n ty N1 = ptr_mem2 n ty N2.

  Definition le_domaing (d1 d2: domain) :=
    G.le_graph (Pto d1) (Pto d2)  /\
      Vars d1 = Vars d2.

  Lemma le_domaing_refl : forall d,
      le_domaing d d.
  Proof.
    constructor; auto.
    constructor; auto.
    lia.
  Qed.

  Lemma le_domaing_trans : forall d1 d2 d3,
      le_domaing d1 d2 -> le_domaing d2 d3 -> le_domaing d1 d3.
  Proof.
    intros.
    destruct H. destruct H0.
    constructor.
    eapply G.le_graph_trans;eauto.
    congruence.
  Qed.






  Lemma is_augmented_refl : forall g1 (ptr_mem1: ptr_memT g1),
      is_augmented g1 ptr_mem1 g1 ptr_mem1.
  Proof.
    unfold is_augmented.
    intros.
    assert (N1 = N2).
    { apply Eqdep_dec.UIP_dec.
      apply res_eq_dec.
      apply typ_eq_dec. }
    subst.
    reflexivity.
  Qed.

  Lemma le_domaing_set_atom : forall d atm d1,
      le_domaing d d1 ->
      le_domaing d (set_atom atm d1).
  Proof.
    intros.
    destruct H ; constructor ;auto.
  Qed.

  
  Lemma bind_path_le_domain : forall d n e d' av,
      wf_domain d ->
      bind_path d n e = OK (d', av) ->
      le_domaing d d'.
  Proof.
    unfold bind_path. intros.
    destruct (IntMap.Facts.eq_dec n (G.root (Pto d))); try discriminate.
    destruct (G.create_edge EdgeLabel.next_label n e (Pto d)) eqn:C ; try discriminate.
    destruct p. destruct p.
    destruct H.
    exploit G.create_edge_le;eauto.
    intro.
    simpl in H0.
    destruct (typ_is_prim t0); try discriminate.
    inv H0. apply le_domaing_refl.
    inv H0.
    constructor; auto.
  Qed.

  Lemma gamma_KVar_augment : forall pto1 pto2 ptr_mem1 ae ptr_mem2 kv ty v,
      gamma_KVar pto1 ptr_mem1 ae  kv ty v ->
      G.le_graph pto1 pto2 ->
      is_augmented pto1 ptr_mem1 pto2 ptr_mem2 ->
      gamma_KVar pto2 ptr_mem2 ae kv ty v.
  Proof.
    intros.
    destruct kv ; simpl in *; auto.
    destruct H as (ND & EQ).
    destruct H0.
    assert (ND' := ND).
    apply le_node in ND'.
    exists ND'.
    unfold is_augmented in H1.
    erewrite <- H1; eauto.
  Qed.





  Definition new_node_case (g g' : G.t) (n:int) (ty:typ) (n':int) (ty':typ)
    (P : forall (nd : int) (lb1 : TypOrdered.t),
        G.has_node_label nd lb1 (G.edges g') <-> G.has_node_label nd lb1 (G.edges g) \/ nd = n' /\ ty' = lb1)
    (NODE : G.has_node_label n ty (G.edges g'))
    :

    ({G.has_node_label n ty (G.edges g)} + {~ G.has_node_label n ty (G.edges g) /\  n = n' /\ ty' = ty}).
  Proof.
    rewrite P in NODE.
    unfold G.has_node_label in NODE.
    unfold G.has_node_label.
    destruct (G.get_label (G.edges g) n) eqn:GET.
    destruct (typ_eq_dec t ty).
    - left. intuition congruence.
    - right. intuition congruence.
    - right. intuition congruence.
  Qed.




  Definition ptr_mem_set (g:G.t) (ptr_mem : ptr_memT g) (g': G.t) (n': int) (ty': typ)
    (LBEL :
      forall (nd : int) (lb1 : TypOrdered.t),
        G.has_node_label nd lb1 (G.edges g') <-> G.has_node_label nd lb1 (G.edges g) \/
                                                   nd = n' /\ ty' = lb1)
    (p':ptr ty') : ptr_memT g'.
  Proof.
    intros n ty LB.
    destruct (new_node_case g g' n ty n' ty' LBEL LB).
    apply (ptr_mem n ty h).
    destruct (eqs n n').
    destruct a. destruct H0.
    apply (cast (f_equal ptr H1) p') .
    tauto.
  Defined.

  Lemma is_augmented_ptr_mem_set : forall g ptr_mem g1 n' ty' NODE pty',
  is_augmented g ptr_mem g1
    (ptr_mem_set g ptr_mem g1 n' ty' NODE pty').
  Proof.
    unfold is_augmented.
    intros.
    unfold ptr_mem_set.
    destruct (new_node_case g g1 n ty n' ty' NODE N2).
    assert (h = N1).
    { apply Eqdep_dec.UIP_dec.       apply res_eq_dec.
      apply typ_eq_dec. }
    congruence.
    exfalso. tauto.
  Qed.

 Lemma gamma_set_atom : forall ae d a (ptrm_mem:ptr_memT (Pto d))  ge e m
                               (G : gamma ae d ptrm_mem ge e m)
                               (WF : wf_edges (Pto d) (Atoms d) -> wf_edges (Pto d) a),
     gamma ae (set_atom a d) ptrm_mem ge e  m.
 Proof.
   intros.
   unfold set_atom.
   destruct G; constructor;simpl;auto.
   destruct gwf0; constructor ;auto.
 Qed.

 Lemma is_injective_set :
   forall pto pto' ptr_mem n' ty' NODE pty'
          (INJ: is_injective pto ptr_mem)
          (OLD : forall n ty (NL : G.has_node_label n ty (G.edges pto)),
              get_addr_of_ptr (ptr_mem n ty NL) = get_addr_of_ptr pty' -> n = n' /\ ty = ty'),
      is_injective pto' (ptr_mem_set pto ptr_mem pto' n' ty' NODE pty').
 Proof.
   unfold is_injective.
   intros.
   unfold ptr_mem_set in H.
   destruct (new_node_case pto pto' i t1 n' ty' NODE P1).
   - destruct (new_node_case pto pto' j t2 n' ty' NODE P2).
     +  eapply INJ; eauto.
     + unfold and_rect in H.
       destruct a. destruct a.
       destruct (eqs j n'); simpl in H.
       *  subst.
          simpl in H.
          eapply OLD; eauto.
       * congruence.
   - destruct a. destruct a.
     destruct (eqs i n'); simpl in H.
     + subst.
       simpl in H.
       destruct (new_node_case pto pto' j t2 n' t1 NODE P2).
       * subst.
         simpl in H.
         symmetry in H.
         eapply OLD in H; eauto.
         intuition congruence.
       * unfold and_rect in H. destruct a.
         destruct a.
         subst.
         destruct (eqs n' n'); try congruence.
         simpl in H.
         tauto.
     + congruence.
 Qed.

 Lemma gamma_vars_set : forall pto pto' ptr_mem ae vars e n' ty' NODE pty',
     gamma_vars pto ptr_mem ae vars e ->
     G.le_graph pto pto' ->
     gamma_vars pto' (ptr_mem_set pto ptr_mem pto' n' ty' NODE pty') ae vars e.
 Proof.
   unfold gamma_vars.
   intros.
   specialize (H v).
   destruct (e v).
   destruct (Vars.get v vars).
   - destruct s.
     eapply gamma_KVar_augment; eauto.
     eapply is_augmented_ptr_mem_set; eauto.
   - tauto.
   - auto.
 Qed.

 Lemma gamma_augment :
   forall pto pto' ptr_mem ge  e m ptr_mem'
          (GMEM : gamma_must ge pto ptr_mem e m)
          (AUG  : is_augmented pto ptr_mem pto' ptr_mem')
          (WF1   : G.wf EdgeLabel.next_label pto)
          (WF2   : G.wf EdgeLabel.next_label pto')
          (LE    : G.le_graph pto pto')
          (NEW  : forall o fd d, G.has_edge o fd d (G.edges pto') ->
                                 ~ G.has_edge o fd d (G.edges pto) ->
                                forall ty ty' ce
                                       (N1 : G.has_node_label o ty (G.edges pto'))
                                       (N2 : G.has_node_label d ty' (G.edges pto')),
                                       gamma_edge ge e m fd ce ->
                                       graph_of_memory m ty (ptr_mem' o ty N1) ce ty' (ptr_mem' d ty' N2))
   ,
     gamma_must ge pto' ptr_mem' e m.
 Proof.
   intros.
   unfold gamma_must in *.
   repeat intro.
     destruct (G.has_edge_dec n el n' (G.edges pto)).
     +  (* old edge *)
     exploit G.has_edge_node_label_le; eauto.
     intros (NL1'& NL2').
     rewrite <- AUG with (N1:= NL1').
     rewrite <- AUG with (N1:= NL2').
     eapply GMEM; eauto.
     destruct LE; congruence.
     + (* new edge *)
     eapply NEW;eauto.
 Qed.

Lemma gamma_edge_inj : forall ge e m ed ce ce',
    gamma_edge ge e m ed ce' ->
    gamma_edge ge e m ed ce  -> ce' = ce.
Proof.
  intros.
  unfold gamma_edge in *.
  destruct ed.
  - congruence.
  - destruct H as (pv1 & e1 & EA1 & IND1 & EQ1).
    destruct H0 as (pv2 & e2 & EA2 & IND2 & EQ2).
    assert (pv1 = pv2).
    {
      rewrite EA1 in EA2.
      revert EA2.
      clear.
      revert pv1 pv2.
      generalize (arr_index_typ arch) as ti.
      intros.
      assert (Vprim ti pv1 = Vprim ti pv2) by congruence.
      clear EA2.
      inv H.
      apply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
      apply typ_eq_dec; auto.
    }
    congruence.
  - tauto.
Qed.

Lemma same_node : forall n ty E (N1 N1': G.has_node_label n ty E),
    N1 = N1'.
Proof.
  intros.
  apply Eqdep_dec.UIP_dec.
  apply res_eq_dec.
  apply typ_eq_dec.
Qed.





 Lemma gamma_must_set :
   forall pto pto' ptr_mem ge  e m n ty ed ce n' ty' NODE pty'
          (WF    : G.wf EdgeLabel.next_label pto)
          (WF'   : G.wf EdgeLabel.next_label pto')
          (LE    : G.le_graph pto pto')
          (GMEM : gamma_must ge pto ptr_mem e m)
          (EDGE :
          forall      (o : int) (e1 : EdgeLabel.t) (d0 : int),
            G.has_edge o    e1 d0 (G.edges pto') <->
              G.has_edge o e1 d0 (G.edges pto) \/ ~ G.has_edge o e1 d0 (G.edges pto) /\ o = n /\ e1 = ed /\ d0 = n')
          (EDGEN : G.has_edge n ed n' (G.edges pto'))
          (NXT : EdgeLabel.next_label ty ed = OK ty')
          (GE : gamma_edge ge e m ed ce)
          (ND : G.has_node_label n ty (G.edges pto))
          (PTY : forall (ND': G.has_node_label n' ty' (G.edges pto)), ptr_mem n' ty' ND' = pty')
          (CMEM : graph_of_memory m ty (ptr_mem n ty ND) ce ty' pty')

   ,
     gamma_must ge pto' (ptr_mem_set pto ptr_mem pto' n' ty' NODE pty') e m.
 Proof.
   intros.
   unfold gamma_must in *; repeat intro.
   assert (AUG := is_augmented_ptr_mem_set pto ptr_mem pto' n' ty' NODE pty').
   assert (CEDGE := H0).
   rewrite EDGE in H0.
   destruct H0.
   - (* old edge *)
     exploit G.has_edge_node_label_le; eauto.
     intros (NDn & NDn').
     unfold is_augmented in AUG.
     rewrite <- AUG with (N1 := NDn).
     rewrite <- AUG with (N1 := NDn').
     eapply GMEM; eauto.
     destruct LE ; congruence.
   - (* n -[ed]-> n' *)
     destruct H0 as (EN & ED & EN').
     destruct EN'; subst.
     assert (ce0 = ce) by (eapply gamma_edge_inj; eauto).
     subst.
     (* The edge does not exists by maybe the nodes are already there *)
     unfold ptr_mem_set.
     destruct (new_node_case pto pto' n ty0 n' ty' NODE NL1).
     + (* n -> ty *)
       assert (ty0 = ty).
       { eapply G.has_node_label_inj; eauto. }
       subst.
       assert (h = ND).
       eapply same_node; eauto.
       subst.
       destruct (new_node_case pto pto' n' ty'0 n' ty' NODE NL2).
       *
         assert (ty'0 = ty').
         {
           eapply G.wf_nxt in EDGEN; eauto.
           congruence.
         }
         subst.
         rewrite PTY. auto.
       * destruct (eqs n' n'); try congruence.
         destruct a. destruct a.
         subst. simpl.
         auto.
     + destruct a.
       destruct a ; subst.
       destruct (eqs n' n'); try congruence.
       exfalso.
       eapply G.tree_no_loop with (E:= G.edges pto') (n:= n').
       eapply G.wf_tree ; eauto.
       eapply Relation_Operators.t_step.
       eexists ; eauto.
 Qed.

 Lemma gamma_set_pto :
   forall ae ge e m g d ptr_mem n ty ed n' ty' ND NODE pty' ce
          (GAMMA : gamma ae d ptr_mem ge e m)
          (WFd   : wf_domain d)
          (WFG   : G.wf EdgeLabel.next_label g)
          (WFE : wf_edges (Pto d) (Atoms d) -> wf_edges g (Atoms d))
          (LEG :   G.le_graph (Pto d) g)
          (HAS : forall (o : int) (e1 : EdgeLabel.t) (d0 : int),
              G.has_edge o e1 d0 (G.edges g) <->
                G.has_edge o e1 d0 (G.edges (Pto d)) \/
                  ~ G.has_edge o e1 d0 (G.edges (Pto d)) /\
                    o = n /\ e1 = ed /\ d0 = n')
          (NODES : forall (nd : int) (lb1 : TypOrdered.t),
              G.has_node_label nd lb1 (G.edges g) <-> G.has_node_label nd lb1 (G.edges (Pto d)) \/ nd = n' /\ ty' = lb1)
(*          (GET : forall m (ty : TypOrdered.t)
                        (NL : G.has_node_label m ty (G.edges (Pto d))),
              get_addr_of_ptr (ptr_mem m ty NL) =  get_addr_of_ptr pty' -> m = n' /\ ty = ty')  *)
          (NXT : EdgeLabel.next_label ty ed = OK ty')
          (GE : gamma_edge ge e m ed ce)
          (PMEM : forall ND' : G.has_node_label n' ty' (G.edges (Pto d)), ptr_mem n' ty' ND' = pty')
          (NN' : graph_of_memory m ty (ptr_mem n ty ND) ce ty' pty')
   ,
          gamma ae (set_pto g d)
            (ptr_mem_set (Pto d) ptr_mem g n' ty' NODE pty') ge e m.
 Proof.
   intros.
   destruct GAMMA ; constructor ; auto.
   - (* wf_domain *)
     destruct d ;
     destruct gwf0; constructor ;auto.
   (*   - destruct d ; simpl in *.
     apply is_injective_set; auto. *)
   - destruct d; simpl in *.
     eapply gamma_vars_set; eauto.
   - eapply gamma_must_set; eauto.
     + destruct gwf0; auto.
     + rewrite HAS. tauto.
 Qed.


Ltac ET := repeat (match goal with
                   | H : existT _ _ _  = existT _ _ _  |- _ =>
                       apply Eqdep_dec.inj_pair2_eq_dec in H
                   end; try apply typ_eq_dec).


 Lemma ptr_of_memval_inv : forall ty mv ce ty' p1 p2,
     ptr_of_memval ty mv ce ty' p1 ->
     ptr_of_memval ty mv ce ty' p2 -> p1 = p2.
 Proof.
   intros.
   inversion H as []; inversion H0 as [] ; subst; try congruence.
   - clear H0 H.
     ET; subst.
   assert (a0 = a).
   { inv H14.
     ET; congruence.
   }
   subst.
   congruence.
   - clear H0 H.
     ET; subst.
   inv H14; subst.
   assert (nm0 = nm) by congruence.
   assert (tyl0 = tyl) by congruence.
   subst. ET; subst.
   assert (r0 = r).
   { inv H13.
     apply Eqdep_dec.inj_pair2_eq_dec in H0.
     auto.
     apply list_eq_dec.
     decide equality.
     apply typ_eq_dec.
     apply string_dec.
   }
   subst.
   rewrite H1 in H9.
   inv H9.
   ET. congruence.
 Qed.

 Lemma create_edge_same_graph :
   forall n ed g g' n' ty',
     G.create_edge EdgeLabel.next_label n ed g =
       OK (g', (n', ty')) ->
     G.has_edge n ed n' (G.edges g) ->
     g' = g.
 Proof.
   unfold G.create_edge.
   intros.
   unfold G.has_edge in H0.
   destruct H0 as (nl & succs & FIND & IN).
   rewrite FIND in H.
   destruct (G.find_edgelabel ed succs) eqn:FINDED.
   - destruct (G.get_label (G.edges g) i) eqn:LAB;
       try discriminate.
     simpl in H. congruence.
   - apply G.find_label_None in FINDED.
     tauto.
     rewrite in_map_iff.
     exists (ed,n'). simpl; tauto.
 Qed.

 Lemma set_pto_same : forall d,
     set_pto (Pto d) d = d.
 Proof.
   destruct d; reflexivity.
 Qed.



 Lemma gamma_set_pto_same : forall ae d ptr_mem ge e m,
     gamma ae d ptr_mem ge e m ->
     gamma ae (set_pto (Pto d) d) ptr_mem ge e m.
 Proof.
   intros. destruct H.
   constructor ; auto.
   destruct gwf0 ; constructor ; auto.
 Qed.

Lemma gamma_set_pto_atom_same : forall ae d a ptr_mem ge e m,
     gamma ae d ptr_mem ge e m ->
     (wf_edges (Pto d) (Atoms d) -> wf_edges (Pto d) a) ->
     gamma ae (set_pto (Pto d) (set_atom a d)) ptr_mem ge e m.
 Proof.
   intros. destruct H.
   constructor ; auto.
   destruct gwf0 ; constructor ; auto.
 Qed.





 Lemma wf_edges_same : forall ed d,
     wf_edges (Pto d) (Atoms d) ->
     wf_edges (Pto d) (register_vars_of_edge ed (Atoms d)).
 Proof.
   unfold wf_edges.
   intros.
   destruct ed; simpl.
   - eauto.
   - eapply H in H0; eauto.
     clear H1.
     unfold register_vars_of_atom.
     clear H.
     induction (AtomOrdered.vars_of_atom a0).
     + simpl. auto.
     + simpl.
       unfold SMap_setl.
       rewrite SMap.gsspec.
       destruct (StringIndexed.eq i a1).
       subst.
       simpl. tauto.
       auto.
   - eauto.
 Qed.

(* Lemma wf_edges_add_edge : forall d pto' n ed n'  ty'

     (EDGE :
       forall (o : int) (e1 : EdgeLabel.t) (d0 : int),
         G.has_edge o e1 d0 (G.edges pto') <->
           G.has_edge o e1 d0 (G.edges (Pto d)) \/
             ~ G.has_edge o e1 d0 (G.edges (Pto d)) /\
               ~ G.has_node d0 (G.edges (Pto d)) /\
               d0 = G.fresh (Pto d) /\ o = n /\ e1 = ed /\ d0 = n')
       (LBEL :
    forall (nd : int) (lb1 : TypOrdered.t),
    G.has_node_label nd lb1 (G.edges pto') <->
    G.has_node_label nd lb1 (G.edges (Pto d)) \/
    nd = n' /\ ty' = lb1),
    wf_edges (Pto d) (Atoms d) ->
       wf_edges pto' (Atoms d).
 Proof.
   intros.
   unfold wf_edges.
   intros.
   rewrite EDGE in
*)


 Definition Atoms_le (atm1 atm2 : SMap.t (list atom)) :=
   forall v, (forall a, List.In a (SMap.get v atm1) -> List.In a (SMap.get v atm2)).

 Lemma wf_edges_le : forall pto a1 a2,
     wf_edges pto a1 ->
     Atoms_le a1 a2 -> wf_edges pto a2.
 Proof.
   intros.
   unfold wf_edges in *.
   intros.
   eapply H in H1; eauto.
 Qed.

 Lemma Atoms_le_refl : forall a,
     Atoms_le a a.
 Proof.
   unfold Atoms_le.
   tauto.
 Qed.

 Lemma Atoms_le_register : forall ed a,
  Atoms_le a (register_vars_of_edge ed a).
 Proof.
   destruct ed; simpl; auto.
   - apply Atoms_le_refl.
   - unfold register_vars_of_atom.
     induction (AtomOrdered.vars_of_atom a); simpl.
     + apply Atoms_le_refl.
     + intros. unfold SMap_setl.
       repeat intro.
       rewrite SMap.gsspec.
       destruct (StringIndexed.eq v a0).
       * simpl. subst.
         right.
         apply IHl; auto.
       * apply IHl;auto.
   -  apply Atoms_le_refl.
 Qed.
   
 Lemma wf_domain_set_atom : forall d ed,
     wf_domain d ->
     wf_domain (set_atom (register_vars_of_edge ed (Atoms d)) d).
 Proof.
   intros.
   destruct H; constructor ; auto.
   simpl.
   eapply wf_edges_le;eauto.
   apply Atoms_le_register.
 Qed.

 Definition vars_of_edge (e:EdgeLabel.t) :=
   match e with
   | EdgeLabel.Field _ => nil
   | EdgeLabel.Index a => AtomOrdered.vars_of_atom a
   | EdgeLabel.Top     => nil
   end.




 Lemma wf_edges_stable :
   forall pto  a pto' ed
          (EDGE : forall o e d, G.has_edge o e d (G.edges pto') ->
                           G.has_edge o e d (G.edges pto) \/
                             e = ed)
          (ED : forall atm,  EdgeLabel.Index atm = ed ->
                           forall i, List.In i (AtomOrdered.vars_of_atom atm) ->
                                     List.In atm (SMap.get i a))
          (WF : wf_edges pto a),
     wf_edges pto' a.
 Proof.
   intros.
   unfold wf_edges in *; auto.
   intros.
   apply EDGE in H.
   destruct H.
   - eauto.
   - eauto.
 Qed.

 Lemma register_vars_of_edge_In : forall atm ed a,
     EdgeLabel.Index atm = ed ->
     forall i : ident, List.In i (AtomOrdered.vars_of_atom atm) ->
                       List.In atm (SMap.get i (register_vars_of_edge ed a)).
 Proof.
   intros.
   subst. simpl.
   unfold register_vars_of_atom.
   revert i H0.
   induction (AtomOrdered.vars_of_atom atm).
   - simpl. tauto.
   - simpl.
     intros.
     simpl in H0; destruct H0; subst.
     + unfold SMap_setl at 1. rewrite SMap.gss.
       simpl. tauto.
     + apply IHl in H.
       unfold SMap_setl at 1. rewrite SMap.gsspec.
       destruct (StringIndexed.eq i a0); subst.
       simpl; tauto.
       auto.
 Qed.

   
 Lemma bind_path_correct :
    forall d n ge ed ce d' av ty r tyr e m ae v ptr_mem
           (BIND:bind_path d n ed = OK (d', av))
           (EVAL:eval_mem_access abs m r ce tyr = OK v)
           (D  : wf_domain d)
           (GE : gamma_edge ge e m ed ce)
           (G  : gamma ae d ptr_mem ge e m)
           (GV : gamma_KVar (Pto d) ptr_mem ae (KNode n) ty r),
    exists ptr_mem' : ptr_memT (Pto d'),
      is_augmented (Pto d) ptr_mem (Pto d') ptr_mem' /\
        gamma_with_var ae d' ptr_mem' ge e m av tyr v.
  Proof.
    intros.
    unfold eval_mem_access in EVAL.
    simpl in GV.
    destruct GV as (ND & R).
    subst.
    simpl in EVAL.
    destruct (get abs (ptr_mem n ty ND) m) eqn:GET ; try discriminate.
    simpl in EVAL.
    assert (EdgeLabel.next_label ty ed = OK tyr).
    {
      destruct ed ; simpl in GE; try tauto.
      - subst.
        unfold eval_record_proj in EVAL.
        destruct m0; try discriminate.
        simpl.
        unfold ecast_val in EVAL.
        destruct (Brecord.gprojT r id) eqn:P.
        destruct s.
        apply cast_val_OK in EVAL.
        destruct EVAL ; subst.
        clear -P.
        induction rty ; simpl in *.
        discriminate.
        destruct a.
        destruct r.
        simpl.
        destruct (id=? s)%string.
        inv P. reflexivity.
        eapply IHrty;eauto.
        discriminate.
      - destruct GE.
        destruct H.
        destruct H.
        destruct H.
        destruct H0. subst.
        unfold EdgeLabel.next_label.
        unfold eval_array_get in EVAL.
        destruct m0; try discriminate.
        destruct (Barray.get a0 x0); try discriminate.
        simpl in EVAL.
        apply cast_val_OK in EVAL.
        destruct EVAL. subst.
        reflexivity.
    }
    unfold bind_path in BIND.
    destruct (IntMap.Facts.eq_dec n (G.root (Pto d))) eqn:ROOT ; try discriminate.
    destruct (G.create_edge EdgeLabel.next_label n ed)
      eqn:C.
    destruct p as (g1,(n',ty')).
    exploit G.create_edge_spec;eauto.
    destruct D; eauto.
    intros (EDGEN & LBN' & EDGE & LBEL & FRESH).
    simpl in BIND.
    assert (EdgeLabel.next_label ty ed = OK ty').
    {
      eapply G.wf_nxt;eauto.
      exploit G.wf_create_edge.
      destruct D; eauto.
      eauto.
      auto.
      rewrite LBEL.
      tauto.
    }
    assert (tyr = ty') by congruence.
    subst.
    destruct (typ_is_prim ty') eqn:PRIM.
    - (* Primitive *)
      inv BIND.
      exists ptr_mem.
      split; auto.
      apply is_augmented_refl.
      constructor; auto.
      apply gamma_KVar_KPrim; auto.
    - (* Not primitive *)
      inv BIND.
      change (exists
                 (ptr_mem' : ptr_memT g1),
                 is_augmented (Pto d) ptr_mem g1 ptr_mem' /\
                   gamma_with_var ae
                     (set_pto g1 (set_atom (register_vars_of_edge ed (Atoms d))
                         d)) ptr_mem' ge e m
                     (KNode n') ty' v).
      assert (VPTR : exists p: ptr ty', v = Vptr ty' p).
      {
        destruct v.
        destruct p; try discriminate.
        eexists. reflexivity.
      }
      destruct VPTR as (p & EQ) ; subst.
      assert (CMEM :
               graph_of_memory m ty (ptr_mem n ty ND) ce ty' p).
      {
        clear - EVAL GET.
        destruct ce.
        - unfold eval_record_proj in EVAL.
          unfold graph_of_memory.
          exists m0.
          split; auto.
          destruct m0 ; try discriminate.
          destruct (Brecord.gprojT r id) eqn:GPROJ; try discriminate.
          simpl in EVAL.
          destruct s.
          apply cast_val_OK in EVAL.
          destruct EVAL as (EQ1 & EQ2). subst.
          simpl in EQ2. subst.
          econstructor;eauto.
        - unfold eval_array_get in EVAL.
          unfold graph_of_memory.
          exists m0.
          split; auto.
          destruct m0 ; try discriminate.
          destruct (Barray.get a i) eqn:GETA; try discriminate.
          simpl in EVAL.
          apply cast_val_OK in EVAL.
          destruct EVAL as (EQ1 & EQ2). subst.
          simpl in EQ2. subst.
          econstructor ;eauto.
      }
      rewrite EDGE in EDGEN.
      assert (EDGEN':= EDGEN).
      destruct EDGEN as [EDGEN
                         | EDGEN].
      +  apply create_edge_same_graph in C; auto.
         subst.
         exists ptr_mem.
         split.
         { apply is_augmented_refl. }
         { constructor.
           +  apply gamma_set_pto_atom_same; auto.
              apply wf_edges_same; auto.
           + simpl.
             exploit G.has_edge_next_label; eauto.
             destruct D;auto.
             intro ND'.
             exists ND'.
             f_equal.
            destruct G.
            eapply gmem0 in EDGEN ; eauto.
            specialize (EDGEN ND ND' GE).
            unfold is_tree_mem in gtree0.
            unfold is_global_tree in gtree0.
            unfold graph_of_memory in *.
            destruct CMEM as (mv1 & G1 & MV1).
            destruct EDGEN as (mv2 & G2 & MV2).
            assert (mv1 = mv2) by congruence.
            subst.
            eapply ptr_of_memval_inv; eauto.
         }
      + (* We really add a new edge *)
      exists (ptr_mem_set _ ptr_mem g1 n' ty' LBEL p).
      split.
      apply is_augmented_ptr_mem_set.
      constructor.
      {
        change (Pto d) with (Pto (set_atom (register_vars_of_edge ed (Atoms d)) d)).
        eapply gamma_set_pto; eauto.
        apply gamma_set_atom; auto.
        - apply wf_edges_same.
        - apply wf_domain_set_atom; auto.
        -  eapply G.wf_create_edge; eauto.
          destruct D;auto.
        - simpl.
          apply wf_edges_stable with (ed:=ed); auto.
          intros.
          rewrite EDGE in H1.
          tauto.
          intros;
          eapply register_vars_of_edge_In; eauto.
        - eapply G.create_edge_le; eauto.
          destruct D;auto.
        - intros.
          rewrite EDGE.
          simpl.
          intuition congruence.
        - intros.
          destruct EDGEN as (NOEDGE & NONODE & FRESH' & _).
          exfalso.
          apply NONODE.
          eexists ; eauto.
      }
      simpl.
      exists LBN'.
      f_equal.
      unfold ptr_mem_set.
      destruct (new_node_case (Pto d) g1 n' ty' n' ty' LBEL LBN').
      destruct EDGEN as (_ & N & _).
      exfalso. apply N.
      eexists ; eauto.
      destruct (eqs n' n') ; try congruence.
      destruct a. destruct a.
      assert (e2 = eq_refl).
      { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst. reflexivity.
    - discriminate.
  Qed.


  Lemma is_augmented_trans :
    forall g1 (ptr_mem1 : ptr_memT g1)
           g2 (ptr_mem2 : ptr_memT g2)
           g3 (ptr_mem3 : ptr_memT g3)
           (LE1 : G.le_graph g1 g2)
           (LE2 : G.le_graph g2 g3),
      is_augmented g1 ptr_mem1 g2 ptr_mem2 ->
      is_augmented g2 ptr_mem2 g3 ptr_mem3 ->
      is_augmented g1 ptr_mem1 g3 ptr_mem3.
  Proof.
    unfold is_augmented; intros.
    destruct LE1.
    assert (N1':= N1).
    apply le_node in N1'.
    rewrite H with (N2:= N1').
    apply H0.
  Qed.


  Lemma aeval_atom_correct :
    forall a ge e m tyr ae d ptr_mem d' av v
           (GAMMAE : gamma_genv ae ge)
           (GAMMA : gamma  ae d ptr_mem ge e m)
           (AEVAL : aeval_atom te ae d a = OK (d',av))
           (EVAL  : eval_atom arch abs te ge e m tyr a = OK v),
      le_domaing d d' /\
        exists ptr_mem', is_augmented (Pto d) ptr_mem (Pto d') ptr_mem' /\
                           gamma_with_var ae d' ptr_mem' ge e m av tyr v.
  Proof.
    induction a; intros.
    - (* ATrue *)
      simpl in EVAL,AEVAL. inv AEVAL.
      split.
      apply le_domaing_refl.
      exists ptr_mem.
      split.  apply is_augmented_refl.
      constructor; auto.
      eapply val_of_pval_is_primitive_val; eauto.
    - (* AFalse *)
      simpl in EVAL,AEVAL. inv AEVAL.
      split.
      apply le_domaing_refl.
      exists ptr_mem.
      split.  apply is_augmented_refl.
      constructor; auto.
      eapply val_of_pval_is_primitive_val; eauto.
    - (* AInt32 *)
      simpl in EVAL,AEVAL. inv AEVAL.
      split.
      apply le_domaing_refl.
      exists ptr_mem.
      split.  apply is_augmented_refl.
      constructor; auto.
      eapply val_of_pval_is_primitive_val; eauto.
    - (* AInt64 *)
      simpl in EVAL,AEVAL. inv AEVAL.
      split.
      apply le_domaing_refl.
      exists ptr_mem.
      split.  apply is_augmented_refl.
      constructor; auto.
      eapply val_of_pval_is_primitive_val; eauto.
    - (* AConstr *)
      simpl in EVAL,AEVAL. inv AEVAL.
      destruct (btyp_to_typ te b); try discriminate.
      simpl in EVAL.
      destruct (get_enum t); try discriminate.
      destruct p.
      destruct (Benum.make_enum l i); try discriminate.
      simpl in EVAL.
      split.
      apply le_domaing_refl.
      exists ptr_mem.
      split.
      apply is_augmented_refl.
      constructor;auto.
      eapply val_of_pval_is_primitive_val; eauto.
    - (* AVar *)
      simpl in EVAL.
      simpl in AEVAL.
      destruct (eval_var ae (Vars d) i) eqn:EVAR; try discriminate.
      simpl in AEVAL. inv AEVAL.
      split.
      apply le_domaing_refl.
      exists ptr_mem.
      split. apply is_augmented_refl.
      econstructor;eauto.
      destruct GAMMA.
      eapply get_var_correct;eauto.
    - (* Cast *)
      simpl in EVAL.
      destruct (btyp_to_typ te b) eqn:BT; try discriminate.
      simpl in EVAL.
      destruct (typof_atom te a) eqn:TA; try discriminate.
      simpl in EVAL.
      destruct (eval_atom arch abs te ge e m t0 a) eqn:EA; try discriminate.
      simpl in EVAL.
      destruct v0 ; try discriminate.
      (* This is a primitive value *)
      simpl in AEVAL. inv AEVAL.
      split.
      apply le_domaing_refl.
      exists ptr_mem.
      split.
      apply is_augmented_refl.
      constructor ;auto.
      simpl.
      destruct (Barocq.get_cast abs ty t) eqn:GCAST ; try discriminate.
      simpl in EVAL. destruct (r (eval_pval abs p)) eqn:R; try discriminate.
      simpl in EVAL. destruct (pval_of_typ abs t e0) eqn:P; try discriminate.
      simpl in EVAL.
      eapply val_of_pval_is_primitive_val;eauto.
    - (* Unary *)
      simpl in AEVAL. inv AEVAL.
      simpl in EVAL.
      econstructor; eauto.
      apply le_domaing_refl.
      exists ptr_mem; split.
      apply is_augmented_refl.
      destruct (btyp_to_typ te b) eqn: BT; try discriminate.
      simpl in EVAL.
      destruct (eval_atom arch abs te ge e m t a) eqn:EA;try discriminate.
      simpl in EVAL.
      destruct (eval_val abs v0) eqn:EV; try discriminate.
      simpl in EVAL.
      destruct (Barocq.eval_unary_op abs u t e0 tyr) eqn:EU; try discriminate.
      simpl in EVAL.
      apply eval_unary_op_typ_is_prim in EU ; auto.
      constructor ; auto.
      apply gamma_KVar_KPrim; auto.
    - (* Binary *)
      simpl in AEVAL. inv AEVAL.
      simpl in EVAL.
      split.
      apply le_domaing_refl.
      exists ptr_mem. split.
      apply is_augmented_refl.
      constructor ;auto.
      apply gamma_KVar_KPrim.
      destruct (typof_atom te a1) eqn: A1; try discriminate.
      simpl in EVAL.
      destruct (typof_atom te a2) eqn: A2; try discriminate.
      simpl in EVAL.
      destruct (eval_atom arch abs te ge e m t a1) eqn:EA1;try discriminate.
      simpl in EVAL.
      destruct (eval_atom arch abs te ge e m t0 a2) eqn:EA2;try discriminate.
      simpl in EVAL.
      destruct (eval_val abs v0) eqn:EV0; try discriminate.
      simpl in EVAL.
      destruct (eval_val abs v1) eqn:EV1; try discriminate.
      simpl in EVAL.
      destruct (Barocq.eval_binary_op abs b t t0 e0 e1 tyr) eqn:EU; try discriminate.
      simpl in EVAL.
      apply eval_binary_op_typ_is_prim in EU ; auto.
    - (* ArrayGet *)
      simpl in EVAL.
      destruct (typof_atom te a1) eqn:TA1; try discriminate.
      simpl in EVAL.
      destruct (eval_atom arch abs te ge e m t a1) eqn:EA1 ; try discriminate.
      simpl in EVAL.
      destruct (eval_atom arch abs te ge e m (Barocq.typof_index arch) a2) eqn:EA2 ; try discriminate.
      simpl in EVAL.
      destruct (index_of_val arch v1) eqn:IDX; try discriminate.
      simpl in EVAL.
      simpl in AEVAL.
      unfold array_get in AEVAL.
      destruct (aeval_atom te ae d a1) eqn:AEA1; try discriminate.
      destruct p as (d1 & av1).
      destruct (aeval_atom te ae d1 a2) eqn:AEA2; try discriminate.
      destruct p as (d2 & av2).
      destruct av1; try discriminate.
      destruct av2; try discriminate.
      eapply IHa1 in AEA1; eauto.
      destruct AEA1 as (LED1 & (ptr_mem1 & AUG1 & GAMMA_ARR)).
      exploit gamma_with_var_gamma; eauto.
      intro GAMMAD1.
      eapply IHa2 in AEA2; eauto.
      destruct AEA2 as (LED2 & (ptr_mem2 & AUG2 & GAMMA2)).
      clear IHa1 IHa2.
      split.
      + eapply le_domaing_trans; eauto.
        eapply bind_path_le_domain in AEVAL; auto.
        eapply le_domaing_trans;eauto.
        destruct GAMMA2. destruct H;auto.
      + destruct GAMMA2.
        assert (GARR : gamma_KVar (Pto d2) ptr_mem2 ae
                  (KNode n) t v0).
        {
          eapply gamma_KVar_augment; eauto.
          destruct GAMMA_ARR ; auto.
          destruct LED2 ; auto.
        }
        assert (GEDGE : gamma_edge ge e m
                          (EdgeLabel.Index a2) (CIndex i)).
        {
          simpl.
          clear - IDX EA2.
          unfold index_of_val in IDX.
          destruct v1 ; try discriminate.
          assert (ty = arr_index_typ arch).
          { unfold index_of_pval in IDX.
            destruct arch, p ; try discriminate.
            destruct s; try discriminate.
            reflexivity.
            destruct s; try discriminate.
            reflexivity.
          }
          subst.
          do 2 eexists; repeat apply conj ; eauto.
        }
        exploit bind_path_correct  ; eauto.
        *
          destruct H; auto.
        * intros (ptr_memd' & AUG & G).
        exists ptr_memd'.
        { split; auto.
          - eapply is_augmented_trans; eauto.
            destruct LED1 ; auto.
            destruct LED2.
            eapply G.le_graph_trans;eauto.
            exploit bind_path_le_domain ; eauto.
            destruct H;auto.
            intros. destruct H3;auto.
            eapply is_augmented_trans; eauto.
            destruct LED2; auto.
            exploit bind_path_le_domain ; eauto.
            destruct H;auto.
            intro. destruct H1; auto.
        }
    - (* Record projection *)
      simpl in EVAL.
      destruct (typof_atom te a) eqn:TA; try discriminate.
      simpl in EVAL.
      destruct (eval_atom arch abs te ge e m t a) eqn:EA1 ; try discriminate.
      simpl in EVAL.
      simpl in AEVAL.
      unfold record_proj_get in AEVAL.
      destruct (aeval_atom te ae d a) eqn:AEA1; try discriminate.
      destruct p as (d1 & av1).
      destruct av1; try discriminate.
      eapply IHa in AEA1; eauto.
      destruct AEA1 as (LED1 & (ptr_mem1 & AUG1 & GAMMA_ARR)).
      exploit gamma_with_var_gamma; eauto.
      intro GAMMAD1.
      clear IHa.
      split.
      + eapply le_domaing_trans; eauto.
        eapply bind_path_le_domain in AEVAL; auto.
        destruct GAMMAD1;auto.
      + assert (GARR : gamma_KVar (Pto d1) ptr_mem1 ae
                  (KNode n) t v0).
        {
          destruct GAMMA_ARR ; auto.
        }
        assert (GEDGE : gamma_edge ge e m
                          (EdgeLabel.Field i) (CField i)).
        {
          simpl. reflexivity.
        }
        exploit bind_path_correct  ; eauto.
        * destruct GAMMAD1; auto.
        * intros (ptr_memd' & AUG & G).
        exists ptr_memd'.
        { split; auto.
          - eapply is_augmented_trans; eauto.
            destruct LED1; auto.
            exploit bind_path_le_domain ; eauto.
            destruct GAMMAD1;auto.
            intros. destruct H;auto.
        }
    - (* Pure Call *)
      simpl in AEVAL.
      simpl in EVAL.
