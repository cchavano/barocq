From Stdlib Require Import Bool List Btauto.
From compcert Require Import Maps Coqlib.
From BarocqComp Require Import Maps2 BSet Types Syntax Benum Option While Typing Denot.
From BarocqComp Require Pp Printer.
Local Open Scope option_monad_scope.


(** * Abstract syntax *)

  (** ** Expressions *)
Inductive expr : Type :=
  | EAtom : atom -> expr
  | EArraySet : atom -> atom -> atom -> btyp -> expr
  | ERecordUpdate : atom -> ident -> atom -> btyp -> expr
  | EApp : atom -> list atom -> btyp -> expr
  | EIfThenElse : atom -> expr -> expr -> btyp -> expr
  | EMatch : atom -> list (pattern * expr) -> btyp -> expr
  | ELetIn : ident -> expr -> expr -> btyp -> expr
  | EActR : list (ident * atom) -> btyp -> expr
  | ELetW  : list (ident * expr) -> atom -> atom -> expr -> expr -> btyp -> expr
  | EAttr : ident -> expr -> expr.


Section Ind.

  Fixpoint depth (e:expr) : nat :=
    match e with
    | EAtom _ => O
    | EArraySet _ _ _ _ => O
    | ERecordUpdate _ _ _ _ => O
    | EApp _ _ _ => O
    | EIfThenElse _ e1 e2 _ => S (max (depth e1) (depth e2))
    | EMatch _ l _  => S (List.fold_right (fun e acc => max (depth (snd e)) acc) O l)
    | ELetIn _ e1 e2 _ => S (max (depth e1) (depth e2))
    | EActR _ _=> O
    | ELetW  init cond variant body e2 _ =>
        S (max (List.fold_right (fun e acc => max (depth (snd e)) acc) O init) (max (depth body) (depth e2)))
    | EAttr _ e => S (depth e)
    end.

  Variable P : expr -> Prop.
  Variable PAtom : forall a, P (EAtom a).
  Variable PArraySet : forall a i v b, P (EArraySet a i v b).
  Variable PRecordUpdate : forall r fd v b, P (ERecordUpdate r fd v b).
  Variable PAapp : forall f args b, P (EApp f args b).
  Variable PActR : forall l b, P (EActR l b).
  Variable PIte  : forall a e1 e2 b, P e1 -> P e2 -> P (EIfThenElse a e1 e2 b).
  Variable PMatch : forall a l b, (forall p e, In (p,e) l ->  P e) -> P (EMatch a l b).
  Variable PLet : forall x e1 e2 b, P e1 -> P e2 -> P (ELetIn x e1 e2 b).
  Variable PWhile : forall init cond variant body e2 b,
      (forall x e, In (x,e) init -> P e) ->
      P body -> P e2 -> P (ELetW init cond variant body e2 b).
  Variable PAttr : forall a e, P e -> P (EAttr a e).

  Lemma expr_depth_ind : forall e, P e.
  Proof.
    intro.
    remember (depth e) as n.
    revert e Heqn.
    induction n using Wf_nat.lt_wf_ind.
    destruct n.
    - destruct e; simpl; try discriminate; auto.
    - destruct e; simpl; try discriminate.
      + intros. inv Heqn.
      apply PIte. eapply H with (m:= depth e1).
      lia. auto.
      eapply H with (m:= depth e2). lia. auto.
      + intros. inv Heqn.
        apply PMatch.
        intros.
        eapply H with (m:= depth e).
        { clear - H0.
          induction l; simpl; auto.
          -  simpl in H0. tauto.
          - simpl in H0. destruct H0 ; subst.
            simpl. lia. apply IHl in H. lia.
        }
        reflexivity.
      +  intros. inv Heqn.
         apply PLet; auto.
         apply H with (m:= depth e1). lia. reflexivity.
         apply H with (m:= depth e2). lia. reflexivity.
      + intros. inv Heqn.
        apply PWhile.
        intros.
        eapply H with (m:= depth e).
        { clear - H0.
          induction l ; simpl in *.
          tauto.
          destruct H0; subst. simpl.
          lia. apply IHl in H.
          lia.
        } reflexivity.
        apply H with (m:= depth e1). lia. reflexivity.
        apply H with (m:= depth e2). lia. reflexivity.
      +  intros. inv Heqn.
         apply PAttr.
         apply H with (m:= depth e). lia. reflexivity.
  Qed.

End Ind.

Fixpoint btypof_expr (e: expr) : btyp :=
  match e with
  | EAtom a => btypof_atom a
  | EArraySet _ _ _ ty
  | ERecordUpdate _ _ _ ty
  | EApp _ _ ty
  | EIfThenElse _ _ _ ty
  | EMatch _ _ ty
  | ELetIn _ _ _ ty => ty
  | EActR _ ty => ty
  | ELetW _ _ _ _ _ ty  => ty
  | EAttr _ e1 => btypof_expr e1
  end.
  
(** ** Functions *)

Definition function : Type := Syntax.function expr btyp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef expr btyp literal.

Definition prog_types_t := smaplist (type_def (btyp * layout)).

Definition prog_tabs_t := smaplist struct_or_union.


(** ** Programs *)

Definition program : Type := Syntax.program expr btyp literal.

(** Variables of [atom] [expr] *)
Definition singleton (x:ident):= BSet.singleton String.string_dec x.


Definition bset_of_bindings {A: Type} (l : list (ident * A)) :=
  BSet.union_list (fun x => singleton (fst x)) l.

Definition sset_of_bindings {A: Type} (l : list (ident * A)) :=
  SSet.union_list (fun x => SSet.singleton (fst x)) l.

Lemma mem_sset_of_bindings : forall {A: Type} (l:list (ident * A)) x,
    SSet.mem x (sset_of_bindings l) = MapList.mem string_dec x l.
Proof.
  induction l; cbn.
  -  intros. rewrite SSet.mem_empty. reflexivity.
  - intros.
    destruct a. rewrite SSet.mem_union.
    rewrite IHl.
    simpl. rewrite SSet.mem_singleton.
    destruct (string_dec i x); auto.
Qed.


Definition sset_of_bindings_cons : forall {A: Type} e (l:list (ident * A)),
    sset_of_bindings (e::l) = SSet.union (SSet.singleton (fst e)) (sset_of_bindings l).
Proof.
  reflexivity.
Qed.

Lemma bset_of_bindings_eq: forall {A: Type} (l: list (ident * A)) x,
  bset_of_bindings l x = SSet.bset (sset_of_bindings l) x.
Proof.
  unfold bset_of_bindings,sset_of_bindings.
  intros.
  rewrite SSet.bset_union_list.
  apply union_list_morph.
  intros. rewrite SSet.bset_singleton.
  reflexivity.
Qed.

Fixpoint has_var  (e: expr) : BSet.t :=
  match e with
    EAtom a => AtomOrdered.has_var a
  | EArraySet a1 a2 a3 _ => BSet.union (AtomOrdered.has_var a1) (BSet.union (AtomOrdered.has_var a2) (AtomOrdered.has_var a3))
  | ERecordUpdate a1 _ a2 _ => BSet.union (AtomOrdered.has_var a1) (AtomOrdered.has_var a2)
  | EApp a al _ => BSet.union (AtomOrdered.has_var a) (BSet.union_list AtomOrdered.has_var al)
  | EIfThenElse a e1 e2 _ => BSet.union (AtomOrdered.has_var a) (BSet.union (has_var e1) (has_var e2))
  | EMatch a l _ => BSet.union (AtomOrdered.has_var a) (BSet.union_list (fun x => has_var (snd x)) l)
  | ELetIn x e1 e2 _ => BSet.union (has_var e1) (BSet.diff (has_var e2) (singleton x))
  | EActR l _ => BSet.union_list (fun x_a => AtomOrdered.has_var (snd x_a)) l (** ??? *)
  | ELetW init cond variant body e _ =>
      BSet.union (BSet.union_list (fun x_a => has_var (snd x_a)) init)
        (BSet.diff
           (BSet.unionl
              ( BSet.union_list (fun x => has_var (snd x)) init ::
                AtomOrdered.has_var cond:: AtomOrdered.has_var variant :: has_var body :: has_var e::nil))
           (bset_of_bindings init))
  | EAttr _ e => has_var e
  end.



(** [binders e] ignores the scope and simply collect the [let] bindings *)
Section BINDER_REC.

  Variable binders : expr -> @BSet.t ident.

  Definition binders_of_init (init : list (ident * expr)) :=
    BSet.union (bset_of_bindings init)
      (BSet.union_list (fun x_a => binders (snd x_a)) init).
End BINDER_REC.


Fixpoint binders (e:expr) : BSet.t :=
  match e with
    EAtom a => BSet.bot
  | EArraySet a1 a2 a3 _ => BSet.bot
  | ERecordUpdate a1 _ a2 _ => BSet.bot
  | EApp a al _ => BSet.bot
  | EIfThenElse a e1 e2 _ => (BSet.union (binders e1) (binders e2))
  | EMatch a l _ => BSet.union_list (fun x => binders (snd x)) l
  | ELetIn x e1 e2 _ => BSet.union (singleton x)
                          (BSet.union (binders e1) (binders e2))
  | EActR l _ => BSet.bot
  | ELetW init cond variant body e _ =>
      BSet.unionl (binders_of_init binders init ::
                     has_var body :: has_var e::nil)
  | EAttr _ e => binders e
  end.

Fixpoint has_varb (e:expr) : SSet.t :=
  match e with
  | EAtom a => AtomOrdered.has_varb a
  | EArraySet a1 a2 a3 _ => SSet.union (AtomOrdered.has_varb a1) (SSet.union (AtomOrdered.has_varb a2) (AtomOrdered.has_varb a3))
  | ERecordUpdate a1 _ a2 _ => SSet.union (AtomOrdered.has_varb a1) (AtomOrdered.has_varb a2)
  | EApp a1 l _ => SSet.union (AtomOrdered.has_varb a1) (SSet.union_list AtomOrdered.has_varb l)
  | EIfThenElse a1 e1 e2 _ => SSet.union (AtomOrdered.has_varb a1) (SSet.union (has_varb e1) (has_varb e2))
  | EMatch a l _ => SSet.union (AtomOrdered.has_varb a) (SSet.union_list (fun x => has_varb (snd x)) l)
  | ELetIn x e1 e2 _ => SSet.union (has_varb e1) (SSet.remove x (has_varb e2))
  | EActR l _ => (SSet.union_list (fun x => AtomOrdered.has_varb (snd x)) l)
  | ELetW init cond variant body e2 _ =>
      SSet.union (SSet.union_list (fun x_a => has_varb (snd x_a)) init)
        (SSet.diff
           (SSet.unionl
              ( SSet.union_list (fun x => has_varb (snd x)) init ::
                AtomOrdered.has_varb cond:: AtomOrdered.has_varb variant :: has_varb body :: has_varb e2::nil))
           (sset_of_bindings init))
  | EAttr _ e => has_varb e
  end.

Lemma has_var_eq (e:expr) : forall x,
    SSet.bset (has_varb e) x = has_var e x.
Proof.
  induction e using expr_depth_ind; intros; cbn; try rewrite AtomOrdered.has_var_eq.
  - reflexivity.
  - rewrite SSet.bset_union.
    unfold union.
    rewrite SSet.bset_union.
    rewrite! AtomOrdered.has_var_eq.
    unfold union.
    rewrite! AtomOrdered.has_var_eq.
    reflexivity.
  - rewrite SSet.bset_union.
    unfold union.
    rewrite! AtomOrdered.has_var_eq.
    reflexivity.
  - rewrite SSet.bset_union.
    unfold union.
    rewrite! AtomOrdered.has_var_eq.
    f_equal.
    rewrite SSet.bset_union_list.
    apply union_list_morph.
    intros. apply AtomOrdered.has_var_eq.
  - rewrite SSet.bset_union_list.
    apply union_list_morph.
    intros.
    rewrite AtomOrdered.has_var_eq.
    reflexivity.
  - rewrite SSet.bset_union.
    unfold union.
    rewrite AtomOrdered.has_var_eq.
    f_equal.
    rewrite SSet.bset_union.
    unfold union.
    rewrite IHe1. rewrite IHe2.
    reflexivity.
  - rewrite SSet.bset_union.
    unfold union.
    rewrite AtomOrdered.has_var_eq.
    f_equal.
    rewrite SSet.bset_union_list.
    apply union_list_morph.
    intros.
    destruct s; simpl in *.
    eapply H; eauto.
  - rewrite SSet.bset_union.
    unfold union.
    rewrite IHe1.
    f_equal.
    rewrite SSet.bset_remove. unfold diff.
    rewrite IHe2.
    reflexivity.
  - intros.
    rewrite SSet.bset_union.
    unfold union.
    rewrite SSet.bset_union_list.
    f_equal.
    apply union_list_morph.
    intros.
    destruct s. simpl. eapply H;eauto.
    rewrite SSet.bset_diff.
    unfold diff.
    rewrite SSet.bset_union.
    unfold union.
    rewrite SSet.bset_union_list.
    f_equal.
    f_equal.
    apply union_list_morph.
    intros.
    destruct s; simpl in *.
    eapply H; eauto.
    rewrite SSet.bset_union.
    unfold union.
    rewrite SSet.bset_union.
    unfold union.
    rewrite SSet.bset_union.
    unfold union.
    rewrite SSet.bset_union.
    unfold union.
    rewrite IHe1. rewrite IHe2.
    rewrite SSet.bset_empty.
    rewrite! AtomOrdered.has_var_eq.
    reflexivity.
    rewrite bset_of_bindings_eq. reflexivity.
  - apply IHe.
Qed.

(** * Expression well-formdness *)

(** An expression [e] is well-formed w.r.t. a set of global and local symbols [globs] and [locals]
    if all of the following conditions are met:
    - Bindings in [e] don't shadow identifiers in [globs] and [locals];
    - There is no variable shadowing in [e];
    - [e] is closed. *)

Section WF.
  
  Variable globs: SSet.t.

  Definition var_defined (locals: SSet.t) (x: ident) : bool :=
    (SSet.mem x locals) || (SSet.mem x globs).


  Fixpoint wf_atom (locals: SSet.t) (a: atom) : bool :=
    match a with
    | ATrue | AFalse
    | AInt32 _ _ | AInt64 _ _
    | AConstr _ _ _ => true
    | AVar x _ => var_defined locals x
    | ACast a1 _
    | AUnaryOp _ a1 _
    | ARecordProj a1 _ _ _ => wf_atom locals a1
    | ABinaryOp _ a1 a2 _
    | AArrayGet a1 a2 _ _ =>
        (wf_atom locals a1) && (wf_atom locals a2)
    | APureCall f _ args _ =>
        (var_defined locals f) && (List.forallb (wf_atom locals) args)
  end.

  Definition wf_binding_syntax (bds:SSet.t) (id_expr : ident * expr) :=
    SSet.is_empty (SSet.inter (has_varb (snd id_expr)) bds).

  Definition wf_init_for_binders (bds:SSet.t) (l:list (ident*expr)) :=
    List.forallb (wf_binding_syntax bds) l.

  Definition wf_init_syntax (l:list (ident * expr)) :=
    wf_init_for_binders (sset_of_bindings l) l.

  Lemma wf_init_for_binders_cons : forall s e l,
      wf_init_for_binders s (e::l) = wf_init_for_binders s l && wf_binding_syntax s e.
  Proof.
    unfold wf_init_for_binders.
    simpl. intros. rewrite andb_comm. reflexivity.
  Qed.

  Lemma wf_binding_syntax_union : forall s1 s2 a,
      wf_binding_syntax (SSet.union s1 s2) a = (wf_binding_syntax s1 a && wf_binding_syntax s2 a).
  Proof.
    unfold wf_binding_syntax.
    intros.
    generalize (has_varb (snd a)).
    intros.
    destruct (SSet.is_empty (SSet.inter t s1)) eqn:E1; simpl.
    rewrite <- SSet.is_empty_iff.
    rewrite SSet.bset_is_empty in E1.
    unfold is_empty,bot,subset in *.
    split; intros.
    - specialize (H x).
    specialize (E1 x).
    rewrite SSet.bset_inter in *.
    unfold inter in *.
    rewrite SSet.bset_union in *.
    unfold union in *.
    rewrite! andb_true_iff in *.
    rewrite! orb_true_iff in *.
    tauto.
    - specialize (H x).
    specialize (E1 x).
    rewrite SSet.bset_inter in *.
    unfold inter in *.
    rewrite SSet.bset_union in *.
    unfold union in *.
    rewrite! andb_true_iff in *.
    rewrite! orb_true_iff in *.
    tauto.
   - rewrite <- not_true_iff_false in *.
     rewrite SSet.bset_is_empty in *.
     intro.
     apply E1.
     unfold is_empty,bot,subset in *.
     intros.
     specialize (H x).
     rewrite SSet.bset_inter in *.
     unfold inter in *.
     rewrite SSet.bset_union in *.
     unfold union in *.
     rewrite! andb_true_iff in *.
     rewrite orb_true_iff in *.
     tauto.
  Qed.



  
  Lemma wf_init_for_binders_union : forall s1 s2 l,
      wf_init_for_binders (SSet.union s1 s2) l = wf_init_for_binders s1 l && wf_init_for_binders s2 l.
  Proof.
    induction l; simpl; auto.
    rewrite IHl.
    rewrite wf_binding_syntax_union.
    btauto.
  Qed.


  Lemma wf_init_syntax_iff : forall e l ,
      wf_init_syntax (e::l) = wf_init_syntax l && wf_binding_syntax (sset_of_bindings l) e
                              && wf_init_for_binders (SSet.singleton (fst e)) l
                              && wf_binding_syntax (SSet.singleton (fst e)) e.
  Proof.
    unfold wf_init_syntax.
    intros.
    rewrite sset_of_bindings_cons.
    rewrite wf_init_for_binders_cons.
    rewrite wf_init_for_binders_union.
    rewrite wf_binding_syntax_union.
    btauto.
  Qed.


  Section WFREC.
    Variable wf_expr : SSet.t -> expr -> bool.

    Definition wf_binding (locals : SSet.t) (x_ei : ident * expr) :=
      negb (SSet.mem (fst x_ei) globs) &&
        negb (SSet.mem (fst x_ei) locals) &&
        wf_expr locals (snd x_ei).

    Fixpoint wf_init (locals : SSet.t) (l : list (ident * expr)) :=
      match l with
      | nil => true
      | b::l => wf_binding locals b &&
                  wf_init locals l &&
                  wf_init (SSet.add (fst b) locals) l
      end.

    Lemma wf_init_mem1 : forall l i locals,
        SSet.mem i locals = true ->
        wf_init locals l = true ->
        MapList.mem string_dec i l = false.
    Proof.
      induction l; simpl; auto.
      intros.
      rewrite andb_true_iff in H0.
      destruct a.
      simpl in *.
      destruct (string_dec i0 i).
      - subst. unfold wf_binding in H0.
        rewrite! andb_true_iff in H0.
        simpl in H0.
        rewrite! negb_true_iff in H0.
        intuition congruence.
      - rewrite andb_true_iff in H0.
        eapply IHl; eauto.
        tauto.
    Qed.

    Lemma wf_init_mem2 : forall l i locals,
        SSet.mem i globs = true ->
        wf_init locals l = true ->
        MapList.mem string_dec i l = false.
    Proof.
      induction l; simpl; auto.
      intros.
      rewrite! andb_true_iff in H0.
      destruct a.
      simpl in *.
      destruct (string_dec i0 i).
      - subst. unfold wf_binding in H0.
        rewrite! andb_true_iff in H0.
        simpl in H0.
        rewrite! negb_true_iff in H0.
        intuition congruence.
      - intuition idtac.
        eapply IHl; eauto.
    Qed.


    Lemma wf_init_no_dup : forall locals l,
        wf_init locals l = true ->
        MapList.nodup String.string_dec l = true.
    Proof.
      induction l; simpl; auto.
      - destruct a ; simpl; intros.
        rewrite! andb_true_iff in H.
        unfold wf_binding in H.
        simpl in H.
        rewrite! andb_true_iff in H.
        rewrite! negb_true_iff in H.
        destruct (MapList.mem string_dec i l) eqn:MEM.
        + assert (MapList.mem string_dec i l = false).
        { apply wf_init_mem1 with (locals:=SSet.add i locals).
          rewrite SSet.mem_add.
          destruct (string_dec i i); try congruence.
          tauto.
        }
        congruence.
        + apply IHl.
          tauto.
    Qed.





  End WFREC.

  Definition add_bindings {A: Type} (locals : SSet.t) (l : list (ident * A)) :=
    List.fold_right (fun i loc => SSet.add (fst i) loc) locals l.

  Fixpoint wf_expr (locals: SSet.t) (e: expr) : bool :=
    match e with
    | EAtom a => wf_atom locals a
    | EArraySet a1 a2 a3 _ =>
        (wf_atom locals a1) && (wf_atom locals a2) && (wf_atom locals a3)
    | ERecordUpdate a1 _ a2 _ =>
        (wf_atom locals a1) && (wf_atom locals a2)
    | EApp f args _ =>
        (wf_atom locals f) && (List.forallb (wf_atom locals) args)
    | EIfThenElse a e1 e2 _ =>
        (wf_atom locals a) && (wf_expr locals e1) && (wf_expr locals e2)
    | EMatch a cases _ =>
        (wf_atom locals a) && List.forallb (fun '(_, ei) => (wf_expr locals) ei) cases
    | ELetIn x e1 e2 _ =>
        negb (SSet.mem x globs)
        && negb (SSet.mem x locals)
        && (wf_expr locals e1)
        && (wf_expr (SSet.add x locals) e2)
    | EActR l _ => List.forallb (fun x => wf_atom locals (snd x)) l (** fst belongs to locals ? *)
    | ELetW l cond decr bdy e2 _ =>
        wf_init_syntax l &&
        wf_init wf_expr locals l
        &&
          (let locals' := add_bindings  locals l in
           wf_atom locals' cond &&
             wf_atom locals' decr &&
             wf_expr locals' bdy &&  wf_expr locals' e2)
    | EAttr _ e1 => wf_expr locals e1
    end.

  Section S.
    Context {A: Type}.
    Variable P : A -> Prop.

    Fixpoint ForallP (l :list A) :=
      match l with
      | nil => True
      | e::l => P e /\ ForallP l
      end.
  End S.


  Lemma andb_intro : forall a1 b1 a2 b2,
      a1 = a2 -> b1 = b2 ->
      a1 && b1  = a2 && b2.
  Proof.
    intros. congruence.
  Qed.


  Lemma forallb_eq : forall {A: Type} (P Q: A -> bool) args,
    (forall x, In x args ->  P x = Q x) ->
      forallb P args = forallb Q args.
  Proof.
    induction args; simpl; auto.
    intros.
    apply andb_intro.
    apply H. tauto.
    apply IHargs;auto.
  Qed.

  Lemma wf_atom_morph : forall a loc1 loc2,
      (forall x, SSet.mem x loc1 = SSet.mem x loc2) ->
    wf_atom loc1 a = wf_atom loc2 a.
  Proof.
    induction a using atom_depth_ind; simpl; auto.
    - unfold var_defined.
      intros. rewrite H. tauto.
    - intros.
      f_equal;auto.
    - intros;f_equal;auto.
    - intros. f_equal;auto.
      unfold var_defined;intros. rewrite H0. reflexivity.
      apply forallb_eq.
      intros.
      apply H; auto.
  Qed.

    
  Lemma mem_add_bindings_eq : forall {A: Type} loc1 loc2  (init: list (ident * A))
      (EQ: forall x : StringIndexed.t, SSet.mem x loc1 = SSet.mem x loc2),
      forall x, SSet.mem x (add_bindings loc1 init) =  SSet.mem x (add_bindings loc2 init).
  Proof.
    induction init ; simpl; auto.
    intros. rewrite! SSet.mem_add.
    destruct a; simpl.
    destruct (string_dec x i);auto.
  Qed.

  Lemma wf_expr_morph : forall e loc1 loc2,
      (forall x, SSet.mem x loc1 = SSet.mem x loc2) ->
    wf_expr loc1 e = wf_expr loc2 e.
  Proof.
    induction e using expr_depth_ind; simpl; intros;
      repeat apply andb_intro; try (apply wf_atom_morph;assumption);
      auto.
    - apply forallb_eq.
      intros ; apply wf_atom_morph;auto.
    - apply forallb_eq.
      intros ; apply wf_atom_morph;auto.
    - apply forallb_eq.
      intros ; destruct x;auto.
      eapply H;eauto.
    - rewrite H. tauto.
    - apply IHe2.
      intros.
      rewrite! SSet.mem_add.
      rewrite H.
      reflexivity.
    - clear IHe1 IHe2.
      revert loc1 loc2 H0.
      induction init; simpl; auto.
      intros.
      repeat apply andb_intro.
      reflexivity. rewrite H0. reflexivity.
      destruct a; simpl in *.
      eapply H; eauto.
      apply IHinit.
      intros. eapply H; eauto. simpl. right; eauto.
      auto. apply IHinit;auto.
      intros. eapply H; eauto. simpl. right; eauto.
      intros. rewrite! SSet.mem_add.
      rewrite H0. reflexivity.
    - apply wf_atom_morph.
      intros.
      clear - H0.
      revert loc1 loc2 H0.
      induction init ; simpl; auto.
      intros.
      rewrite! SSet.mem_add.
      destruct a; simpl.
      destruct (string_dec x i); auto.
    - apply wf_atom_morph.
      apply mem_add_bindings_eq; auto.
    - apply IHe1.
      apply mem_add_bindings_eq; auto.
    - apply IHe2.
      apply mem_add_bindings_eq; auto.
  Qed.

  Section WFREC.
    Variable wf_expr : expr -> Prop.

    Definition wf_binding2 (locals : @BSet.t ident) (x_ei : ident * expr) :=
      BSet.is_empty (BSet.inter (has_var (snd x_ei)) locals) /\
        wf_expr (snd x_ei).

  End WFREC.

  
  Fixpoint wf_expr2  (e: expr) {struct e}: Prop :=
    match e with
    | EAtom a => True
    | EArraySet a1 a2 a3 _ => True
    | ERecordUpdate a1 _ a2 _ => True
    | EApp f args _ => True
    | EIfThenElse a e1 e2 _ =>
        wf_expr2 e1 /\ wf_expr2 e2
    | EMatch a cases _ =>
        ForallP (fun '(_, ei) => wf_expr2 ei) cases
    | ELetIn x e1 e2 _ =>
        wf_expr2 e1 /\
          wf_expr2 e2 /\
          (is_empty (inter (diff (has_var e2) (singleton x))
                           (binders e1)))
    | EActR l _ => True
    | ELetW l cond decr bdy e2 _ =>
        let bd := bset_of_bindings l in
        ForallP (wf_binding2 wf_expr2 bd) l /\
          MapList.nodup string_dec l = true /\
          let vcont := unionl
                         (AtomOrdered.has_var cond ::
                            AtomOrdered.has_var decr ::
                            has_var bdy :: has_var e2::nil) in
          (is_empty (inter
                       (diff vcont bd)
                       (union_list (fun x_e => binders (snd x_e))
                                   l))) /\
          wf_expr2  bdy /\ wf_expr2  e2 /\


          is_empty (inter bd (binders bdy)) /\
          is_empty (inter bd (binders e2))
    | EAttr _ e1 => wf_expr2 e1
    end.



(*
  Fixpoint wf_expr3 (binders: SSet.t) (e: expr) : bool :=
    match e with
    | EAtom a => true
    | EArraySet a1 a2 a3 _ => true
    | ERecordUpdate a1 _ a2 _ => true
    | EApp f args _ => true
    | EIfThenElse a e1 e2 _ =>
        wf_expr3 binders e1 && wf_expr3 binders e2
    | EMatch a cases _ =>
        List.forallb (fun '(_, ei) => (wf_expr3 binders) ei) cases
    | ELetIn x e1 e2 _ =>
        wf_expr3 binders e1 &&  wf_expr2 e2 && negb (binders e2 x)
    | EActR l _ => true
    | ELetW l cond decr bdy e2 _ =>
        wf_init2 wf_expr2 l && wf_expr2 bdy && wf_expr2 e2 &&
          List.forallb (fun x => negb (binders bdy x) && negb (binders e2 x)) (List.map fst l)
    | EAttr _ e1 => wf_expr2  e1
    end.
*)





(*Lemma wf_init_cons : forall  k2 wf b l,
    wf_init wf k2 (b :: l) = true <->
      (wf_init wf k2 l = true /\
         wf_binding  wf k2 b = true /\
         MapList.mem String.string_dec (fst b) l = false).
Proof.
  unfold wf_init.
  intros.
  simpl.
  destruct b.
  rewrite! andb_true_iff.
  simpl.
  destruct (MapList.mem String.string_dec i l) eqn:MEM.
  intuition congruence.
  tauto.
Qed.
*)

End WF.

(** * Pretty-printing *)

Module Pp.
  Import Pp Printer.
  Import String.

  Fixpoint pp_expr (e:expr) : box :=
    match e with
    | EAtom a => Printer.pp_atom a
    | EArraySet a i v _ => Pp.seq (Printer.pp_atom a :: Bstr "[" :: Printer.pp_atom i :: Bstr "] <- " :: Printer.pp_atom v :: nil)
    | ERecordUpdate a fd v _ => Pp.seq (Printer.pp_atom a :: Bstr "." :: Bstr fd :: Bstr " <- " :: Printer.pp_atom v :: nil)
    | EApp a l _ => Pp.seq (Printer.pp_atom a :: Bstr "(" :: pp_list (Bstr ", ") Printer.pp_atom l :: Bstr ")" :: nil)
    | EMatch a cases _ =>
        pp_match pp_atom pp_expr "match " a cases
    | EIfThenElse c t e _ => Bstack
                             (Bcat (Bstr "if ") (Printer.pp_atom c))
                             (Bstack (Bcat (Bstr "then ") (pp_expr t))
                                     (Bcat (Bstr "else ") (pp_expr e)) Left) Left
    | ELetIn id e1 e2 _ => Bstack (Pp.seq (Bstr "let " :: Bstr id :: Bstr " = " :: pp_expr e1 :: nil))
                             (Bcat (Bstr "in ") (pp_expr e2)) Left
    | EActR l _ =>
        (Pp.seq (Bstr "{" :: pp_list (Bstr ", ") (fun '(x,e) => Pp.seq (Bstr x :: Bstr " <- " :: pp_atom e :: nil)) l :: Bstr "}"::nil))
    | ELetW init cond variant body e2 _ =>
        Bstack (Pp.seq (Bstr "let {" :: pp_list (Bstr ", ") (fun '(x,e) => Pp.seq (Bstr x :: Bstr " <- " :: pp_expr e :: nil)) init :: Bstr "} = "::
                          Bstr "while " :: pp_atom cond :: Bstr " decr " :: pp_atom variant :: Bstr " do " ::
                          pp_expr body :: Bstr " done " :: nil))
               (Bcat (Bstr "in ") (pp_expr e2)) Left
    | EAttr id e => Pp.seq (Bstr "#[ " :: Bstr id :: Bstr " ]"  :: pp_expr e :: nil)
    end.

  Definition pp_program (p:program) : box :=
    Printer.pp_program Printer.pp_btyp  Printer.pp_literal pp_expr p.

End Pp.

(** * Denotational semantics *)

Section DENOT.

  Variable tabs : PMap.t Type.

  Notation genv := (@Denot.genv tabs).

  Notation lenv := (@Denot.lenv tabs).

  Notation value := (@Denot.value tabs).

  Notation eval_typ := (eval_typ tabs).

  Notation eval_atom := (@Denot.eval_atom tabs).

  Definition typof_expr (te:tenv) (e:expr) : option typ :=
    btyp_to_typ te (btypof_expr e).

  Section EVALEXPR.
    (** This is parallel evaluation *)
    Variable eval_expr : lenv -> forall (ty:typ), expr -> option (eval_typ ty).

    Fixpoint update_para_lenv (te:tenv) (le0 :lenv) (l:list (ident * expr)) (le:lenv) : option lenv :=
      match l with
      | nil => Some le
      | xe::l   => let* ty := typof_expr te (snd xe) in
                   let* v := eval_expr le0 ty (snd xe) in
                   update_para_lenv te le0 l (lenv_update tabs le (fst xe) (Val _ ty v))
      end.

    (** This is sequencial evaluation *)
    Fixpoint update_seq_lenv (te:tenv)  (l:list (ident * expr)) (le:lenv) : option lenv :=
      match l with
      | nil => Some le
      | xe::l   => let* ty := typof_expr te (snd xe) in
                   let* v := eval_expr le ty (snd xe) in
                   update_seq_lenv te l (lenv_update tabs le (fst xe) (Val _ ty v))
      end.


    Lemma match_env_update1 : forall   (ge:Denot.genv tabs) (le : Denot.lenv tabs) (k : ident) (v : Denot.value tabs),
        STree.get k le = None ->
        STree.get k ge = None ->
        match_env tabs ge  le ge (lenv_update tabs le k v).
    Proof.
      unfold match_env, lenv_update.
      unfold get_env. intros.
      rewrite STree.gsspec.
      destruct (STree.elt_eq x k).
      - subst. rewrite H. rewrite H0. constructor.
      - constructor.
    Qed.



    Lemma less_def_update :
      forall (ge:genv) te
             (EVAL_EXPR : forall le1 le2 ty e1, match_env tabs ge le1 ge le2 ->
                                                less_def (eval_expr le1 ty e1)
                                                  (eval_expr le2 ty e1))
             l le0 le
             (WF : wf_init (STree.keys ge) (wf_expr (STree.keys ge)) (STree.keys le0) l = true)
             (MATCH  : match_env tabs ge le0 ge le)      ,
             less_def  (update_para_lenv te le0 l le) (update_seq_lenv te l le).
    Proof.
      induction l; simpl.
      - intros. constructor.
      - intros.
        apply less_def_bind_eq.
        intros.
        apply less_def_bind_less_def.
        apply EVAL_EXPR; auto.
        intros.
        eapply IHl;eauto.
        { rewrite! andb_true_iff in WF.
          tauto. }
        {
          unfold wf_binding in WF.
          rewrite! andb_true_iff in WF.
          rewrite! negb_true_iff in WF.
          (*rewrite wf_init_cons in WF.
          destruct WF as (WF1 & WF2 & WF3).
          unfold wf_binding in WF2.
          rewrite! andb_true_iff in WF2.
          rewrite! negb_true_iff in WF2. *)
          eapply match_env_trans.
          apply match_env_update1 with (k:= fst a).
          - rewrite STree.keys_get_mem_false_iff.
            tauto.
          - rewrite STree.keys_get_mem_false_iff.
            tauto.
          -
          apply match_env_update; auto.
        }
    Qed.


    Lemma update_para_lenv_None :
      forall (ge:genv) te
             (EVAL_EXPR_LD : forall le1 le2 ty e1, match_env tabs ge le1 ge le2 ->
                                                less_def (eval_expr le1 ty e1)
                                                  (eval_expr le2 ty e1))
             (l:list (ident * expr))
             le0 le
             (WF : wf_init (STree.keys ge) (wf_expr (STree.keys ge)) (STree.keys le0) l = true)
             (EVAL_EXPR_None : forall  le2 ty id e1, match_env tabs ge le0 ge le2 ->
                                                        In (id,e1) l ->
                                                        eval_expr le0 ty e1 = None ->
                                                        eval_expr le2 ty e1 = None)


             (MATCH  : match_env tabs ge le0 ge le)
              ,
                update_para_lenv te le0 l le = None ->
                update_seq_lenv te l le = None.
    Proof.
      induction l; simpl.
      - intros. discriminate.
      - intros.
        unfold wf_binding in WF.
        rewrite! andb_true_iff  in WF.
        rewrite! negb_true_iff in WF.
        destruct (typof_expr te (snd a)); try reflexivity.
        simpl in *.
        assert (LD : less_def (eval_expr le0 t (snd a))
                         (eval_expr le t (snd a))).
        {
          apply EVAL_EXPR_LD; auto.
        }
        inv LD.
        rewrite <- H1 in H. clear H.
        symmetry in H1.
        destruct (eval_expr le t (snd a)) eqn:EE; try reflexivity.
        destruct a as (id1,a) ; simpl in *.
        eapply EVAL_EXPR_None in H1.
        rewrite EE in H1. discriminate.
        auto.
        left; reflexivity.
        destruct (eval_expr le0 t (snd a)).
        simpl in *.
        eapply IHl ; eauto.
        tauto.
        eapply match_env_trans.
        apply match_env_update1 with (k:= fst a).
        + rewrite STree.keys_get_mem_false_iff.
          tauto.
        + rewrite STree.keys_get_mem_false_iff.
          tauto.
        + apply match_env_update; auto.
        + reflexivity.
    Qed.


(*
    Lemma update_para_lenv_None :
      forall (ge:genv) te
             (EVAL_EXPR_LD : forall le1 le2 ty e1, match_env tabs ge le1 ge le2 ->
                                                less_def (eval_expr le1 ty e1)
                                                  (eval_expr le2 ty e1))
             (l:list (ident * expr))
             (EVAL_EXPR_None : forall le1 le2 ty id e1, match_env tabs ge le1 ge le2 ->
                                                     In (id,e1) l ->
                                                     eval_expr le1 ty e1 = None ->
                                                     eval_expr le2 ty e1 = None)

             le0 le
             (WF : wf_init (STree.keys ge) (wf_expr (STree.keys ge)) (STree.keys le0) l = true)
             (MATCH  : match_env tabs ge le0 ge le)
              ,
                update_para_lenv te le0 l le = None ->
                update_seq_lenv te l le = None.
    Proof.
      induction l; simpl.
      - intros. discriminate.
      - intros.
        unfold wf_binding in WF.
        rewrite! andb_true_iff  in WF.
        rewrite! negb_true_iff in WF.
        destruct (typof_expr te (snd a)); try reflexivity.
        simpl in *.
        assert (LD : less_def (eval_expr le0 t (snd a))
                         (eval_expr le t (snd a))).
        {
          apply EVAL_EXPR_LD; auto.
        }
        inv LD.
        rewrite <- H1 in H. clear H.
        symmetry in H1.
        destruct (eval_expr le t (snd a)) eqn:EE; try reflexivity.
        destruct a as (id1,a) ; simpl in *.
        eapply EVAL_EXPR_None in H1.
        rewrite EE in H1. discriminate.
        auto.
        left; reflexivity.
        destruct (eval_expr le0 t (snd a)).
        simpl in *.
        eapply IHl ; eauto.
        tauto.
        eapply match_env_trans.
        apply match_env_update1 with (k:= fst a).
        + rewrite STree.keys_get_mem_false_iff.
          tauto.
        + rewrite STree.keys_get_mem_false_iff.
          tauto.
        + apply match_env_update; auto.
        + reflexivity.
    Qed.
*)


  End EVALEXPR.

  Fixpoint eval_expr_rec (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr) : option (eval_typ ty) :=
    match e with
    | EAtom a =>
        let* ta := typof_atom te a in
        ecast_typ tabs (eval_atom te ge le ta a) ty
    | EArraySet a1 a2 a3 bt =>
        let* t := btyp_to_typ te bt in
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* ta3 := typof_atom te a3 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        let* v3 := eval_atom te ge le ta3 a3 in
        ecast_typ tabs (eval_array_set tabs ta1 v1 ta2 v2 ta3 v3 t) ty
    | ERecordUpdate a1 k a2 bt =>
        let* t := btyp_to_typ te bt in
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        ecast_typ tabs (eval_record_update tabs ta1 v1 k ta2 v2 t) ty
    | EApp f args btr =>
        let* tr := btyp_to_typ te btr in
        let* tf := typof_atom te f in
        match tf with
        | TFun tparams tret =>
            let* f := eval_atom te ge le  (TFun tparams tret) f in
            let* vargs := DList.map2 _ (eval_atom te ge le) args tparams in
            ecast_typ tabs (eval_app_option tabs tparams tret f vargs tr) ty
            (*let* vargs := DList.mmap _ (eval_atom te ge le) args tparams in
            eval_app tabs tparams tret f vargs ty *)
        |  _  => fail
        end
    | EIfThenElse a1 e2 e3 _ =>
        let* v1 := eval_atom te ge le TBool a1  in
        if v1 then eval_expr_rec te ge le ty e2
        else eval_expr_rec te ge le ty e3
    | EMatch a1 cases _  =>
        let* ta1:= typof_atom te a1 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let vcases := MapList.map (eval_expr_rec te ge le ty) cases in
        eval_match tabs ta1 v1 vcases
    | ELetIn x e1 e2 _ =>
        let* te1 := typof_expr te e1 in
        let* v1 := eval_expr_rec te ge le te1 e1 in
        let le' := lenv_update tabs le x (Val tabs te1 v1) in
        eval_expr_rec te ge le' ty e2
    | EActR l bt =>
        match ty with
        | TRecord None lty =>
            let* ty1 := Typing.btyp_to_typ te bt in
            if typ_eqb ty ty1
            then
            eval_act_record tabs eval_atom te ge  l lty le
            else None
        |   _            => None
        end
    | ELetW init cond decr body e2 _ =>
        (** Evaluate the initialisation in the initial environment *)
        let* le' := update_para_lenv (eval_expr_rec te ge) te le init le  in
        let* tyd := typof_atom te decr in
        let* m := eval_atom te ge le' tyd decr in
        let* n := nat_of_val _ m in
        let* tyb := MapList.mmap _  (typof_expr te) init in
        let* initr := record_of_lenv tabs ge tyb le' in
        let C := fun r =>
                   eval_atom te ge (lenv_of_record _ _ r le') TBool cond in
        let B := fun r => eval_expr_rec te ge (lenv_of_record _ _ r le') (TRecord None tyb) body in
        let* whiler := while C B n initr in
        eval_expr_rec te ge (lenv_of_record _ _ whiler le') ty e2
    | EAttr _ e1 => eval_expr_rec te ge le ty e1
    end.

  Lemma eval_expr_rec_rw : forall (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr),

      eval_expr_rec te ge le ty e =
    match e with
    | EAtom a =>
        let* ta := typof_atom te a in
        ecast_typ tabs (eval_atom te ge le ta a) ty
    | EArraySet a1 a2 a3 bt =>
        let* t := btyp_to_typ te bt in
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* ta3 := typof_atom te a3 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        let* v3 := eval_atom te ge le ta3 a3 in
        ecast_typ tabs (eval_array_set tabs ta1 v1 ta2 v2 ta3 v3 t) ty
    | ERecordUpdate a1 k a2 bt =>
        let* t := btyp_to_typ te bt in
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        ecast_typ tabs (eval_record_update tabs ta1 v1 k ta2 v2 t) ty
    | EApp f args btr =>
        let* tr := btyp_to_typ te btr in
        let* tf := typof_atom te f in
        match tf with
        | TFun tparams tret =>
            let* f := eval_atom te ge le  (TFun tparams tret) f in
            let* vargs := DList.map2 _ (eval_atom te ge le) args tparams in
            ecast_typ tabs (eval_app_option tabs tparams tret f vargs tr) ty
            (*let* vargs := DList.mmap _ (eval_atom te ge le) args tparams in
            eval_app tabs tparams tret f vargs ty *)
        |  _  => fail
        end
    | EIfThenElse a1 e2 e3 _ =>
        let* v1 := eval_atom te ge le TBool a1  in
        if v1 then eval_expr_rec te ge le ty e2
        else eval_expr_rec te ge le ty e3
    | EMatch a1 cases _  =>
        let* ta1:= typof_atom te a1 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let vcases := MapList.map (eval_expr_rec te ge le ty) cases in
        eval_match tabs ta1 v1 vcases
    | ELetIn x e1 e2 _ =>
        let* te1 := typof_expr te e1 in
        let* v1 := eval_expr_rec te ge le te1 e1 in
        let le' := lenv_update tabs le x (Val tabs te1 v1) in
        eval_expr_rec te ge le' ty e2
    | EActR l bt =>
        match ty with
        | TRecord None lty =>
            let* ty1 := Typing.btyp_to_typ te bt in
            if typ_eqb ty ty1
            then
            eval_act_record tabs eval_atom te ge  l lty le
            else None
        |   _            => None
        end
    | ELetW init cond decr body e2 _ =>
        let* le' := update_para_lenv (eval_expr_rec te ge) te le init le  in
        let* tyd := typof_atom te decr in
        let* m := eval_atom te ge le' tyd decr in
        let* n := nat_of_val _ m in
        let* tyb := MapList.mmap _ (typof_expr te) init in
        let* initr := record_of_lenv tabs ge tyb le' in
        let C := fun (r: eval_recordtyp eval_typ tyb) =>
                   eval_atom te ge (lenv_of_record _ _ r le') TBool cond in
        let B := fun r => eval_expr_rec te ge (lenv_of_record _ _ r le') (TRecord None tyb) body in
        let* whiler := while C B n initr in
        eval_expr_rec te ge (lenv_of_record _ _ whiler le') ty e2
    | EAttr _ e1 => eval_expr_rec te ge le ty e1
    end.
  Proof.
    destruct e; reflexivity.
  Qed.

  Definition eval_expr_rec2 (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr) : option (eval_typ ty) :=
    match e with
    | EAtom a =>
        let* ta := typof_atom te a in
        ecast_typ tabs (eval_atom te ge le ta a) ty
    | EArraySet a1 a2 a3 bt =>
        let* t := btyp_to_typ te bt in
        ecast_typ tabs(
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* ta3 := typof_atom te a3 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        let* v3 := eval_atom te ge le ta3 a3 in
        (eval_array_set tabs ta1 v1 ta2 v2 ta3 v3 t)) ty
    | ERecordUpdate a1 k a2 bt =>
        let* t := btyp_to_typ te bt in
        ecast_typ tabs
          (let* ta1 := typof_atom te a1 in
          let* ta2 := typof_atom te a2 in
          let* v1 := eval_atom te ge le ta1 a1 in
          let* v2 := eval_atom te ge le ta2 a2 in
          (eval_record_update tabs ta1 v1 k ta2 v2 t)) ty
    | EApp f args btr =>
        let* tr := btyp_to_typ te btr in
        ecast_typ tabs
          (let* tf := typof_atom te f in
        match tf with
        | TFun tparams tret =>
            let* f := eval_atom te ge le  (TFun tparams tret) f in
            let* vargs := DList.map2 _ (eval_atom te ge le) args tparams in
            (eval_app_option tabs tparams tret f vargs tr)
            (*let* vargs := DList.mmap _ (eval_atom te ge le) args tparams in
            eval_app tabs tparams tret f vargs ty *)
        |  _  => fail
        end) ty
    | EIfThenElse a1 e2 e3 _ =>
        let* v1 := eval_atom te ge le TBool a1  in
        if v1 then eval_expr_rec te ge le ty e2
        else eval_expr_rec te ge le ty e3
    | EMatch a1 cases _  =>
        let* ta1:= typof_atom te a1 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let vcases := MapList.map (eval_expr_rec te ge le ty) cases in
        eval_match tabs ta1 v1  vcases
    | ELetIn x e1 e2 _ =>
        let* te1 := typof_expr te e1 in
        let* v1 := eval_expr_rec te ge le te1 e1 in
        let le' := lenv_update tabs le x (Val tabs te1 v1) in
        eval_expr_rec te ge le' ty e2
    | EActR l bt =>
        match ty with
        | TRecord None lty =>
            let* ty1 := Typing.btyp_to_typ te bt in
            if typ_eqb ty ty1
            then
            eval_act_record tabs eval_atom te ge  l lty le
            else None
        |   _            => None
        end
    | ELetW init cond decr body e2 _ =>
        (** Evaluate the initialisation in the initial environment *)
        let* le' := update_para_lenv (eval_expr_rec te ge) te le init le  in
        let* tyd := typof_atom te decr in
        let* m := eval_atom te ge le' tyd decr in
        let* n := nat_of_val _ m in
        let* tyb := MapList.mmap _  (typof_expr te) init in
        let* initr := record_of_lenv tabs ge tyb le' in
        let C := fun r =>
                   eval_atom te ge (lenv_of_record _ _ r le') TBool cond in
        let B := fun r => eval_expr_rec te ge (lenv_of_record _ _ r le') (TRecord None tyb) body in
        let* whiler := while C B n initr in
        eval_expr_rec te ge (lenv_of_record _ _ whiler le') ty e2
    | EAttr _ e1 => eval_expr_rec te ge le ty e1
    end.



Lemma lenv_of_record_update : forall rt r le s v,
    In s (map fst rt) ->
    lenv_of_record tabs rt r
      (lenv_update tabs le s v) =
      lenv_of_record tabs rt r le.
Proof.
  induction rt; simpl.
  - tauto.
  - intros.
    destruct a as (s1,ty).
    simpl in *.
    destruct (string_dec s s1).
    + subst.
      unfold lenv_update.
      unfold STree.set.
      rewrite PTree.set2.
      reflexivity.
    + destruct H; try congruence.
      unfold lenv_update.
      rewrite STree.set_swap by congruence.
      unfold lenv_update in IHrt.
      rewrite IHrt by auto.
      reflexivity.
Qed.


Lemma lenv_of_record_twice : forall
    rt2 r2 rt1 r1  le
    (DUB     : forall x, In x (map fst rt2) -> In x (map fst rt1))
  ,
    lenv_of_record tabs rt1 r1 (lenv_of_record tabs rt2 r2 le) =
      lenv_of_record tabs rt1 r1 le.
Proof.
  induction rt2 ; simpl; auto.
  destruct a.
  intros.
  simpl in *.
  rewrite IHrt2; auto.
  specialize (DUB s (or_introl eq_refl)).
  rewrite lenv_of_record_update by auto.
  reflexivity.
Qed.


Lemma alternate_while : forall te ge rt  fuel rinit leinit cond body,
    option_rel (fun r le => lenv_of_record tabs rt r leinit = le )
      (While.while
         (fun r : eval_recordtyp (eval_typ ) rt =>
            eval_atom  te ge (lenv_of_record tabs rt r leinit)
              TBool cond)
         (fun r : eval_recordtyp (eval_typ ) rt =>
            eval_expr_rec  te ge
              (lenv_of_record tabs rt r leinit)
              (TRecord None rt) body)
         fuel rinit)
      (While.while
         (fun le  =>
            eval_atom  te ge le TBool cond)
         (fun le => let* r :=
                      eval_expr_rec  te ge le (TRecord None rt) body in
                    Some (lenv_of_record tabs rt r le))%option_monad
         fuel (lenv_of_record tabs rt rinit leinit)).
Proof.
    induction fuel.
    - simpl. intros.
      apply option_rel_bind_rel with (RA:=eq).
      {
        apply option_rel_refl. auto.
      }
      intros; subst.
      destruct y.
      destruct (eval_expr_rec  te ge (lenv_of_record tabs rt rinit leinit) (TRecord None rt) body) eqn:EVAL;
        simpl; constructor.
      constructor. reflexivity.
    - intros.
      simpl.
      apply option_rel_bind_rel with (RA:=eq).
      { apply option_rel_refl;auto. }
      intros; subst.
      destruct y.
      destruct (eval_expr_rec  te ge (lenv_of_record tabs rt rinit leinit) (TRecord None rt) body) eqn:EVAL.
      simpl.
      rewrite  lenv_of_record_twice; auto.
      simpl. constructor.
      constructor.
      reflexivity.
  Qed.







  Lemma ecast_typ_None : forall (t1 t2:typ),
      ecast_typ (t2:=t2) tabs None t1 = None.
  Proof.
    unfold ecast_typ. intros.
    destruct (typ_eq_dec t2 t1); auto.
    destruct e; reflexivity.
  Qed.

  Lemma option_rel_ecast_typ : forall t1 (v1 v2:option (eval_typ t1)) ty,
      option_rel eq v1 v2 ->
      option_rel eq (ecast_typ tabs v1 ty) (ecast_typ tabs v2 ty).
  Proof.
    intros.
    inv H. rewrite ecast_typ_None. constructor.
    unfold ecast_typ.
    destruct (typ_eq_dec t1 ty); subst;
      constructor; auto.
  Qed.



  Lemma eval_expr_rec_eq : forall (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr),
      eval_expr_rec te ge le ty e =  eval_expr_rec2 te ge le ty e.
  Proof.
    destruct e; simpl; auto.
    Ltac elim_bind :=
      match goal with
      | |- bind ?X ?F = _ =>
          destruct X ; simpl
      end; try rewrite ecast_typ_None ; auto.
    - repeat elim_bind.
    - repeat elim_bind.
    - repeat elim_bind.
      destruct t0; try rewrite ecast_typ_None; auto.
      repeat elim_bind; auto.
  Qed.

  Definition eval_expr (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr) : option (eval_typ ty) :=
    (eval_expr_rec te ge le ty e).

  Definition eval_fun (te: tenv) (ge:genv) (params : smaplist typ) (tret:typ) (e:expr): Types.eval_typ tabs (TFun (map (fun x : String.string * typ => snd x) params) tret) := eval_fun tabs eval_expr te ge params tret e.


  Definition eval_def_fun := eval_def_fun tabs eval_expr.


  Fixpoint eval_def_rec (te: tenv) (ge: genv) (defs: list globdef) (x: ident) : option value :=
    match defs with
    | nil => fail
    | d :: defs' =>
        match d with
        | DefConst y l ty =>
            let* ge' := eval_def_const tabs te ge y l ty in
            if Ident.eq_dec x y then genv_get tabs ge' x
            else eval_def_rec te ge' defs' x
        | DefFun y f =>
            let* ge':= eval_def_fun  te ge y f in
            if Ident.eq_dec x y then genv_get tabs ge' x
            else eval_def_rec te ge' defs' x
        | DeclConst y _
        | DeclFun y _ _ =>
            if Ident.eq_dec x y then genv_get tabs ge x
            else eval_def_rec te ge defs' x
        end
    end.



  Definition eval_value_err_typ (rv: option value) : Type :=
    match rv with
    | Some (Val _ tv _) => eval_typ tv
    | None => unit
    end.

  Definition eval_def (impl: genv) (prog: program) (x: ident) : option value :=
    let* te := tenv_of_type_defs (prog_types prog) in
    eval_def_rec te impl (prog_defs prog) x.

  (** Evaluation of a whole program *)

  Definition eval_prog (impl: genv) (prog: program) : option (tenv * genv) :=
    Denot.eval_prog tabs  eval_expr impl prog.

  Definition eval_prog_rec (te:tenv) (impl: genv) (ge:genv) (prog: list globdef) : option genv :=
    Denot.eval_prog_rec tabs  eval_expr te impl ge prog.


  (** Redefinition of eval_def by computing the whole global environment first *)

  Definition eval_def2 (impl: genv) (prog: program) (x: ident) : option value :=
    let* (_, ge) := eval_prog impl prog in
    genv_get tabs ge x.


  Lemma less_def_ecast_typ : forall t1 ty (v1 v2 : option (eval_typ t1)),
      less_def v1 v2 ->
      less_def (ecast_typ tabs v1 ty) (ecast_typ tabs v2 ty).
  Proof.
    intros.
    unfold ecast_typ.
    destruct (typ_eq_dec t1 ty).
    subst. inv H.
    constructor.
    constructor.
    constructor.
  Qed.

  Lemma less_def_eval_match : forall tv (e:eval_typ tv) tr (l1 l2:list (pattern * option (eval_typ tr))),
      Forall2 (fun x  y=> fst x = fst y /\ less_def (snd x) (snd y)) l1 l2 ->
      less_def (eval_match tabs tv e  l1)
        (eval_match tabs tv e l2).
  Proof.
    intros.
    destruct tv; try constructor.
    unfold eval_match.
    induction H.
    - constructor.
    - simpl. destruct x,y.
      simpl in H.
      destruct H ; subst.
      destruct p0.
      eapply less_def_bind_eq.
      intros.
      destruct (enum_eq x e); auto.
      auto.
  Qed.

  Lemma less_def_eval_act_record : forall te ge1 ge2 le1 le2 l l0,
      match_env tabs ge1 le1 ge2 le2 ->
      less_def (eval_act_record tabs eval_atom te ge1 l l0 le1)
        (eval_act_record tabs eval_atom te ge2 l l0 le2).
  Proof.
    induction l; simpl.
    - destruct l0; try constructor.
    - destruct a as (x1,e1).
      destruct l0. constructor.
      destruct p.
      destruct (string_dec x1 s); try constructor.
      intros.
      apply less_def_bind_less_def.
      apply less_def_eval_atom;auto.
      intros.
      apply less_def_bind_less_def.
      apply IHl; auto.
      intros. constructor.
  Qed.

  Lemma less_def_with_bind_match_env : forall
      {B: Type} ge1 ge2 le1 le2
      (F G: lenv -> option B),
      less_def_with (fun le1 le2 => match_env tabs ge1 le1 ge2 le2) le1 le2 ->
      (forall le1 le2, match_env tabs ge1 le1 ge2 le2 ->
                      less_def (F le1) (G le2)) ->
      less_def (bind le1 F) (bind le2 G).
  Proof.
    intros.
    inv H.
    - constructor.
    - simpl. auto.
  Qed.

  Lemma less_def_record_of_lenv : forall ge1 le1 ge2 le2 r,
      match_env tabs ge1 le1 ge2 le2 ->
      less_def (record_of_lenv tabs ge1 r le1) (record_of_lenv tabs ge2 r le2).
  Proof.
    induction r ; simpl.
    -  constructor.
    - intros.
      apply less_def_bind_less_def.
      apply H.
      intros.
      apply less_def_bind_eq.
      intros.
      apply less_def_bind_less_def.
      auto.
      constructor.
  Qed.

  Lemma match_env_lenv_of_record : forall ge1 ge2 lt r le1 le2,
      match_env tabs ge1 le1 ge2 le2 ->
      match_env tabs ge1 (lenv_of_record tabs lt r le1) ge2 (lenv_of_record tabs lt r le2).
  Proof.
    unfold lenv_of_record.
    set (F1 := (fun (x : string) (bt : typ) (e : eval_typ bt) (acc : lenv) => lenv_update tabs acc x (Val tabs bt e))).
    induction lt ; simpl; auto.
    intros.
    apply IHlt.
    unfold F1.
    apply match_env_update. auto.
  Qed.

  Fixpoint  less_def_eval_expr  (ge1 ge2:genv) (te:tenv) (e:expr):
    forall le1 le2 ty
           (MATCH : match_env tabs ge1 le1 ge2 le2),
           less_def (eval_expr te ge1 le1 ty e) (eval_expr te ge2 le2 ty e).
  Proof.
    destruct e; simpl;auto.
    - intros. apply less_def_bind_eq.
      intros.
      apply less_def_ecast_typ; auto.
      apply less_def_eval_atom; auto.
    - intros.
      repeat (apply less_def_bind_eq; intros).
      apply less_def_bind_less_def.
      apply less_def_eval_atom; auto.
      intros.
      apply less_def_bind_less_def.
      apply less_def_eval_atom; auto.
      intros.
      apply less_def_bind_less_def.
      apply less_def_eval_atom; auto.
      intros.
      constructor.
    - intros.
      repeat (apply less_def_bind_eq; intros).
      apply less_def_bind_less_def.
      apply less_def_eval_atom; auto.
      intros.
      apply less_def_bind_less_def.
      apply less_def_eval_atom; auto.
      intros.
      constructor.
    - intros.
      repeat (apply less_def_bind_eq; intros).
      destruct x0; try constructor.
      apply less_def_bind_less_def.
      apply less_def_eval_atom with (ty:= (TFun l0 x0)); auto.
      intros.
      assert (less_def (let* vargs := DList.map2 eval_typ (eval_atom te ge1 le1) l l0 in  (eval_app_option tabs l0 x0 x1 vargs x))
                (let* vargs := DList.map2 eval_typ (eval_atom te ge2 le2) l l0 in (eval_app_option tabs l0 x0 x1 vargs x))).
      { apply less_def_eval_app_option_args; eauto.
        apply less_def_eval_atom.
      }
      destruct (DList.map2 eval_typ (eval_atom te ge1 le1) l l0); try constructor.
      simpl in H; simpl.
      destruct (DList.map2 eval_typ (eval_atom te ge2 le2) l l0).
      simpl in *.
      eapply less_def_ecast_typ; auto.
      simpl in H. simpl.
      inv H. rewrite ecast_typ_None.
      constructor.
      rewrite H2. rewrite ecast_typ_None.
      constructor.
    - intros.
      apply less_def_bind_less_def.
      apply less_def_eval_atom with (ty:= TBool); auto.
      intros.
      destruct x; auto.
    - intros.
      repeat (apply less_def_bind_eq; intros).
      apply less_def_bind_less_def.
      apply less_def_eval_atom; auto.
      intros.
      apply less_def_eval_match;auto.
      induction l.
      + simpl. constructor.
      + simpl. constructor.
        simpl. split; auto.
        auto.
    - intros.
      repeat (apply less_def_bind_eq; intros).
      apply less_def_bind_less_def.
      auto.
      intros.
      apply less_def_eval_expr; auto.
      unfold env_noshadow in *.
      intros.
      apply match_env_update; auto.
    - destruct ty; try constructor.
      destruct o; try constructor.
      intro.
      apply less_def_bind_eq.
      intro. destruct (typ_eqb (TRecord None l0) x); try constructor.
      apply less_def_eval_act_record; auto.
    - intros.
      apply less_def_with_bind_match_env with (ge1:=ge1) (ge2:=ge2).
      {
        assert (GEN : forall le1' le2',
                   match_env tabs ge1 le1' ge2 le2' ->
                   less_def_with (fun le1 le2 => match_env tabs ge1 le1 ge2 le2)
                     (update_para_lenv (eval_expr te ge1) te le1' l le1)
                     (update_para_lenv (eval_expr te ge2) te le2' l le2)).
        { revert le1 le2 MATCH.
        induction l; simpl.
        - constructor.
          auto.
        - intros.
          apply less_def_with_bind_eq.
          intros.
          generalize (less_def_eval_expr ge1 ge2 te (snd a1) le1' le2' x H).
          intro IH ; inv IH.
          simpl. constructor.
          destruct (eval_expr te ge1 le1' x (snd a1)); try constructor.
          simpl.
          apply IHl.
          apply match_env_update; auto.
          auto.
        }
        apply GEN;auto.
      }
      intros.
      apply less_def_bind_eq.
      intros.
      apply less_def_bind_less_def.
      apply less_def_eval_atom;auto.
      intros.  apply less_def_bind_eq.
      intros.  apply less_def_bind_eq.
      intros.
      apply less_def_bind_less_def.
      apply less_def_record_of_lenv; auto.
      intros.
      apply less_def_bind_less_def.
      apply less_def_while.
      +  intros.
      apply less_def_eval_atom with (ty:=TBool);auto.
      apply match_env_lenv_of_record; auto.
      + intros.
      apply less_def_eval_expr with (ty := TRecord None x2).
      apply match_env_lenv_of_record; auto.
      +  intro. apply less_def_eval_expr.
         apply match_env_lenv_of_record;auto.
  Qed.

  Lemma get_env_var_defined :
    forall ge1 ge2 le1 le2 v
           (MATCH : match_env tabs ge1 le1 ge2 le2)
           (WF : var_defined (STree.keys ge1) (STree.keys le1) v = true),
      option_rel eq (get_env tabs ge1 le1 v) (get_env tabs ge2 le2 v).
  Proof.
    intros.
    specialize (MATCH v).
    inv MATCH.
    -  unfold var_defined, get_env in *.
       rewrite orb_true_iff in WF.
       destruct WF.
       * apply STree.keys_mem_true_get in H.
         destruct H as (v1 & EQ).
         rewrite EQ in *.
         discriminate.
       * apply STree.keys_mem_true_get in H.
         destruct H as (v1 & EQ).
         rewrite EQ in *.
         destruct (STree.get v le1); try discriminate.
    - rewrite H1.
      apply option_rel_refl. repeat intro;reflexivity.
  Qed.

  
  Lemma eval_var_same : forall ge1 le1 ge2 le2 v ty
      (MATCH : match_env tabs ge1 le1 ge2 le2)
        (WF : var_defined (STree.keys ge1) (STree.keys le1) v = true),
    option_rel eq (eval_var tabs ge1 le1 v ty)
      (eval_var tabs ge2 le2 v ty).
  Proof.
    unfold eval_var; intros.
    apply option_rel_bind_rel with (RA:=eq).
    apply get_env_var_defined;auto.
    intros. subst.
    apply option_rel_refl. auto.
  Qed.

  Lemma match_on_update : forall P x v ge1 le1 ge2 le2,
      match_on tabs (diff P (singleton  x)) ge1 le1 ge2 le2 ->
      match_on tabs P ge1 (lenv_update tabs le1 x v) ge2 (lenv_update tabs le2 x v).
  Proof.
    unfold match_on; intros.
    unfold get_env,lenv_update.
    rewrite! STree.gsspec.
    destruct (STree.elt_eq x0 x). constructor; auto.
    apply H.
    unfold diff. unfold singleton, BSet.singleton.
    destruct (string_dec x0 x); try congruence.
    simpl. rewrite H0; reflexivity.
  Qed.
  
  Lemma match_on_le : forall P Q ge1 le1 ge2 le2,
      match_on tabs P ge1 le1 ge2 le2 ->
      (BSet.subset Q P) ->
      match_on tabs Q ge1 le1 ge2 le2.
  Proof.
    unfold match_on,subset ; intros.
    apply H;auto.
  Qed.

  Lemma option_rel_map2_eval_atoms :
    forall te ge1 le1 ge2 le2 l l0,
      match_on tabs (union_list AtomOrdered.has_var l) ge1 le1 ge2 le2 ->
      option_rel eq (DList.map2 (eval_typ) (eval_atom  te ge1 le1) l l0) (DList.map2 (eval_typ ) (eval_atom  te ge2 le2) l l0).
  Proof.
    induction l ; simpl.
    - destruct l0; simpl. constructor.
      reflexivity.
      constructor.
    - destruct l0 ; simpl.
      constructor.
      intros.
      rewrite match_on_union in H.
      eapply option_rel_bind_rel.
      apply IHl.
      tauto.
      intros ; subst.
      constructor.
      f_equal.
      apply option_rel_eq_eq.
      apply eval_atom_match_on;auto.
      tauto.
  Qed.

  Lemma option_rel_eval_act_record :
    forall te ge1 le1 ge2 le2 l l0,
      match_on tabs (union_list (fun x => AtomOrdered.has_var (snd x)) l) ge1 le1 ge2 le2 ->
      option_rel eq (eval_act_record tabs (eval_atom ) te ge1 l l0 le1)
        (eval_act_record tabs (eval_atom ) te ge2 l l0 le2).
  Proof.
    induction l ; simpl.
    - destruct l0; simpl. constructor.
      reflexivity.
      constructor.
    - destruct l0 ; simpl.
      destruct a; constructor.
      destruct a. destruct p.
      destruct (string_dec s s0).
      intros.
      rewrite match_on_union in H.
      eapply option_rel_bind_rel.
      apply eval_atom_match_on;auto. tauto.
      intros; subst.
      eapply option_rel_bind_rel.
      apply IHl.
      tauto.
      intros ; subst.
      constructor.
      f_equal.
      simpl. constructor.
  Qed.

  
  Lemma record_of_lenv_match_on :
    forall ge1 le1 ge2 le2 rt,
      match_on tabs (bset_of_bindings rt) ge1 le1 ge2 le2 ->
      option_rel eq (record_of_lenv tabs ge1 rt le1)
        (record_of_lenv tabs ge2 rt le2).
  Proof.
    induction rt ; simpl.
    -  constructor. reflexivity.
    - intros.
      eapply option_rel_bind_rel with (RA:=eq).
      rewrite match_on_union in H.
      destruct H.
      apply H.
      unfold singleton ; auto with bset.
      intros.
      subst.
      apply option_rel_bind_equal;intros.
      eapply option_rel_bind_rel with (RA:=eq).
      apply IHrt.
      rewrite match_on_union in H.
      tauto.
      intros.
      constructor.
      congruence.
  Qed.

  Lemma mmap_bset_of_bindings : forall {A B:Type} (F: A -> option B) l1 l2,
      MapList.mmap _ F l1 = Some l2 ->
      bset_of_bindings l1  = bset_of_bindings l2.
  Proof.
    induction l1; try discriminate; auto.
    -  intros. simpl in H. inv H. reflexivity.
    - simpl. intros.
      monadInv H.
      monadInv EQ. simpl.
      f_equal.
      apply IHl1; auto.
  Qed.

  Lemma match_on_lenv_of_record : forall P lt ge1 le1 ge2 le2  r,
      match_on tabs (BSet.diff P (bset_of_bindings lt)) ge1 le1 ge2  le2 ->
      match_on tabs P ge1
        (lenv_of_record tabs lt r le1) ge2
        (lenv_of_record tabs lt r le2).
  Proof.
    induction lt ; simpl.
    - intros. eapply match_on_le;eauto.
      unfold subset,diff,bot.
      intros. rewrite andb_true_iff. tauto.
    - intros.
      apply IHlt.
      eapply match_on_update.
      eapply match_on_le;eauto.
      unfold subset,diff,union.
      intros.
      rewrite! andb_true_iff in H0.
      rewrite! andb_true_iff.
      rewrite negb_true_iff in *.
      rewrite orb_false_iff.
      rewrite negb_true_iff in H0. intuition congruence.
  Qed.

  Lemma match_on_bot : forall ge1 le1 ge2 le2, match_on tabs bot ge1 le1 ge2 le2.
  Proof.
    repeat intro.
    discriminate.
  Qed.


  Lemma wf_atom_match_on : forall ge1 le1 ge2 le2 a,
      wf_atom (STree.keys ge1) (STree.keys le1) a = true ->
      match_env tabs ge1 le1 ge2 le2 ->
      match_on tabs (AtomOrdered.has_var a) ge1 le1 ge2 le2.
  Proof.
    induction a using atom_depth_ind.
    - simpl. intros. apply match_on_bot.
    - simpl. intros. apply match_on_bot.
    - simpl. intros. apply match_on_bot.
    - simpl. intros. apply match_on_bot.
    - simpl. intros. apply match_on_bot.
    - simpl. intros.
      eapply get_env_var_defined in H; eauto.
      repeat intro.
      unfold BSet.singleton in H1.
      destruct (string_dec x i); try discriminate.
      congruence.
    - simpl ; intros.
      auto.
    - simpl ; intros; auto.
    - simpl ; intros; auto.
      rewrite match_on_union.
      rewrite andb_true_iff in H.
      destruct H.
      split;auto.
    - simpl.
      rewrite! match_on_union.
      rewrite! andb_true_iff.
      intuition.
    - simpl.
      auto.
    - simpl.
      rewrite andb_true_iff.
      rewrite match_on_union.
      split; intros.
      destruct H0.
      +  eapply get_env_var_defined in H0; eauto.
         repeat intro.
         unfold BSet.singleton in H3.
         destruct (string_dec x i); try congruence.
      + destruct H0.
        clear H0.
        induction args; simpl;auto.
        apply match_on_bot.
        intros.
        rewrite match_on_union.
        simpl in H2. rewrite andb_true_iff in H2.
        destruct H2.
        split ; auto.
        * apply H; auto.
          simpl;tauto.
        * apply IHargs;auto.
          intros;apply H;auto.
          simpl. tauto.
  Qed.

  Fixpoint  eval_expr_match_on  (ge1 ge2:genv) (te:tenv) (e:expr):
    forall le1 le2 ty
           (MATCH : match_on  tabs (has_var e) ge1 le1 ge2 le2),
      option_rel eq (eval_expr te ge1 le1 ty e) (eval_expr te ge2 le2 ty e).
  Proof.
    destruct e; simpl;auto.
    - intros. apply option_rel_bind_equal.
      intros.
      eapply eval_atom_match_on with (te:=te) (ty:=a0) in MATCH.
      apply option_rel_eq_eq in MATCH.
      rewrite MATCH.
      apply option_rel_refl; auto.
    - intros.
      rewrite! match_on_union in MATCH.
      repeat (apply option_rel_bind_equal; intros).
      eapply option_rel_bind_rel.
      apply eval_atom_match_on. tauto.
      intros.
      eapply option_rel_bind_rel.
      apply eval_atom_match_on. tauto.
      intros.
      eapply option_rel_bind_rel.
      apply eval_atom_match_on. tauto.
      intros.
      subst.
      apply option_rel_refl; auto.
    - intros.
      rewrite! match_on_union in MATCH.
      repeat (apply option_rel_bind_equal; intros).
      eapply option_rel_bind_rel.
      apply eval_atom_match_on. tauto.
      intros.
      eapply option_rel_bind_rel.
      apply eval_atom_match_on. tauto.
      intros.
      subst.
      apply option_rel_refl; auto.
    - intros.
      intros.
      rewrite! match_on_union in MATCH.
      repeat (apply option_rel_bind_equal; intros).
      destruct a1; try constructor.
      eapply option_rel_bind_rel.
      apply eval_atom_match_on with (ty:= TFun l0 a1). tauto.
      intros. subst.
      eapply option_rel_bind_rel with (RA:=eq).
      { destruct MATCH as (_,M).
        clear - M eval_expr_match_on.
        revert l0.
        induction l; destruct l0; simpl; try constructor.
        reflexivity.
        simpl in M.
        rewrite match_on_union in M.
        apply option_rel_bind_rel with (RA:=eq).
        apply IHl.  tauto.
        intros; subst.
        constructor.
        f_equal;auto.
        apply option_rel_eq_eq.
        apply eval_atom_match_on; tauto.
      }
      intros.
      subst.
      apply option_rel_refl;auto.
    - intros.
      rewrite! match_on_union in MATCH.
      eapply option_rel_bind_rel.
      apply eval_atom_match_on with (ty:=TBool). tauto.
      intros. subst.
      destruct y; auto.
      apply eval_expr_match_on. tauto.
      apply eval_expr_match_on. tauto.
    - intros.
      repeat (apply option_rel_bind_equal; intros).
      rewrite! match_on_union in MATCH.
      eapply option_rel_bind_rel.
      apply eval_atom_match_on . tauto.
      intros. subst.
      assert
        (EQ:MapList.map (eval_expr te ge1 le1 ty) l =
            MapList.map (eval_expr te ge2 le2 ty) l).
      {
        destruct MATCH as (_ & MATCH).
        induction l; simpl; auto.
        simpl in MATCH.
        rewrite match_on_union in MATCH.
        destruct MATCH as (M1 & M2).
        f_equal.
        f_equal.
        apply option_rel_eq_eq; auto.
        apply IHl ; auto.
      }
      rewrite EQ.
      apply option_rel_refl;auto.
    - intros.
      repeat (apply option_rel_bind_equal; intros).
      rewrite match_on_union in MATCH.
      eapply option_rel_bind_rel.
      apply eval_expr_match_on. tauto.
      intros ; subst.
      eapply eval_expr_match_on.
      destruct MATCH as (M1 & M2).
      apply match_on_update;auto.
    - destruct ty; try constructor.
      destruct o. constructor.
      intro.
      apply option_rel_bind_equal.
      intros.
      destruct (typ_eqb (TRecord None l0) a); try constructor.
      apply option_rel_eval_act_record ;auto.
    - intros.
      eapply option_rel_bind_rel.
      {
        set (F1:= (fun x_a : ident * expr => has_var (snd x_a))).
        assert (GEN : forall P Q le1' le2',
                   match_on tabs Q ge1 le1' ge2 le2' ->
                   subset (union_list F1 l) Q ->
                   match_on tabs P ge1 le1 ge2 le2  ->
                   option_rel (fun le1 le2 => match_on tabs (BSet.union (bset_of_bindings l) P) ge1 le1 ge2 le2)
                     (update_para_lenv (eval_expr te ge1) te le1' l le1)
                     (update_para_lenv (eval_expr te ge2) te le2' l le2)).
        { clear MATCH.
          revert le1 le2.
          induction l; simpl.
          - constructor. auto.
          - intros.
            apply option_rel_bind_equal; intros.
            eapply option_rel_bind_rel.
            apply eval_expr_match_on.
            eapply match_on_le;eauto.
            { eapply subset_trans;eauto.
              unfold subset,union.
              intros. rewrite orb_true_iff. unfold F1. tauto.
            }
            intros.
            subst.
            set (F2:= (fun x_a : ident * expr => singleton  (fst x_a))).
            apply option_rel_weaken
              with (R1 :=
                      (fun le0 le3 : lenv =>
                         match_on tabs (union (bset_of_bindings l) (union (F2 a1) P))
                           ge1 le0 ge2 le3)).
            eapply IHl; eauto.
            eapply subset_trans;eauto.
            unfold subset,diff.
            intros.
            unfold union.
            rewrite orb_true_iff.
            tauto.
            apply match_on_update.
            eapply match_on_le; eauto.
            unfold F2.
            unfold subset,diff,union.
            intros.
            rewrite andb_true_iff in H3.
            rewrite! orb_true_iff in H3.
            rewrite negb_true_iff in H3.
            intuition congruence.
            intros.
            eapply match_on_le; eauto.
            unfold subset,union; intros.
            rewrite! orb_true_iff in H8.
            rewrite! orb_true_iff.
            tauto.
        }
        eapply GEN.
        apply MATCH.
        { unfold subset,diff,union.
          intros.
          rewrite! orb_true_iff.
          tauto.
        }
        apply MATCH.
      }
      intros. simpl in H.
      apply match_on_le
          with (Q :=
(union
         (bset_of_bindings l)
         (union
            (union_list
               (fun x_a : ident * expr => has_var (snd x_a)) l)
               (union
                  (union_list
                     (fun x : ident * expr => has_var (snd x)) l)
                  (union (AtomOrdered.has_var a)
                     (union (AtomOrdered.has_var a0)
                        (union (has_var e1)
                           (union (has_var e2) bot)))))
               ))) in H.
      apply option_rel_bind_equal; intros.
      eapply option_rel_bind_rel.
      apply eval_atom_match_on.
      eapply match_on_le;eauto.
      { unfold subset, union.
        intros.
        rewrite! orb_true_iff.
        tauto.
      }
      intros; subst.
      apply option_rel_bind_equal;intros; subst.
      apply option_rel_bind_equal;intros; subst.
      eapply option_rel_bind_rel with (RA:=eq).
      apply record_of_lenv_match_on.
      eapply match_on_le; eauto.
      { unfold subset,union.
        intros.
        rewrite! orb_true_iff.
        left. rewrite <- H7.
        apply mmap_bset_of_bindings in H6; congruence.
      }
      intros ; subst.
      apply option_rel_bind_rel with (RA:=eq).
      clear MATCH.
      apply While.while_rel; auto.
      + intros. subst.
        apply option_rel_eq_eq.
        apply eval_atom_match_on with (ty:=TBool).
        apply match_on_lenv_of_record.
        eapply match_on_le;eauto.
        {
          unfold subset,diff,union.
          intros.
          rewrite andb_true_iff in *.
          rewrite negb_true_iff in H7.
          rewrite! orb_true_iff.
          tauto.
        }
      + intros ; subst.
        eapply eval_expr_match_on with (ty:= TRecord None a3).
        apply match_on_lenv_of_record.
        eapply match_on_le;eauto.
        {
          unfold subset,diff,union.
          intros.
          rewrite andb_true_iff in *.
          rewrite negb_true_iff in H7.
          rewrite! orb_true_iff.
          tauto.
        }
      + intros; subst.
        apply eval_expr_match_on.
        apply match_on_lenv_of_record.
        eapply match_on_le;eauto.
        {
          unfold subset,diff,union.
          intros.
          rewrite andb_true_iff in *.
          rewrite negb_true_iff in H7.
          rewrite! orb_true_iff.
          tauto.
        }
      +
        generalize (union (union_list (fun x0 : ident * expr => has_var (snd x0)) l)
                      (union (AtomOrdered.has_var a) (union (AtomOrdered.has_var a0) (union (has_var e1) (union (has_var e2) bot)))))
                     as S1.
        intros.
        generalize (bset_of_bindings l) as L.
        generalize (union_list (fun x_a : ident * expr => has_var (snd x_a)) l) as S2.
        unfold subset,union,diff; intros.
        rewrite! orb_true_iff in *.
        rewrite andb_true_iff in *.
        rewrite negb_true_iff.
        destruct (L x0). tauto.
        intuition congruence.
  Qed.





  Lemma eval_atom_map2 :
    forall te ge1 ge2 le1 le2
           (MATCH : match_env tabs ge1 le1 ge2 le2)
           l args
      (REC : forall x : atom,
          In x args ->
          forall (le3 le4 : lenv) (ty0 : typ),
            match_env tabs ge1 le3 ge2 le4 ->
            wf_atom (STree.keys ge1) (STree.keys le3) x = true ->
            option_rel eq (eval_atom te ge1 le3 ty0 x)
              (eval_atom te ge2 le4 ty0 x))
      (WF: forallb (wf_atom (STree.keys ge1) (STree.keys le1)) args = true),
      option_rel eq
        (DList.map2 eval_typ (eval_atom te ge1 le1) args l)
        (DList.map2 eval_typ (eval_atom te ge2 le2) args l).
  Proof.
    induction l ; simpl.
    - destruct args ; simpl. constructor. reflexivity.
      constructor.
    - intros.
      simpl.
      destruct args; simpl; auto.
      constructor.
      apply option_rel_bind_rel with (RA:=eq).
      eapply IHl;auto.
      intros. apply REC. simpl. tauto.
      auto. auto.
      simpl in WF. rewrite andb_true_iff in WF. tauto.
      intros. subst.
      constructor.
      assert (option_rel eq (eval_atom te ge1 le1 a a0) (eval_atom te ge2 le2 a a0)).
      {
        apply REC; auto.
        simpl. tauto.
        simpl in WF. rewrite andb_true_iff in WF. tauto.
      }
      inv H.
      reflexivity.
      reflexivity.
  Qed.




  Lemma  eval_atom_same  (ge1 ge2:genv) (te:tenv) (a:atom):
    forall le1 le2 ty
           (MATCH : match_env tabs ge1 le1 ge2 le2)
           (WF    : wf_atom (STree.keys ge1) (STree.keys le1) a = true)
    ,
      option_rel eq (eval_atom te ge1 le1 ty a) (eval_atom te ge2 le2 ty a).
  Proof.
    induction a using atom_depth_ind;
      simpl; intros ; try (apply option_rel_refl ; auto).
    - apply eval_var_same;auto.
    - repeat (apply option_rel_bind_equal; intros).
      apply option_rel_bind_rel with (RA := eq).
      apply IHa; auto.
      intros.
      subst.
      apply option_rel_refl. auto.
    - repeat (apply option_rel_bind_equal; intros).
      apply option_rel_bind_rel with (RA := eq).
      apply IHa; auto.
      intros.
      subst.
      apply option_rel_refl. auto.
    - repeat (apply option_rel_bind_equal; intros).
      rewrite! andb_true_iff in WF.
      apply option_rel_bind_rel with (RA := eq).
      apply IHa1; try tauto.
      intros.
      subst.
      apply option_rel_bind_rel with (RA := eq).
      apply IHa2; try tauto.
      intros.
      subst.
      apply option_rel_refl. auto.
    - repeat (apply option_rel_bind_equal; intros).
      rewrite! andb_true_iff in WF.
      apply option_rel_bind_rel with (RA := eq).
      apply IHa1; try tauto.
      intros.
      subst.
      apply option_rel_bind_rel with (RA := eq).
      apply IHa2; try tauto.
      intros.
      subst.
      apply option_rel_refl. auto.
    - repeat (apply option_rel_bind_equal; intros).
      apply option_rel_bind_rel with (RA := eq).
      apply IHa; try tauto.
      intros.
      subst.
      apply option_rel_refl. auto.
    - repeat (apply option_rel_bind_equal; intros).
      destruct a; try constructor.
      apply option_rel_bind_rel with (RA := eq).
      apply eval_var_same with (ty:= TFun l a); auto.
      rewrite andb_true_iff in WF; tauto.
      intros.
      subst.
      apply option_rel_bind_rel with (RA:=eq).
      rewrite andb_true_iff in WF.
      apply eval_atom_map2; auto.  tauto.
      intros.
      subst.
      apply option_rel_refl. auto.
  Qed.


  Lemma eval_act_record_same :
    forall te ge1 ge2 le1 le2 l l0
           (MATCH : match_env tabs ge1 le1 ge2 le2)
           (WF : forallb
                   (fun x : ident * atom =>
                      wf_atom (STree.keys ge1) (STree.keys le1) (snd x))
                   l =
                   true),
      option_rel eq (eval_act_record tabs eval_atom te ge1 l l0 le1)
        (eval_act_record tabs eval_atom te ge2 l l0 le2).
  Proof.
    induction l; simpl.
    - destruct l0. constructor. reflexivity.
      constructor.
    - destruct a as (fd,a).
      destruct l0.
      constructor.
      intros. destruct p as (fd1,a1).
      destruct (string_dec fd fd1);try constructor.
      apply option_rel_bind_rel with (RA:=eq).
      apply eval_atom_same;auto.
      rewrite andb_true_iff in WF;tauto.
      intros;subst.
      apply option_rel_bind_rel with (RA:=eq).
      apply IHl; auto.
      rewrite andb_true_iff in WF;tauto.
      intros ; subst.
      constructor;auto.
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

  Lemma update_para_lenv_keys_eq : forall te (ge:genv) l (acc le:lenv) lei,
      update_para_lenv  (eval_expr  te ge) te acc l le
         = Some lei ->
      STree.keys lei = add_bindings (STree.keys le) l.
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

Fixpoint  eval_expr_same  (ge1 ge2:genv) (te:tenv) (e:expr):
    forall le1 le2 ty
           (MATCH : match_env tabs ge1 le1 ge2 le2)
           (WF    : wf_expr (STree.keys ge1) (STree.keys le1) e = true)
    ,
      option_rel eq (eval_expr te ge1 le1 ty e) (eval_expr te ge2 le2 ty e).
  Proof.
    destruct e; simpl;auto.
    - intros.
      apply option_rel_bind_equal. intros.
      specialize (eval_atom_same ge1 ge2 te a le1 le2 a0 MATCH WF).
      intro. inv H0.
      rewrite <- H2. rewrite <- H3.
      apply option_rel_refl;auto.
      rewrite <- H1. rewrite <- H2.
      apply option_rel_refl;auto.
    - intros.
      repeat (apply option_rel_bind_equal; intros).
      rewrite! andb_true_iff in WF.
      apply option_rel_bind_rel with (RA:=eq).
      eapply eval_atom_same;eauto. tauto.
      intros; subst.
      apply option_rel_bind_rel with (RA:=eq).
      eapply eval_atom_same;eauto. tauto.
      intros; subst.
      apply option_rel_bind_rel with (RA:=eq).
      eapply eval_atom_same;eauto. tauto.
      intros; subst.
      apply option_rel_refl. auto.
    - intros.
      repeat (apply option_rel_bind_equal; intros).
      rewrite! andb_true_iff in WF.
      apply option_rel_bind_rel with (RA:=eq).
      eapply eval_atom_same;eauto. tauto.
      intros; subst.
      apply option_rel_bind_rel with (RA:=eq).
      eapply eval_atom_same;eauto. tauto.
      intros; subst.
      apply option_rel_refl. auto.
    - intros.
      repeat (apply option_rel_bind_equal; intros).
      rewrite! andb_true_iff in WF.
      destruct a1; try constructor.
      apply option_rel_bind_rel with (RA:=eq).
      eapply eval_atom_same with (ty:= TFun l0 a1);eauto. tauto.
      intros; subst.
      apply option_rel_bind_rel with (RA:=eq).
      apply eval_atom_map2; auto.
      intros.
      destruct WF.
      apply eval_atom_same;auto.
      tauto.
      intros; subst.
      apply option_rel_refl. auto.
    - intros.
      rewrite! andb_true_iff in WF.
      apply option_rel_bind_rel with (RA:=eq).
      apply eval_atom_same with (ty:= TBool);auto.
      tauto.
      intros; subst.
      destruct y.
      apply eval_expr_same; auto.
      tauto.
      apply eval_expr_same; auto.
      tauto.
    - intros.
      repeat (apply option_rel_bind_equal; intros).
      rewrite! andb_true_iff in WF.
      apply option_rel_bind_rel with (RA:=eq).
      eapply eval_atom_same; auto. tauto.
      intros; subst.
      assert (MapList.map (eval_expr te ge1 le1 ty) l
        = MapList.map (eval_expr te ge2 le2 ty) l).
      {
        destruct WF as (_,WF).
        revert WF.
        clear - eval_expr_same MATCH.
        induction l; simpl;auto.
        - destruct a. simpl.
          intro.
          f_equal.
          f_equal.
          apply option_rel_eq_eq.
          eapply eval_expr_same;eauto.
          rewrite andb_true_iff in WF. tauto.
          apply IHl.
          rewrite andb_true_iff in WF. tauto.
      }
      rewrite H0. apply option_rel_refl. auto.
    -
      intros.
      repeat (apply option_rel_bind_equal; intros).
      rewrite! andb_true_iff in WF.
      rewrite !negb_true_iff in WF.
      eapply option_rel_bind_rel with (RA:= eq).
      apply eval_expr_same; auto.
      tauto.
      intros; subst.
      apply eval_expr_same; auto.
      apply match_env_update; auto.
      rewrite keys_lenv_update.
      tauto.
    - intros. destruct ty; try constructor.
      destruct o. constructor.
      apply option_rel_bind_equal.
      intros.
      destruct (typ_eqb (TRecord None l0) a); try constructor.
      apply eval_act_record_same;auto.
    - intros.
      rewrite! andb_true_iff in WF.
      apply option_rel_bind_rel with (RA:=fun le1 le2 =>
                                            match_env tabs ge1 le1 ge2 le2 ).
      { destruct WF as (WF & _).
        assert (forall le0 le0',
                   match_env tabs ge1 le0 ge2 le0' ->
                   option_rel (fun le0 le3 : lenv => match_env tabs ge1 le0 ge2 le3)
                     (update_para_lenv (eval_expr te ge1) te le1 l le0)
                     (update_para_lenv (eval_expr te ge2) te le2 l le0')).
        {
        revert le1 le2 WF MATCH.
        induction l; simpl.
        - constructor. auto.
        - intros.
          eapply option_rel_bind_equal; intros.
          apply option_rel_bind_rel with (RA:=eq).
          apply eval_expr_same; auto.
          unfold wf_binding in WF.
          rewrite !andb_true_iff in WF.
          tauto.
          intros; subst.
          apply IHl.
          rewrite wf_init_syntax_iff in WF.
          rewrite !andb_true_iff in WF.
          tauto.
          auto.
          apply match_env_update;auto.
        }
        apply H; auto.
      }
      intros.
      repeat (apply option_rel_bind_equal; intros).
      apply option_rel_bind_rel with (RA:= eq).
      apply eval_atom_same;auto.
      apply update_para_lenv_keys_eq in H0.
      rewrite H0.
      tauto.
      intros. subst.
      repeat (apply option_rel_bind_equal; intros).
      assert (KEYS : forall v, In v (map fst a3) ->
                          SSet.mem v (STree.keys x) = true).
      {
        apply MapList.mmap_fst in H6.
        apply update_para_lenv_keys_eq in H0.
        intros. rewrite H0.
        rewrite <- H6 in H7.
        clear - H7.
        induction l ; simpl.
        - simpl in H7. tauto.
        - simpl in H7.
          rewrite SSet.mem_add.
          destruct a; simpl in *.
          destruct H7 ; subst.
          destruct (string_dec v v); auto.
          destruct (string_dec v i); auto.
      }
      apply option_rel_bind_rel with (RA:= eq).
      { clear - KEYS H.
        induction a3 ; simpl.
        - constructor. reflexivity.
        -
          apply option_rel_bind_rel with (RA:=eq).
          specialize (H (fst a)).
          inv H.
          symmetry in H1.
          unfold get_env in H1.
          unfold get_env at 1.
          destruct (STree.get (fst a) x) eqn:GET.
          discriminate.
          setoid_rewrite GET.
          rewrite STree.keys_get_mem_false_iff in GET.
          rewrite KEYS in GET. congruence.
          simpl. tauto.
          setoid_rewrite H2.
          apply option_rel_refl; auto.
          intros; subst.
          apply option_rel_bind_equal;intros.
          apply option_rel_bind_rel with (RA:=eq).
          apply IHa3;auto.
          intros. apply KEYS; simpl. tauto.
          intros.
          constructor. subst. reflexivity.
      }
      intros.
      apply option_rel_bind_rel with (RA:=eq).
      subst.
      apply while_rel; auto.
      { intros; subst.
        apply option_rel_eq_eq.
        apply eval_atom_same with (ty:=TBool).
        apply match_env_lenv_of_record; auto.
        rewrite keys_lenv_of_record_same.
        apply update_para_lenv_keys_eq in H0.
        rewrite H0. tauto.
        intros. apply KEYS.
        rewrite in_map_iff. exists (x0,v). split; auto.
      }
      { intros ; subst.
        apply eval_expr_same with (ty:= TRecord None a3).
        apply match_env_lenv_of_record; auto.
        rewrite keys_lenv_of_record_same.
        apply update_para_lenv_keys_eq in H0.
        rewrite H0. tauto.
        intros. apply KEYS.
        rewrite in_map_iff. exists (x0,v). split; auto.
      }
      intros ; subst.
      apply eval_expr_same.
      apply match_env_lenv_of_record; auto.
      rewrite keys_lenv_of_record_same.
      apply update_para_lenv_keys_eq in H0.
      rewrite H0. tauto.
      intros. apply KEYS.
      rewrite in_map_iff. exists (x0,v). split; auto.
  Qed.



  Lemma update_eq_Some :
      forall (ge:genv) te
             l le0 le le1
             (WF : wf_init (STree.keys ge) (wf_expr (STree.keys ge)) (STree.keys le0) l = true)
             (MATCH  : match_env tabs ge le0 ge le)
             (UPDATE : update_para_lenv (eval_expr te ge) te le0 l le = Some le1),
        update_seq_lenv (eval_expr te ge) te l le = Some le1.
    Proof.
      intros.
      assert (less_def (update_para_lenv (eval_expr te ge) te le0 l le)
                       (update_seq_lenv (eval_expr te ge) te l le)).
      {
        apply less_def_update with (ge:=ge); auto.
        intros.
        apply less_def_eval_expr; auto.
      }
      inv H.
      congruence.
      congruence.
    Qed.

    Lemma wf_init_all : forall K1 K2 l,
        wf_init K1 (wf_expr K1) K2 l = true ->
        forall id e, In (id,e) l -> wf_expr K1 K2 e = true.
    Proof.
      induction l ; simpl.
      - tauto.
      - intros.
        destruct H0 ; subst.
        unfold wf_binding in H.
        rewrite ! andb_true_iff in H. tauto.
        eapply IHl; eauto.
        rewrite! andb_true_iff in H;tauto.
    Qed.


    Lemma update_eq_None :
      forall (ge:genv) te
             l le0
             (WF : wf_init (STree.keys ge) (wf_expr (STree.keys ge)) (STree.keys le0) l = true)
      ,
        update_para_lenv (eval_expr te ge) te le0 l le0 = update_seq_lenv (eval_expr te ge) te l le0.
    Proof.
      intros.
      apply option_rel_eq_eq.
      destruct (update_para_lenv (eval_expr te ge) te le0 l le0) eqn:UP.
      - eapply update_eq_Some in UP; eauto.
        rewrite UP. constructor. reflexivity.
        apply match_env_refl.
      - eapply update_para_lenv_None in UP; eauto.
        rewrite UP. constructor.
        intros.
        apply less_def_eval_expr; auto.
        intros.
        rewrite <- H1.
        symmetry.
        apply option_rel_eq_eq.
        apply eval_expr_same; auto.
        eapply wf_init_all        ; eauto.
        apply match_env_refl.
    Qed.

    Lemma match_on_update_r : forall P ge1 le1 ge2 le2 x v,
        match_on tabs P ge1 le1 ge2 le2 ->
        P x = false ->
        match_on tabs P ge1 le1 ge2 (lenv_update tabs le2 x v).
    Proof.
      unfold match_on;intros.
      unfold get_env. unfold lenv_update.
      destruct (STree.elt_eq x0 x); subst.
      congruence.
      rewrite STree.gso by auto.
      apply H; auto.
    Qed.

    Lemma match_on_refl : forall P ge le,
        match_on tabs P ge le ge le.
    Proof.
      unfold match_on. intros.
      apply option_rel_refl; auto.
    Qed.


    Lemma update_para_seq_wf : forall  te ge l le1,
        ForallP (fun x_e => is_empty (inter (has_var (snd x_e)) (bset_of_bindings l))) l ->
        option_rel eq
          (update_para_lenv  (eval_expr_rec  te ge) te le1 l le1)
          (update_seq_lenv  (eval_expr_rec  te ge) te l le1).
    Proof.
      intros.
      assert (forall le1' Q,
                 Forall (fun e => is_empty (inter (has_var e) Q) /\ match_on tabs (has_var e) ge le1 ge le1') (map snd l) ->
                 subset (bset_of_bindings l) Q ->
                 option_rel eq
                   (update_para_lenv  (eval_expr_rec  te ge) te le1 l le1')
                   (update_seq_lenv  (eval_expr_rec  te ge) te l le1')).
      {
        clear H.
        induction l; simpl.
        - constructor. reflexivity.
        - intros.
          inv H.
          eapply option_rel_bind_equal. intros.
          eapply option_rel_bind_rel.
          { apply eval_expr_match_on; auto.
            destruct H3 ; auto. }
          intros; subst.
          eapply IHl; eauto.
          eapply Forall_impl in H4;eauto.
          simpl.
          intros.
          destruct H1 ; split;eauto.
          apply match_on_update_r; auto.
          specialize (H0 (fst a)).
          specialize (H1 (fst a)).
          revert H0 H1.
          unfold union,inter,bot; simpl.
          unfold singleton.
          rewrite BSet.singleton_refl.
          simpl.
          rewrite andb_true_iff.
          destruct (has_var a1 (fst a)); auto.
          intuition. eapply subset_trans;eauto.
          eapply subset_morph2.
          intros. rewrite union_sym.
          reflexivity.
          apply subset_union1.
      }
      eapply H0 with (Q:= bset_of_bindings l).
      revert H.
      generalize (bset_of_bindings l).
      clear H0.
      induction l ; simpl.
      - constructor.
      - constructor. destruct H; auto.
        split;auto.
        apply match_on_refl.
        apply IHl.
        tauto.
      - apply subset_refl.
    Qed.




End DENOT.
