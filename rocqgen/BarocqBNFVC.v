(**  Generation of verification conditions to prove equivalence between
     Shallow and Deep embedding.

This is adapted from the [BarocqVC] version.
 *)

From Stdlib Require Import String List.
From compcert Require Import Integers Maps.
From BarocqComp Require Import  Denot Syntax Ident Option Barray Brecord Types BarocqBNF Maps2 MergeSort Utils.
From BarocqComp Require Import ExtEqual.
From compcert Require Import Coqlib.
From Stdlib Require Import ZifyBool.

Open Scope string_scope.
Local Open Scope option_monad_scope.

Definition ident_of_globdef (g : globdef) :=
  match g with
  | DefConst id _ _ => id
  | DefFun id _ => id
  | DeclConst id _ => id
  | DeclFun id _ _  => id
  end.

Section S.
  Variable tabs : PMap.t Type.

  Local Notation "# X" := (Types.eval_typ tabs X) (at level 90).

  (** Generation of proof obligations - some could be factorised *)

  Definition val_of_value (v: value tabs) : # (typeof_value tabs v) :=
    match v with
    | Val _ _ v => v
    end.

  Section VARLET.
    Variable vars_of_expr : STree.t unit -> expr -> STree.t unit.

    Definition vars_of_let (vars : STree.t unit) (x:ident) (e1 e2:expr) :=
      let vars_e2 :=
        match STree.get x vars with
        | Some _ => (* x escapes *) vars_of_expr vars e2
        | None   => STree.remove x (vars_of_expr vars e2)
        end in vars_of_expr vars_e2 e1.

  End VARLET.

  Section REMOVELETW.

    Fixpoint remove_let {A: Type} (l : list (ident * A)) (vars : STree.t unit) (vars2 : STree.t unit) :=
      match l with
      | nil => vars2
      | (x,_)::l => match STree.get x vars with
                    | Some _ => remove_let l vars vars2
                    | None   => remove_let l vars (STree.remove x vars2)
                    end
      end.

  End REMOVELETW.



  Fixpoint vars_of_atom (vars: STree.t unit) (a : Syntax.atom) : STree.t unit :=
    match a with
    | Syntax.ATrue
    | Syntax.AFalse
    | Syntax.AInt32 _ _
    | Syntax.AInt64 _ _
    | Syntax.AConstr _ _ _ => vars
    | Syntax.AVar id _ => STree.set id tt vars
    | Syntax.AUnaryOp _ a _
    | Syntax.ARecordProj a  _ _ _
    | Syntax.ACast a _ => vars_of_atom vars a
    | Syntax.AArrayGet a1 a2 _ _
    | Syntax.ABinaryOp _ a1 a2 _ => vars_of_atom (vars_of_atom vars a1) a2
    | Syntax.APureCall f _ l _ =>
        List.fold_left vars_of_atom l (STree.set f tt vars)
    end.



  Fixpoint vars_of_expr (vars : STree.t unit) (e:expr)  : STree.t unit :=
    match e with
    | EAtom a  => vars_of_atom vars a
    | EArraySet a1 a2 a3 _ => vars_of_atom (vars_of_atom (vars_of_atom vars a1) a2) a3
    | ERecordUpdate a1 _ a2 _ => vars_of_atom (vars_of_atom vars a1) a2
    | EApp e l _   => List.fold_left vars_of_atom l (vars_of_atom vars e)
    | EIfThenElse e1 e2 e3 _ => vars_of_expr (vars_of_expr (vars_of_atom vars e1) e2) e3
    | EMatch e1 cases _  =>
        MapList.fold_left (fun vars _ ep => vars_of_expr vars ep) cases (vars_of_atom vars e1)
    | ELetIn x e1 e2 _ =>
        vars_of_let vars_of_expr vars x e1 e2
    | ELetW l cond variant body e _ =>
        (* scopes? *)
        let vars_loop := vars_of_atom (vars_of_atom (vars_of_expr (vars_of_expr vars e) body) cond) variant in
        let vars_cont := remove_let l vars vars_loop in
        MapList.fold_left (fun vars _ e => vars_of_expr vars e) l vars_cont
    | EActR l  _     => (** What about field names? *)
        List.fold_left (fun acc v_a => vars_of_atom acc (snd v_a)) l vars
    | EAttr _ e => vars_of_expr vars e
    end.


  Lemma vars_of_expr_rw : forall (vars : STree.t unit) (e:expr),
      vars_of_expr vars e =
    match e with
    | EAtom a  => vars_of_atom vars a
    | EArraySet a1 a2 a3 _ => vars_of_atom (vars_of_atom (vars_of_atom vars a1) a2) a3
    | ERecordUpdate a1 _ a2 _ => vars_of_atom (vars_of_atom vars a1) a2
    | EApp e l _   => List.fold_left vars_of_atom l (vars_of_atom vars e)
    | EIfThenElse e1 e2 e3 _ => vars_of_expr (vars_of_expr (vars_of_atom vars e1) e2) e3
    | EMatch e1 cases _  =>
        MapList.fold_left (fun vars _ ep => vars_of_expr vars ep) cases (vars_of_atom vars e1)
    | ELetIn x e1 e2 _ => (* Ignore scopes - should remove x from e2 *)
        vars_of_let vars_of_expr vars x e1 e2
    | ELetW l cond variant body e _ =>
        let vars_loop := vars_of_atom (vars_of_atom (vars_of_expr (vars_of_expr vars e)  body) cond) variant in
        let vars_cont := remove_let l vars vars_loop in
        MapList.fold_left (fun vars _ e => vars_of_expr vars e) l vars_cont

    | EActR l  _     => (** What about field names? *)
        List.fold_left (fun acc v_a => vars_of_atom acc (snd v_a)) l vars
    | EAttr _ e => vars_of_expr vars e
    end.
  Proof.
    destruct e; reflexivity.
  Qed.


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

(*
  Lemma  map_err_same  {V A : Type} (f : V -> res A) (l : list (ident* V)) :
    map_err f l = MapList.map_err f l.
  Proof.
    induction l; simpl.
    - reflexivity.
    - destruct a; simpl.
      rewrite IHl.
      reflexivity.
  Qed.
*)
  Definition generate_def_fun_obligation (te:Typing.tenv)  (params : smaplist btyp) (tret : btyp) (e : expr) (checked : list (propt tabs))
    (prop : value tabs) : option Prop :=
    if MergeSort.nodup String.leb String.eqb (List.map fst params)
    then
      let* tret' := Typing.btyp_to_typ te tret in
      let* params' := MapList.mmap _ (Typing.btyp_to_typ te) params in
      let vars     := vars_of_fun params e in
      let needed_checked := List.filter (fun '(k,_) => has_var k vars) checked in
      let o := forall ge,
          Forall (has_property tabs ge) needed_checked ->
          let v := (eval_fun tabs  te ge params' tret'
                      e) in
          eq_value _ prop _ v  in
      ret o
    else fail.

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
      destruct (s2 ! (StringIndexed.index x)); try tauto;
      simpl in H.
    intuition congruence.
    inv H. inv H.
  Qed.




  Definition generate_def_fun_obligation' (f:ident) (te:Typing.tenv)  (params : smaplist btyp) (tret : btyp) (e : expr) (checked : list (propt tabs))
    (prop : value tabs) : option Prop :=
    if MergeSort.nodup String.leb String.eqb (List.map fst params)
    then
      let* tret' := Typing.btyp_to_typ te tret in
      let* params' := MapList.mmap _ (Typing.btyp_to_typ te) params in
      let vars     := vars_of_fun params e in
      let needed_checked := List.filter (fun '(k,_) => has_var k vars) checked in
      let ge := genv_has_property tabs STree.empty needed_checked in
      if stree_equal vars ge
      then
        let o :=
          let v := (eval_fun tabs  te ge params' tret' e) in
          eq_value _ prop _ v in
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

  Lemma eq_env_le : forall vars vars' le le' ge ge',
      eq_env vars' le le' ge ge' ->
      (forall x, STree.get x vars = Some tt -> STree.get x vars' = Some tt) ->
      eq_env vars le le' ge ge'.
  Proof.
    unfold eq_env; intros.
    apply H; auto.
  Qed.

  
  Fixpoint get_var_of_atom_acc (x:string) (a: Syntax.atom) :
    forall acc,
      STree.get x acc = Some tt ->
      STree.get x (vars_of_atom acc a) = Some tt.
  Proof.
    destruct a; simpl; auto.
    - intros.
      rewrite STree.gsspec.
      destruct (STree.elt_eq x i); auto.
    - intros.
      assert (STree.get x (STree.set i tt acc) = Some tt).
      {
        rewrite STree.gsspec.
        destruct (STree.elt_eq x i); auto.
      }
      revert H0.
      generalize (STree.set i tt acc) as acc'.
      induction l; simpl;auto.
  Qed.

  Fixpoint get_var_of_atom_case (x:string) (a:Syntax.atom): forall acc,
      STree.get x (vars_of_atom acc a) = Some tt <->
        (STree.get x acc = Some tt \/
           STree.get x (vars_of_atom STree.empty a) = Some tt).
  Proof.
    destruct a; simpl; try rewrite STree.gempty;
      try intuition congruence.
    - intros. rewrite! STree.gsspec.
      destruct (STree.elt_eq x i); subst.
      intuition congruence.
      rewrite STree.gempty. intuition congruence.
    - intros.
      rewrite get_var_of_atom_case.
      tauto.
    - intros.
      rewrite get_var_of_atom_case.
      tauto.
    - intros.
      rewrite get_var_of_atom_case.
      rewrite get_var_of_atom_case.
      rewrite get_var_of_atom_case with (acc:= vars_of_atom STree.empty a1).
      tauto.
    - intros.
      rewrite get_var_of_atom_case.
      rewrite get_var_of_atom_case.
      rewrite get_var_of_atom_case with (acc:= vars_of_atom STree.empty a1).
      tauto.
    - intros.
      rewrite get_var_of_atom_case.
      tauto.
    - assert (ACC': forall acc,
                 STree.get x (fold_left vars_of_atom l acc) = Some tt <->
                   STree.get x acc = Some tt \/ STree.get x (fold_left vars_of_atom l STree.empty) = Some tt).
      {
        induction l;simpl;auto.
        - rewrite STree.gempty. intuition congruence.
        - intros. rewrite IHl.
          symmetry. rewrite IHl.
          rewrite get_var_of_atom_case with (acc:= acc).
          tauto.
      }
      intros.
      rewrite ACC'.
      symmetry.
      rewrite ACC'.
      rewrite! STree.gsspec.
      rewrite STree.gempty.
      destruct (STree.elt_eq x i).
      intuition congruence.
      intuition congruence.
  Qed.

  Lemma get_var_remove_let_acc : forall {A:Type} (x:string) (l : list (ident * A)) acc acc'
      (LE : forall x, STree.get x acc = Some tt -> STree.get x acc' = Some tt),
      STree.get x acc = Some tt ->
      STree.get x (remove_let l acc acc') = Some tt.
  Proof.
    induction l; simpl.
    - auto.
    - destruct a.
      intros.
      destruct (STree.get i acc) eqn:GET.
      + eapply IHl ; eauto.
      + apply IHl; auto.
        intros.
        rewrite STree.grspec.
        destruct (STree.elt_eq x0 i). congruence.
        eapply LE;eauto.
  Qed.

  Lemma get_var_remove_let_acc_incr :
    forall {A: Type} (x:string) (l : list (ident * A)) acc1 acc1' acc2 acc2'
           (LE1 : forall x, STree.get x acc1 = Some tt -> STree.get x acc1' = Some tt)
           (LE2 : forall x, STree.get x acc2 = Some tt -> STree.get x acc2' = Some tt),
      STree.get x (remove_let l acc1 acc2) = Some tt ->
      STree.get x (remove_let l acc1' acc2') = Some tt.
  Proof.
    induction l; simpl.
    - auto.
    - destruct a.
      intros.
      destruct (STree.get i acc1) eqn:GET.
      + destruct u.  rewrite LE1 by auto.
        eapply IHl ; eauto.
      +  destruct (STree.get i acc1') eqn:ACC2.
         revert H.
         eapply IHl;eauto.
         intros. rewrite STree.grspec in H.
         destruct (STree.elt_eq x0 i). discriminate.
         eauto.
         revert H.  eapply IHl;eauto.
         intro.
         rewrite! STree.grspec.
         destruct (STree.elt_eq x0 i);auto.
  Qed.

  Lemma get_fold_left_acc :
    forall {A: Type} (vars_of_expr : PTree.t unit -> A -> PTree.t unit) (x:string)
                 (HYP :  forall acc e, STree.get x acc = Some tt
                                     -> STree.get x (vars_of_expr acc e) = Some tt)
           (l: list (string * A)) acc,


      STree.get x acc = Some tt ->
      STree.get x
        (MapList.fold_left (fun (vars : STree.t unit) (_ : Syntax.ident) (e : A) => vars_of_expr vars e) l
           acc) =
        Some tt.
  Proof.
    induction l; simpl; auto.
    destruct a.
    intros.
    apply IHl; auto.
  Defined.

  Lemma remove_let_iff : forall {A: Type} x (l:list (string * A))  acc acc',
      STree.get x (remove_let l acc acc') =
        if List.existsb (fun x_e => String.eqb x (fst x_e)) l
        then match STree.get x acc with
             | Some _ => STree.get x acc'
             | None   => None
             end
        else STree.get x acc'.
  Proof.
    induction l ; simpl; auto.
    destruct a.
    intros.
    destruct (STree.get s acc) eqn:GET.
    - simpl.
      rewrite IHl.
      destruct (string_dec x s).
      + subst. rewrite String.eqb_refl. simpl.
        destruct (existsb (fun x_e : string * A => s =? fst x_e) l) eqn:EX; auto.
        rewrite GET. auto.
      + assert (x =? s = false).
        {
          rewrite eqb_neq. auto.
        }
        rewrite H. auto.
    - simpl.
      rewrite IHl.
      destruct (string_dec x s).
      + subst. rewrite String.eqb_refl. simpl.
        rewrite GET.
        destruct (existsb (fun x_e : string * A => s =? fst x_e) l) eqn:EX; auto.
        apply STree.grs.
      +
        assert (x =? s = false).
        {
          rewrite eqb_neq. auto.
        }
        rewrite H. simpl.
        destruct (existsb (fun x_e : string * A => x =? fst x_e) l) eqn:EX.
        rewrite STree.grspec.
        destruct (STree.elt_eq x s); try congruence.
        rewrite STree.grspec.
        destruct (STree.elt_eq x s); try congruence.
  Qed.


  Fixpoint get_var_of_expr_acc (x:string) (e:expr): forall acc,
      STree.get x acc = Some tt ->
      STree.get x (vars_of_expr acc e) = Some tt.
  Proof.
    destruct e; simpl; auto.
    - intros.
      eapply get_var_of_atom_acc;eauto.
    - intros.
      eapply get_var_of_atom_acc;eauto.
      eapply get_var_of_atom_acc;eauto.
      eapply get_var_of_atom_acc;eauto.
    - intros.
      eapply get_var_of_atom_acc;eauto.
      eapply get_var_of_atom_acc;eauto.
    - intros.
      apply get_var_of_atom_acc with (a:=a) in H.
      revert H.
      generalize (vars_of_atom acc a) as acc'.
      induction l; simpl ; auto.
      {
        intros.
        apply IHl. apply get_var_of_atom_acc; auto.
      }
    - intros.
      eapply get_var_of_expr_acc; eauto.
      eapply get_var_of_expr_acc; eauto.
      eapply get_var_of_atom_acc;eauto.
    - intros.
      apply get_var_of_atom_acc with (a:=a) in H.
      revert H.
      generalize (vars_of_atom acc a) as acc'.
      induction l; simpl ; eauto.
      intros.
      destruct a0.
      eapply IHl; eauto.
    - intros.
      unfold vars_of_let.
      destruct (STree.get i acc) eqn:GET.
      +   rewrite get_var_of_expr_acc; auto.
      +  destruct (STree.elt_eq x i).
         congruence.
         apply get_var_of_expr_acc.
         rewrite STree.grspec.
         destruct (STree.elt_eq x i);try congruence.
         apply get_var_of_expr_acc;auto.
    - induction l;simpl; auto.
      intros. apply IHl.
      destruct a. apply get_var_of_atom_acc; auto.
    - intros.
      assert (ACC' : STree.get x (vars_of_atom (vars_of_atom (vars_of_expr (remove_let l acc (vars_of_expr acc e2)) e1) a) a0) = Some tt).
      {
        apply get_var_of_atom_acc.
        apply get_var_of_atom_acc.
        apply get_var_of_expr_acc.
        apply get_var_remove_let_acc.
        intros ; apply get_var_of_expr_acc;auto.
        assumption.
      }
      apply get_fold_left_acc.
      intros.
      apply get_var_of_expr_acc; auto.
      rewrite remove_let_iff.
      destruct (existsb (fun x_e : string * expr => x =? fst x_e) l) eqn:EX.
      +  rewrite H.
         apply get_var_of_atom_acc.
         apply get_var_of_atom_acc.
         apply get_var_of_expr_acc; auto.
      +  apply get_var_of_atom_acc.
         apply get_var_of_atom_acc.
         apply get_var_of_expr_acc; auto.
  Qed.



  Fixpoint get_var_of_expr_case (x:string) (e:expr): forall acc,
      STree.get x (vars_of_expr acc e) = Some tt <->
        (STree.get x acc = Some tt \/
           STree.get x (vars_of_expr STree.empty e) = Some tt).
  Proof.
    destruct e; simpl.
    - intros. rewrite get_var_of_atom_case.
      tauto.
    - intros. rewrite (get_var_of_atom_case x a1).
      rewrite (get_var_of_atom_case x a0).
      rewrite (get_var_of_atom_case x a).
      symmetry.
      rewrite (get_var_of_atom_case x a1).
      rewrite (get_var_of_atom_case x a0).
      rewrite (get_var_of_atom_case x a).
      tauto.
    - intros.
      rewrite (get_var_of_atom_case x a0).
      rewrite (get_var_of_atom_case x a).
      symmetry.
      rewrite (get_var_of_atom_case x a0).
      rewrite (get_var_of_atom_case x a).
      tauto.
    - 
      intros.
      assert (forall acc',
                 STree.get x (fold_left vars_of_atom l acc') = Some tt <->
                   (STree.get x acc' = Some tt \/
                      STree.get x (fold_left vars_of_atom l STree.empty) = Some tt)).
      {
        induction l.
        - simpl. rewrite STree.gempty.
          intuition congruence.
        - simpl. intros.
          rewrite IHl.
          symmetry.
          rewrite IHl. symmetry.
          rewrite (get_var_of_atom_case x a0 acc').
          tauto.
      }
      rewrite H.
      symmetry.
      rewrite H.
      rewrite (get_var_of_atom_case x a acc).
      tauto.
    - intros.
      rewrite (get_var_of_expr_case x e2).
      rewrite (get_var_of_expr_case x e1).
      rewrite (get_var_of_atom_case x a).
      symmetry.
      rewrite (get_var_of_expr_case x e2).
      rewrite (get_var_of_expr_case x e1).
      rewrite (get_var_of_atom_case x a).
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
          destruct a0.
          rewrite get_var_of_expr_case.
          symmetry. rewrite IHl.
          unfold F at 1. tauto.
      }
      intros.
      rewrite H. symmetry.
      rewrite H.
      rewrite (get_var_of_atom_case x a acc).
      tauto.
    - intros.
      unfold vars_of_let.
      rewrite STree.gempty.
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
    - induction l.
      + simpl. intros. rewrite STree.gempty.
        intuition congruence.
      + simpl.
        intros.
        destruct a.
        rewrite IHl.
        symmetry.
        rewrite IHl.
        rewrite (get_var_of_atom_case _ _ acc).
        tauto.
    -  assert (ACC' :
                 forall acc : STree.t unit,
                   STree.get x
                     (MapList.fold_left (fun (vars : STree.t unit) (_ : Syntax.ident) (e : expr) => vars_of_expr vars e) l
                        acc) =
                     Some tt <->
                     STree.get x acc = Some tt \/
                       STree.get x
                         (MapList.fold_left (fun (vars : STree.t unit) (_ : Syntax.ident) (e : expr) => vars_of_expr vars e) l
                            STree.empty) =
                         Some tt).
      {
        induction l ;simpl; auto.
        - rewrite STree.gempty. intuition congruence.
        - intros. destruct a1.
          rewrite IHl.
          symmetry. rewrite IHl.
          rewrite get_var_of_expr_case with (acc:=acc).
          intuition congruence.
      }
      intro.
      rewrite ACC'.
      symmetry.
      rewrite ACC'.
      rewrite! remove_let_iff.
      destruct (existsb (fun x_e : string * expr => x =? fst x_e) l).
      + rewrite ! STree.gempty.
        destruct (STree.get x acc) eqn:GACC.
        * destruct u.
          rewrite get_var_of_atom_case.
          rewrite get_var_of_atom_case.
          rewrite get_var_of_expr_case with (acc:=(vars_of_expr acc e2)).
          rewrite get_var_of_expr_case with (acc:=acc).
          intuition  congruence.
        * intuition congruence.
      +   rewrite get_var_of_atom_case.
          rewrite get_var_of_atom_case.
          rewrite get_var_of_expr_case with (acc:= vars_of_expr STree.empty e2).
          rewrite get_var_of_atom_case with (acc:=vars_of_atom (vars_of_expr (vars_of_expr acc e2) e1) a).
          rewrite get_var_of_atom_case with (acc:= (vars_of_expr (vars_of_expr acc e2) e1)).
          rewrite get_var_of_expr_case with (acc:= vars_of_expr acc e2).
          rewrite get_var_of_expr_case with (acc:= acc).
          intuition congruence.
    - apply get_var_of_expr_case.
  Qed.

  Definition eq_env_vars_of_atom_acc (a:atom) : forall acc le le' ge ge',
      eq_env (vars_of_atom acc a) le le' ge ge' ->
      eq_env acc le le' ge ge'.
  Proof.
    unfold eq_env.
    intros.
    apply H; auto.
    apply get_var_of_atom_acc; auto.
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

  Definition eq_env_vars_of_atom (a:atom) : forall acc le le' ge ge',
      eq_env (vars_of_atom acc a) le le' ge ge' ->
      eq_env (vars_of_atom STree.empty a) le le' ge ge'.
  Proof.
    unfold eq_env.
    intros.
    apply H; auto.
    rewrite get_var_of_atom_case.
    tauto.
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

  Lemma get_fold_vars_of_atom : forall x args acc,
      STree.get x (fold_left vars_of_atom args acc) = Some tt <->
        (STree.get x (fold_left vars_of_atom args STree.empty) = Some tt \/
           STree.get x acc = Some tt).
  Proof.
    induction args ; simpl.
    -  intros. rewrite STree.gempty. intuition congruence.
    - intros.
      rewrite IHargs.
      rewrite get_var_of_atom_case.
      symmetry.
      rewrite IHargs.
      tauto.
  Qed.

  Lemma eq_env_exprs : forall args acc le le' ge ge',
      eq_env (fold_left vars_of_expr args acc) le le' ge ge' <->
      eq_env (fold_left vars_of_expr args STree.empty) le le' ge ge' /\
        eq_env acc le le' ge ge'.
  Proof.
    unfold eq_env; simpl; split; intros.
    - split; intros.
      apply H;auto.
      rewrite get_fold_vars_of_expr; tauto.
      apply H;auto.
      rewrite get_fold_vars_of_expr; tauto.
    - destruct H.
      rewrite get_fold_vars_of_expr in H2.
      destruct H2; auto.
  Qed.

  Lemma fold_left_snd : forall {A B C: Type} F (args : list (A * B)) acc,
      fold_left (fun (acc0 : C) (v_a : A * B) => F acc0 (snd v_a)) args acc =
        fold_left F (List.map snd args) acc.
  Proof.
    induction args ; simpl;auto.
  Qed.



  Lemma eq_env_exprs_snd : forall args acc le le' ge ge' ,
    eq_env
      (MapList.fold_left (fun (vars : STree.t unit) (_ : Syntax.ident) (e : expr) => vars_of_expr vars e) args
         acc) le le' ge ge' <->
    eq_env (MapList.fold_left (fun (vars : STree.t unit) (_ : Syntax.ident) (e : expr) => vars_of_expr vars e) args
               STree.empty) le le' ge ge' /\ eq_env acc le le' ge ge'.
  Proof.
    intros.
    rewrite! MapList.fold_left_eq in *.
    rewrite! fold_left_snd in *.
    apply eq_env_exprs;auto.
  Qed.

  Lemma eq_env_atoms : forall args acc le le' ge ge',
      eq_env (fold_left vars_of_atom args acc) le le' ge ge' ->
      eq_env (fold_left vars_of_atom args STree.empty) le le' ge ge' /\
        eq_env acc le le' ge ge'.
  Proof.
    unfold eq_env; simpl; split; intros.
    apply H;auto.
    rewrite get_fold_vars_of_atom; tauto.
    apply H;auto.
    rewrite get_fold_vars_of_atom; tauto.
  Qed.

  Lemma eq_env_snd_atoms : forall {A: Type} (args: list (A * atom)) acc le le' ge ge',
      eq_env (fold_left (fun acc v_a => vars_of_atom acc (snd v_a)) args acc) le le' ge ge' ->
      eq_env (fold_left (fun acc v_a => vars_of_atom acc (snd v_a)) args STree.empty) le le' ge ge' /\
        eq_env acc le le' ge ge'.
  Proof.
    intros.
    rewrite fold_left_snd in *.
    apply eq_env_atoms; auto.
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

  Lemma  ext_equal_eval_match : forall te x y tr l1 l2,
      ext_equal tabs te x y ->
      Forall2 (fun x y => fst x = fst y /\ option_rel (ext_equal tabs tr) (snd x) (snd y))  l1 l2 ->
      option_rel (ext_equal tabs tr) (eval_match tabs te x l1) (eval_match tabs te y  l2).
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

  Lemma eq_env_remove : forall x P le le' v1 v2 ge ge',
      eq_env (STree.remove x P) le le' ge ge' ->
      eq_env P (lenv_update tabs le x v1) (lenv_update tabs le' x v2) ge ge'.
  Proof.
    unfold eq_env;intros.
    unfold lenv_update in *.
    rewrite STree.gsspec in *.
    destruct (STree.elt_eq x0 x); try congruence.
    apply H; auto.
    rewrite STree.gro;auto.
  Qed.

  Lemma eq_env_remove2 : forall x P le le' v1 v2 ge ge',
      eq_env  P le le' ge ge' ->
      eq_env (STree.remove x P) (lenv_update tabs le x v1) (lenv_update tabs le' x v2) ge ge'.
  Proof.
    unfold eq_env;intros.
    unfold lenv_update in *.
    rewrite STree.gsspec in *.
    rewrite STree.grspec in *.
    destruct (STree.elt_eq x0 x); try congruence.
    apply H; auto.
  Qed.






  Lemma eq_env_eval_var :
    forall s le le' ge ge' v ty
           (GE: eq_env s le le' ge ge')
           (LE:eq_env_all le le')
           (GET:STree.get v s = Some tt),
      option_rel (ext_equal tabs ty) (eval_var tabs ge le v ty) (eval_var tabs ge' le' v ty).
  Proof.
    intros.
    unfold eval_var.
    apply option_rel_bind_rel with (RA:= same_value tabs).
    { specialize (LE v).
      unfold get_env.
      inv LE.
      apply GE; auto.
      constructor ;auto. }
    intros.
    apply same_value_cast_value; auto.
  Qed.

  Fixpoint eq_genv_eval_atom  (te:Typing.tenv)  (ge ge':genv tabs) (ty:typ) (a:atom) : forall le le',
      eq_env (vars_of_atom (STree.empty) a) le le' ge ge' ->
      eq_env_all le le'  ->
      option_rel (ext_equal tabs ty) (eval_atom tabs te ge le ty a)
        (eval_atom tabs te ge' le' ty a).
  Proof.
    specialize (eq_genv_eval_atom te ge ge').
    destruct a; intros; simpl; try (apply ExtEqual.option_rel_cast_typ_refl;reflexivity).
    - unfold eval_constr. destruct ty; simpl; try constructor.
      apply option_rel_refl; intro; reflexivity.
    - eapply eq_env_eval_var; eauto.
      simpl.
      rewrite STree.gss.  reflexivity.
    - destruct (Typing.btyp_to_typ te b); try reflexivity.
      simpl.
      destruct (Typing.typof_atom te a); try constructor.
      simpl.
      specialize (eq_genv_eval_atom t0 a le le' H H0).
      inv eq_genv_eval_atom.
      constructor.
      simpl.
      eapply ExtEqual.ext_equal_eval_cast with (t:=t)in H3;eauto.
      apply ext_equal_ecast_typ; auto.
      constructor.
    - destruct (Typing.typof_atom te a); try constructor.
      simpl.
      specialize (eq_genv_eval_atom t a le le' H H0).
      inv eq_genv_eval_atom.
      constructor.
      simpl.
      apply ExtEqual.ext_equal_eval_unary_op; auto.
    - simpl in H.
      destruct (Typing.typof_atom te a1); try constructor.
      destruct (Typing.typof_atom te a2); try constructor.
      simpl.
      generalize (eq_genv_eval_atom t a1 le le' (eq_env_vars_of_atom_acc _ _ _ _ _ _ H) H0).
      generalize (eq_genv_eval_atom t0 a2 le le' (eq_env_vars_of_atom _ _ _ _ _ _ H) H0).
      intros E2 E1.
      inv E1 ; try constructor.
      simpl. inv E2 ; try constructor.
      simpl.
      apply ext_equal_eval_binary_op; auto.
    - simpl in H.
      apply option_rel_bind_equal.
      intros t1 _.
      apply option_rel_bind_equal.
      intros t2 _.
      eapply option_rel_bind_rel.
      { apply eq_genv_eval_atom; auto.
        eapply eq_env_vars_of_atom_acc; eauto.
      }
      intros.
      eapply option_rel_bind_rel.
      { apply eq_genv_eval_atom; auto.
        eapply eq_env_vars_of_atom; eauto.
      }
      intros.
      apply ext_equal_array_get; auto.
    - simpl in H.
      apply option_rel_bind_equal.
      intros t1 _.
      eapply option_rel_bind_rel.
      { apply eq_genv_eval_atom; auto.
      }
      intros.
      apply ext_equal_eval_record_proj; auto.
    - simpl in H.
      apply option_rel_bind_equal.
      intros t1 _.
      apply eq_env_atoms in H as (EQ1 & EQ2).
      destruct t1; try constructor.
      apply option_rel_bind_rel with (RA:= ext_equal tabs (TFun l0 t1)).
      eapply eq_env_eval_var; eauto.
      rewrite STree.gss. reflexivity.
      set (Ftyp := fun (ty:typ) => option (eval_typ tabs ty)).
      set (Pred := fun ty => option_rel (ext_equal tabs ty)).
      assert (option_rel (DList.Forall2 Ftyp Pred  _) (DList.map2 (eval_typ tabs) (eval_atom tabs te ge le) l l0)
                (DList.map2 (eval_typ tabs) (eval_atom tabs te ge' le') l l0)).
      {
        revert l0.
        induction l; destruct l0.
        - simpl. constructor. constructor.
        - simpl.
          constructor.
        - simpl. constructor.
        - simpl.
          simpl in EQ1.
          apply eq_env_atoms in EQ1 as (EQ1 & EQ1').
          specialize (eq_genv_eval_atom t a le le' EQ1' H0).
          specialize (IHl EQ1 l0).
          inv IHl.
          constructor.
          simpl. constructor.
          constructor ;auto.
      }
      intros.
      eapply option_rel_bind_rel.
      eapply H.
      intros.
      apply ext_equal_eval_app_res; auto.
  Qed.

  Definition and_rel {A B: Type} (R1 R2: A -> B -> Prop) :=
    fun x y => R1 x y /\ R2 x y.

  Lemma option_rel_and_rel : forall A B (R1 R2 : A -> B -> Prop) x y,
      option_rel R1 x y ->
      option_rel R2 x y ->
      option_rel (and_rel R1 R2) x y.
  Proof.
    intros.
    inv H.
    - constructor.
    - inv H0. constructor; split;auto.
  Qed.

  Lemma option_rel_and_rel_swap : forall A B (R1 R2 : A -> B -> Prop) x y,
      option_rel (and_rel R1 R2) x y ->
      option_rel (and_rel R2 R1) x y.
  Proof.
    intros.
    inv H.
    - constructor.
    - destruct H0.
      constructor.
      unfold and_rel ; auto.
  Qed.

  Lemma option_rel_and_rel_mp : forall A B (R1 R2 : A -> B -> Prop) x y,
      (option_rel R1 x y) ->
      (option_rel R1 x y -> option_rel R2 x y) ->
      option_rel (and_rel R1 R2) x y.
  Proof.
    intros.
    inv H.
    - constructor.
    -  constructor.
      unfold and_rel ; auto.
      split; auto.
      specialize (H0 (option_rel_some _ _ _ H1)).
      inv H0. auto.
  Qed.



  Definition has_keys {A: Type} (P: list (ident * A)) (le:lenv tabs) : bool :=
    forallb (fun x => SSet.mem (fst x) (STree.keys le)) P.

  Lemma has_keys_nil : forall {A: Type}  (le:lenv tabs),
      has_keys (A:=A) nil le = true.
  Proof.
    unfold has_keys.
    simpl. tauto.
  Qed.

  Lemma has_keys_cons : forall {A: Type} (e:ident * A) l le,
      has_keys (e::l) le =
        (SSet.mem (fst e) (STree.keys le) && has_keys l le).
  Proof.
    unfold has_keys.
    simpl. intros. split ; intros.
  Qed.

  Lemma has_keys_map : forall {A: Type} (l1 l2: list (string * A)) le,
      map fst l1 = map fst l2 ->
      has_keys l1 le = has_keys l2 le.
  Proof.
    unfold has_keys.
    induction l1 ; simpl; auto.
    - destruct l2 ; simpl; try discriminate.
      reflexivity.
    - destruct l2 ; simpl ; try discriminate.
      intros. inv H.
      apply IHl1 with (le:=le) in H2.
      f_equal;auto.
      f_equal. auto.
  Qed.

    
  Lemma eq_env_all_update_para_lenv :
    forall  te ge ge'
            (eq_genv_eval_expr_rec :
              forall (ty : typ) (e : expr) (le le' : lenv tabs),
                eq_env (vars_of_expr STree.empty e) le le' ge ge' ->
                eq_env_all le le' -> option_rel (ext_equal tabs ty) (eval_expr_rec tabs te ge le ty e) (eval_expr_rec tabs te ge' le' ty e)),
    forall (le le':lenv tabs) l (l1 l1':lenv tabs) P
           (ALL_EVAL : eq_env_all le le')
           (ALL : eq_env_all l1 l1')
           (EQ: eq_env (remove_let l STree.empty P) l1 l1' ge ge')
           (FORALL : Forall (fun x_e => eq_env (vars_of_expr STree.empty (snd x_e)) le le' ge ge') l),
      option_rel (and_rel eq_env_all (fun le le' =>
                                  eq_env  P le le' ge ge'))
        (update_para_lenv tabs (eval_expr_rec tabs te ge) te le l l1)
        (update_para_lenv tabs (eval_expr_rec tabs te ge') te le' l l1').
  Proof.
    induction l; simpl.
    - constructor. split; auto.
    - simpl ; intros.
      apply option_rel_bind_equal.
      intros tya1 _.
      eapply option_rel_bind_rel.
      eapply eq_genv_eval_expr_rec; eauto.
      inv FORALL. auto.
      intros.
      destruct a.
      eapply IHl; auto.
      { apply eq_env_all_lenv_update; auto. }
      { simpl.
      apply eq_env_remove; auto.
      eapply eq_env_le.
      apply EQ.
      {
        clear H0 H1.
        intros.
        rewrite STree.grspec in H0.
        rewrite remove_let_iff in *.
        rewrite STree.gempty in *.
        rewrite STree.grspec.
        destruct (STree.elt_eq x0 i).
        discriminate.
        auto.
      }
      }
      inv FORALL ; auto.
  Defined.


  Lemma keys_update_para_lenv :
    forall  te  F l,
    forall (le le1 le2:lenv tabs),
      (update_para_lenv tabs F te le l le1) = Some le2 ->
      forall x, SSet.mem x (STree.keys le2) =
                  (SSet.mem x (STree.keys le1) || MapList.mem string_dec x l).
  Proof.
    induction l ; simpl.
    - intros. inv H. rewrite orb_false_r.
      reflexivity.
    - intros.
      monadInv H.
      apply IHl with (x:= x) in EQ2.
      rewrite EQ2.
      destruct a.
      rewrite keys_lenv_update.
      simpl.
      rewrite SSet.mem_add.
      destruct (string_dec x i);
        destruct (string_dec i x); try congruence; simpl.
      rewrite orb_true_r.
      reflexivity.
  Defined.

  Lemma has_keys_update_para_lenv :
    forall {A: Type} te ge (le: lenv tabs) l le1 (lt:list (string *A))
            (UP1 : update_para_lenv tabs (eval_expr_rec tabs te ge) te le l le =
                     Some le1)
        (MMAP : map fst l = map fst lt),
      has_keys lt le1 = true.
  Proof.
    intros.
    unfold has_keys.
    rewrite forallb_forall.
    intros.
    apply keys_update_para_lenv with (x:=fst x) in UP1.
    rewrite UP1.
    rewrite orb_true_iff.
    right.
    apply in_map with (f:=fst) in H.
    setoid_rewrite <- MMAP in H.
    rewrite in_map_iff in H.
    destruct H as (x1 & EQ & IN).
    apply MapList.in_mem with (v:= snd x1); auto.
    destruct x1,x ; simpl in *.
    subst. auto.
  Qed.


(*

  Lemma eq_env_all_update_lenv :
    forall  te ge ge'
            (eq_genv_eval_expr_rec :
              forall (ty : typ) (e : expr) (le le' : genv tabs),
                eq_env (vars_of_expr STree.empty e) le le' ge ge' ->
                eq_env_all le le' -> option_rel (ext_equal tabs ty) (eval_expr_rec tabs te ge le ty e) (eval_expr_rec tabs te ge' le' ty e)),
           forall le le' l l1 l1',
             eq_env_all le le' ->
             eq_env_all l1 l1' ->
             eq_env P l1 l1' ge ge' ->
             Forall (fun x_e => eq_env (vars_of_expr STree.empty (snd x_e)) le le' ge ge') l ->
             option_rel eq_env_all (update_lenv tabs (eval_expr_rec tabs te ge le) te l l1)
               (update_lenv tabs (eval_expr_rec tabs te ge' le') te l l1').
  Proof.
    induction l.
    - simpl. constructor. auto.
    - simpl.
      intros.
      apply option_rel_bind_equal.
      intro tya1.
      eapply option_rel_bind_rel.
      eapply eq_genv_eval_expr_rec; eauto.
      inv H1. auto.
      intros.
      apply IHl; auto.
      apply eq_env_all_lenv_update; auto.
      inv H1 ; auto.
Defined.
*)

  Lemma ext_equal_nat_of_var : forall ty v1 v2,
      ext_equal tabs ty v1 v2 ->
      option_rel eq (nat_of_val tabs v1) (nat_of_val tabs v2).
  Proof.
    unfold nat_of_val.
    destruct ty; try constructor.
    - destruct s; try constructor.
      +  simpl in H. congruence.
      +  simpl in H; congruence.
    - destruct s; try constructor.
      +  simpl in H. congruence.
      +  simpl in H; congruence.
  Qed.


  Definition same_value_eq (v1 v2: value tabs) :=
    same_value tabs v1 v2 \/ v1 = v2.

  Lemma get_env_eq_env_all : forall ge ge' le1 le2 x,
      eq_env_all le1 le2 ->
      STree.get x le1 <> None ->
      option_rel (same_value tabs)
        (get_env tabs ge le1 x)
        (get_env tabs ge' le2 x).
  Proof.
    unfold eq_env_all.
    intros.
    specialize (H x).
    unfold get_env.
    inv H; try congruence.
    constructor; auto.
  Qed.


  Lemma equal_record_record_of_lenv : forall ge ge' le1 le1',
      eq_env_all le1 le1' ->
      forall lty,
        has_keys lty le1 = true ->
        option_rel (equal_record tabs (ext_equal tabs) lty)
        (record_of_lenv tabs ge lty le1) (record_of_lenv tabs ge' lty le1').
  Proof.
    induction lty.
    - simpl. constructor. tauto.
    - simpl. destruct a.
      simpl; intros.
      rewrite andb_true_iff in H0.
      destruct H0 as (MEM1 & MEM2).
      eapply option_rel_bind_rel with (RA:=same_value tabs).
      apply get_env_eq_env_all; auto.
      rewrite STree.keys_get_mem_false_iff. intuition congruence.
      intros x y SV _ _ .
      eapply option_rel_bind_rel with (RA:= ext_equal tabs t).
      apply same_value_cast_value; auto.
      intros x0 y0 EQ _ _ .
      eapply option_rel_bind_rel with (RA:= (equal_record tabs (ext_equal tabs) lty)); eauto.
      intros. constructor.
      simpl. split; auto.
  Qed.

  Lemma option_rel_ext_equal_bool : forall  v1 v2,
      option_rel (ext_equal tabs TBool) v1 v2 ->
      v1 = v2.
  Proof.
    intros. inv H.
    - reflexivity.
    - simpl in H0.
      congruence.
  Qed.

  Lemma eq_env_lenv_of_record : forall P lt r1 r2 ge ge' le1 le2,
      eq_env P le1 le2 ge ge' ->
      eq_env P
        (lenv_of_record tabs lt r1 le1) (lenv_of_record tabs lt r2 le2)
        ge ge'.
  Proof.
    induction lt.
    - simpl. auto.
    - intros.
      simpl.
      intros.
      apply IHlt.
      apply eq_env_remove.
      eapply eq_env_le. apply H.
      intros.
      rewrite STree.grspec in H0.
      destruct (STree.elt_eq x (fst a)); congruence.
  Qed.

  Lemma eq_env_all_lenv_of_record : forall lt r1 r2 le1 le2,
      eq_env_all le1 le2 ->
      equal_record tabs (ext_equal tabs) lt r1 r2 ->
      eq_env_all (lenv_of_record tabs lt r1 le1) (lenv_of_record tabs lt r2 le2).
  Proof.
    induction lt.
    - simpl. auto.
    - intros.
      simpl.
      intros.
      apply IHlt.
      apply eq_env_all_lenv_update; auto.
      simpl in H0. destruct a.
      tauto. simpl in H0 ; destruct a; tauto.
  Qed.


  Fixpoint eq_genv_eval_expr_rec (te:Typing.tenv)  (ge ge':genv tabs) (ty:typ) (e:expr) : forall le le',
      eq_env (vars_of_expr (STree.empty) e) le le' ge ge' ->
      eq_env_all le le'  ->
      option_rel (ext_equal tabs ty) (eval_expr_rec tabs te ge le ty e)
        (eval_expr_rec tabs te ge' le' ty e).
  Proof.
    specialize (eq_genv_eval_expr_rec te ge ge').
    destruct e; intros; simpl; try (apply option_rel_cast_typ_refl;reflexivity).
    - apply option_rel_bind_equal.
      intros.
      apply ext_equal_ecast_typ.
      eapply eq_genv_eval_atom;eauto.
    - apply option_rel_bind_equal.
      intros t1 _.
      apply option_rel_bind_equal.
      intros t2 _.
      apply option_rel_bind_equal.
      intros t3 _.
      apply option_rel_bind_equal.
      intros t4 _.
      eapply option_rel_bind_rel.
      { apply eq_genv_eval_atom; auto.
        simpl in H.
        eapply eq_env_vars_of_atom_acc.
        eapply eq_env_vars_of_atom_acc.
        eauto.
      }
      intros.
      eapply option_rel_bind_rel.
      { apply eq_genv_eval_atom; auto.
        simpl in H.
        apply eq_env_vars_of_atom_acc in H.
        apply eq_env_vars_of_atom in H.
        auto.
      }
      intros.
      eapply option_rel_bind_rel.
      {
        simpl in H.
        apply eq_genv_eval_atom; auto.
        apply eq_env_vars_of_atom in H.
        auto.
      }
      intros.
      eapply ext_equal_ecast_typ.
      eapply ext_equal_array_set;eauto.
    - apply option_rel_bind_equal.
      intros t1 _.
      apply option_rel_bind_equal.
      intros t2 _.
      apply option_rel_bind_equal.
      intros t3 _.
      eapply option_rel_bind_rel.
      {
        apply eq_genv_eval_atom; auto.
        simpl in H.
       eapply eq_env_vars_of_atom_acc in H; auto.
      }
      intros.
      eapply option_rel_bind_rel.
      { apply eq_genv_eval_atom; auto.
        simpl in H.
        apply eq_env_vars_of_atom in H.
        auto.
      }
      intros.
      eapply ext_equal_ecast_typ.
      eapply ext_equal_eval_record_update;eauto.
    - simpl in H.
      apply option_rel_bind_equal.
      intros t1 _.
      apply option_rel_bind_equal.
      intros t2 _.
      apply eq_env_atoms in H as (EQ1 & EQ2).
      destruct t2; try constructor.
      apply option_rel_bind_rel with (RA:= ext_equal tabs (TFun l0 t2)).
      eapply eq_genv_eval_atom; eauto.
      intros.
      clear H1 H2.
      set (Ftyp := fun (ty:typ) => option (eval_typ tabs ty)).
      set (Pred := fun ty => option_rel (ext_equal tabs ty)).
      clear EQ2.
      assert (option_rel (DList.Forall2 Ftyp Pred  _) (DList.map2 (eval_typ tabs) (eval_atom tabs te ge le) l l0)
                (DList.map2 (eval_typ tabs) (eval_atom tabs te ge' le') l l0)).
      {
        clear x y H.
        revert l0.
        induction l; destruct l0.
        - simpl. constructor. constructor.
        - simpl.
          constructor.
        - simpl. constructor.
        - simpl.
          simpl in EQ1.
          apply eq_env_atoms in EQ1 as (EQ1 & EQ1').
          simpl.
          specialize (eq_genv_eval_atom te ge ge' t a0 le le' EQ1' H0).
          specialize (IHl EQ1 l0).
          intros.
          inv IHl.
          constructor.
          simpl. constructor.
          constructor ;auto.
      }
      intros.
      eapply option_rel_bind_rel.
      eapply H1.
      intros.
      apply ext_equal_ecast_typ.
      apply ext_equal_eval_app_res; auto.
    - simpl in H.
      apply eq_env_split in H as (EQ1 & EQ2).
      apply eq_env_split in EQ2 as (EQ2 & EQ3).
      eapply option_rel_bind_rel with (RA:= ext_equal tabs TBool) ;eauto.
      eapply eq_genv_eval_atom;eauto.
      intros.
      simpl in H. subst.
      destruct y; eauto.
    - simpl in H.
      apply eq_env_pattern in H.
      eapply option_rel_bind_equal.
      intros.
      eapply option_rel_bind_rel;eauto.
      eapply eq_genv_eval_atom;eauto.
      tauto.
      intros.
      destruct H as (EQ1 & EQ2).
      apply ext_equal_eval_match; auto.
      revert EQ1.
      induction l.
      + simpl. constructor.
      + simpl.
        destruct a1.
        intros.
        apply eq_env_pattern in EQ1.
        constructor.
        simpl. split;auto.
        apply eq_genv_eval_expr_rec.
        destruct EQ1. auto.
        auto.
        apply IHl.
        tauto.
    - simpl in H.
      eapply option_rel_bind_equal.
      intros t _.
      apply eq_env_split in H as (EQ1 & EQ2).
      eapply option_rel_bind_rel.
      eapply eq_genv_eval_expr_rec; eauto.
      intros.
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
    - (* ActR *)
      destruct ty ; try constructor.
      destruct o; try constructor.
      eapply option_rel_bind_equal.
      intros.
      destruct (typ_eqb (TRecord None l0) a);
        try constructor.
      rewrite vars_of_expr_rw in H.
      {
        change (ext_equal tabs (TRecord None l0))
          with  (equal_record tabs (ext_equal tabs) l0).
        revert l0.
        induction l.
        - simpl. destruct l0.
          + constructor.
            apply I.
          + constructor.
        - destruct l0.
          + simpl. destruct a0; constructor.
          + simpl.
            destruct p as (id,ty).
            destruct a0 as (id',a').
            destruct (string_dec id' id).
            *  subst.
               assert (EA : option_rel (ext_equal tabs ty)
                              (eval_atom tabs te ge le ty a')
                              (eval_atom tabs te ge' le' ty a')).
               {
                 apply eq_genv_eval_atom; auto.
                 - simpl in H.
                   apply eq_env_snd_atoms in H. tauto.
               }
               assert (ER : option_rel
                              (equal_record tabs (ext_equal tabs) l0)
                              (eval_act_record tabs (eval_atom tabs) te ge l l0 le)
                              (eval_act_record tabs (eval_atom tabs) te ge' l l0 le')).
               {
                 apply IHl; auto.
                 simpl in H.
                 apply eq_env_snd_atoms in H.
                 tauto.
               }
               eapply option_rel_bind_rel.
               apply EA.
               intros.
               eapply option_rel_bind_rel.
               apply ER.
               constructor.
               simpl. tauto.
            * constructor.
      }
    - (* while *)
      simpl in H.
      eapply option_rel_bind_rel.
      { apply eq_env_all_update_para_lenv; auto.
        - rewrite eq_env_exprs_snd in H.
          destruct H.
          apply H1.
        - rewrite eq_env_exprs_snd in H.
          destruct H.
          clear H1.
          { induction l ; simpl in *.
            - constructor.
            -  apply eq_env_exprs_snd in H.
               destruct a1.
               constructor ;tauto.
          }
      }
      intros le1 le1' EQ UP1 UP2.
      destruct EQ as (EQ1 & EQ2).
      apply option_rel_bind_equal.
      intros tya _.
      (* Evaluate the variant *)
      eapply option_rel_bind_rel with (RA:= ext_equal tabs tya).
      { apply eq_genv_eval_atom;auto.
        eapply eq_env_le.
        apply EQ2.
        intros.
        rewrite get_var_of_atom_case.
        tauto.
      }
      intros.
      eapply option_rel_bind_rel with (RA := @eq nat).
      apply ext_equal_nat_of_var; auto.
      intros ; subst.
      apply option_rel_bind_equal.
      intros lt MMAP.
      (* Construct the initial activation record *)
      intros.
      eapply option_rel_bind_rel with (RA :=
                                         equal_record tabs (ext_equal tabs) lt).
      apply MapList.mmap_fst in MMAP.
      apply equal_record_record_of_lenv; auto.
      {
        eapply has_keys_update_para_lenv; eauto.
      }
      intros ar1 ar2 EQR _ _.
      eapply option_rel_bind_rel with (RA :=
                                         equal_record tabs (ext_equal tabs) lt).
      eapply While.while_rel; auto.
      intros.
      apply option_rel_ext_equal_bool.
      apply eq_genv_eval_atom.
      apply eq_env_lenv_of_record; auto.
      apply eq_env_vars_of_atom_acc in EQ2.
      apply eq_env_vars_of_atom in EQ2. auto.
      apply eq_env_all_lenv_of_record ; auto.
      {
        intros.
        assert (option_rel (ext_equal tabs (TRecord None lt))
                  (eval_expr_rec tabs te ge (lenv_of_record tabs lt i1 le1) (TRecord None lt) e1)
                  (eval_expr_rec tabs te ge' (lenv_of_record tabs lt i2 le1') (TRecord None lt) e1)).
        {
          apply eq_genv_eval_expr_rec; auto.
          apply eq_env_lenv_of_record.
          apply eq_env_vars_of_atom_acc in EQ2.
          apply eq_env_vars_of_atom_acc in EQ2.
          apply eq_env_vars_of_expr in EQ2.
          auto.
          apply eq_env_all_lenv_of_record; auto.
        }
        auto.
      }
      {
        intros.
        apply eq_genv_eval_expr_rec.
        apply eq_env_lenv_of_record.
        apply eq_env_vars_of_atom_acc in EQ2.
        apply eq_env_vars_of_atom_acc in EQ2.
        apply eq_env_vars_of_expr_acc in EQ2.
        auto.
        apply eq_env_all_lenv_of_record; auto.
      }
    - apply eq_genv_eval_expr_rec; tauto.
  Qed.

  Lemma eq_genv_eval_expr (te:Typing.tenv)  (ge ge':genv tabs) (ty:typ) (e:expr) : forall le le',
      eq_env (vars_of_expr (STree.empty) e) le le' ge ge' ->
      eq_env_all le le'  ->
      option_rel (ext_equal tabs ty) (eval_expr tabs te ge le ty e)
        (eval_expr tabs te ge' le' ty e).
  Proof.
    unfold eval_expr.
    intros.
    generalize (eq_genv_eval_expr_rec te ge ge' ty e le le' H H0).
    intro EQ. inv EQ.
    constructor. simpl. constructor ;auto.
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

  Lemma eval_fun_rec_eq : forall te ge ge' lt e le le' t,
      eq_env (vars_of_fun lt e) le le' ge ge' ->
      eq_env_all le le' ->
      ext_fun tabs (ext_equal tabs) t (map snd lt) (eval_fun_rec tabs (eval_expr tabs) te  ge le lt t e)
        (eval_fun_rec tabs (eval_expr tabs) te ge' le' lt t e).
  Proof.
    unfold vars_of_fun.
    induction lt.
    - simpl.
      intros.
      specialize (eq_genv_eval_expr te ge ge' t e le le' H H0).
      intro E1.
      inv E1.
      constructor.
      constructor.
      auto.
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
      MapList.mmap _ F l1  = Some l2 ->
      map fst l1 = map fst l2.
  Proof.
    induction l1;simpl;auto.
    - intros. inv H. reflexivity.
    - intros.
      monadInv H.
      monadInv EQ.
      simpl. f_equal;auto.
  Qed.

  Lemma map_err_nil
     : forall (A B : Type) (F : A -> option B) (l : list (string * A)),
      MapList.mmap _ F l = Some nil -> l = nil.
  Proof.
    destruct l; simpl.
    - reflexivity.
    - intros. monadInv H.
  Qed.
  
  Lemma generate_def_fun_obligation_impl : forall f te params tret e checked prop o',
      generate_def_fun_obligation' f te params tret e checked prop = Some o' ->
      exists o, generate_def_fun_obligation te params tret e checked prop = Some o /\
                  (o' -> o).
  Proof.
    unfold generate_def_fun_obligation', generate_def_fun_obligation.
    intros.
    destruct (MergeSort.nodup String.leb String.eqb
                (map fst params)); try discriminate.
    destruct (Typing.btyp_to_typ te tret); try discriminate.
    simpl in *.
    destruct (MapList.mmap _ (Typing.btyp_to_typ te) params)eqn:PARAM; try discriminate.
    simpl in *.
    set (ge :=    (genv_has_property tabs STree.empty
                          (filter (fun '(k, _) => has_var k (vars_of_fun params e))
                             checked))) in *.
    destruct (stree_equal (vars_of_fun params e) ge) eqn:ALLKEY; try discriminate.
    inv H.
    eexists. split. eauto.
    intros.
    eapply eq_value_trans;eauto.
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
    unfold eval_fun.
    destruct t0.
    - simpl.
      apply map_err_nil in PARAM. subst.
      generalize (eq_genv_eval_expr te ge ge0 t e STree.empty STree.empty EQENV eq_env_all_empty).
      intro EEXPR.
      simpl. auto.
    - rewrite ext_equal_rew.
      eapply eval_fun_rec_eq.
      eapply eq_env_fst with (v1 := params).
      eapply map_err_fst;eauto.
      auto.
      apply eq_env_all_empty.
  Qed.

  Definition is_checked (x:Syntax.ident) (checked:list (propt tabs)) :=
    List.existsb (fun p => string_dec x (fst p)) checked.

  Definition generate_decl_const_obligation (te: Typing.tenv) (ge0 : genv tabs) (x:Syntax.ident) (bt:btyp) (prop:value tabs) : option Prop :=
    let* ty := Typing.btyp_to_typ te bt in
    let* v  := genv_get tabs ge0 x in
    let* v' := cast_value tabs v ty in
    ret (eq_value tabs prop  _ v').

  Definition generate_decl_fun_obligation (te: Typing.tenv) (ge0 : genv tabs) (x:Syntax.ident) (params : list (Syntax.param_attr * btyp))
    (tret : btyp) (prop:value tabs) : option Prop :=
    let* tparam := mmap (Typing.btyp_to_typ te) (map snd params) in
    let* tret' := Typing.btyp_to_typ te tret in
    let* v  := genv_get tabs ge0 x in
    let* v' := cast_value tabs v (TFun tparam tret') in
    ret (eq_value tabs prop  _ v').

  (* Definition tenv_update_opt (te: Typing.tenv) (x: Syntax.ident) (fields : smaplist typ) :=
  let id := StringIndexed.index x in
  match PTree.get id te.(tenv_defs) with
  | None => ret (PTree.set id fields te)
  | Some _ => fail
  end. *)

  (* Definition obligation_def_type (te: Typing.tenv) (x:Syntax.ident) (fields : SMapList.t btyp) : option Typing.tenv :=
  let* fields' := fields_btyp_to_typ te fields in
  tenv_update_opt te x fields'. *)

(*  Definition obligation_def_type (te: Typing.tenv) (x: ident) (td: Syntax.type_def field_descr) : option Typing.tenv :=
    eval_def_type te x td. *)

  Fixpoint generate_obligations (te:Typing.tenv) (ge0 : genv tabs)
    (checked : list (propt tabs)) (vc : list Prop) (p:list globdef) (props : list (propt tabs)) : option (list Prop) :=
    match p with
    | nil => match props with
             | nil => ret vc
             | _   => fail
             end
    | a :: prog' =>
        match a with
        | DefConst x l ty    =>
            let* (p,props') := get_prop tabs x props in
            let*  o  := generate_const_obligation tabs te x l ty p in
            generate_obligations te ge0 ((x,p)::checked) (o::vc) prog'  props'
        | DefFun y f =>
            let* (p,props') := get_prop tabs y props in
            let*  o   := generate_def_fun_obligation' y te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p in
            generate_obligations te ge0 ((y,p)::checked) (o::vc) prog'  props'
        | DeclConst y bt =>
            let* (p,props') := get_prop tabs y props in
            let* o := generate_decl_const_obligation te ge0  y bt p in
            generate_obligations te ge0 ((y,p)::checked) (o::vc) prog' props'
        | DeclFun y params tret =>
            let* (p,props') := get_prop tabs y props in
            let* o := generate_decl_fun_obligation te ge0 y params tret p in
            generate_obligations te ge0 ((y,p)::checked) (o::vc) prog' props'
        end
    end.


  Lemma get_prop_inv : forall s p props props',
      get_prop tabs s props = Some (p, props')  ->
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

  Definition wf_checked (props : list (propt tabs)) (prog:list globdef) :=
    forall s p, In (s,p) props -> In s (map ident_of_globdef prog) ->  False.

  Definition incr_genv (ge ge': genv tabs) (prog:list globdef) :=
    (forall x v, STree.get x ge = Some v -> STree.get x ge' = Some v)
    /\
      forall x,
        In x (map ident_of_globdef prog) ->
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

  Lemma has_property_set : forall x v p ge,
      same_value tabs v p ->
      has_property tabs (STree.set x v ge) (x, p).
  Proof.
    unfold has_property.
    intros.
    unfold genv_get.
    simpl. rewrite STree.gss. exists v.
    split. reflexivity.
    apply same_value_sym. assumption.
  Qed.

  Lemma generate_const_obligation_sound :
    forall te x l ty p (P:Prop) ge
           (GEN : generate_const_obligation tabs te x l ty p = Some P)
           (GET : genv_get tabs ge x = fail)
           (HOLD : P),
    exists ge',
      eval_def_const tabs te ge x l ty = Some ge' /\
        has_property tabs ge' (x,p).
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

  (** For each program declaration,
    if the proof obligation holds then the evaluation succeeds and
    the declaration has the property *)

  Lemma generate_def_fun_obligation_sound :
    forall te x f checked ge p o
           (GEN : generate_def_fun_obligation te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p = Some o)
           (GET : genv_get tabs ge x = fail)
           (ALL : Forall (has_property tabs ge) checked)
           (HAS : o)
    ,
    exists ge',
      eval_def_fun tabs te ge x f = Some ge' /\
        has_property tabs ge' (x,p).
  Proof.
    unfold generate_def_fun_obligation.
    unfold eval_def_fun. unfold Denot.eval_def_fun.
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
    unfold Syntax.ident, ident in *.
    destruct (@MapList.mmap string btyp typ (Typing.btyp_to_typ te) (fn_params f)); try discriminate.
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
      Forall (has_property tabs ge) checked   ->
      forall v, find_err string_dec x checked = Some v ->
                has_property tabs ge (x,v).
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
           (EVAL: eval_prog tabs ge0 prog = Some (te,ge))
           (FO : fo_typ t = true)
           (HASP : has_property tabs  ge  (s,Val tabs t v)),
    exists
      v' : eval_typ tabs t,
      (let* (_, ge0):= eval_prog tabs ge0 prog
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

  Lemma cast_value_typ_eq : forall v t e,
      cast_value tabs v t = Some e ->
      typeof_value tabs v = t.
  Proof.
    unfold cast_value. intros.
    destruct v. unfold cast_typ in H.
    destruct (typ_eq_dec t0 t); subst; try discriminate.
    inv H. reflexivity.
  Qed.

  Lemma cast_value_eq_value : forall v t e p ,
      cast_value tabs v t = Some e ->
      eq_value tabs p t e ->
      same_value tabs p v.
  Proof.
    unfold cast_value, eq_value, same_value.
    intros.
    destruct p,v.
    unfold cast_typ in H.
    destruct (typ_eq_dec t1 t); try discriminate.
    subst.
    simpl in H. inv H.
    destruct (typ_eq_dec t t0) ; try tauto.
  Qed.

  Lemma generate_decl_const_obligation_sound :
    forall te x bt  ge0 ge p P
           (GEN : generate_decl_const_obligation  te ge0 x bt p = Some P)
           (FAIL : genv_get tabs ge x = fail)
           (HOLD: P)
    ,
    exists ge',
      eval_decl_const tabs te ge0 ge x bt = Some ge' /\  has_property tabs ge' (x,p).
  Proof.
    unfold generate_decl_const_obligation.
    unfold eval_decl_const.
    intros.
    destruct (Typing.btyp_to_typ te bt); try discriminate.
    simpl in GEN. simpl.
    destruct (genv_get tabs ge0 x) eqn:FIND ; try discriminate.
    simpl in *.
    destruct (cast_value tabs v t) eqn:CAST; try discriminate.
    simpl in GEN. inv GEN.
    exploit cast_value_typ_eq; eauto.
    intro R; rewrite R.
    destruct (typ_eq_dec t t); try congruence.
    unfold genv_update. rewrite FAIL. simpl.
    eexists ; split. reflexivity. unfold has_property. simpl.
    eexists. split. unfold genv_get. rewrite STree.gsspec.
    destruct (STree.elt_eq x x); try congruence.
    reflexivity.
    eapply cast_value_eq_value;eauto.
  Qed.

  Lemma generate_decl_fun_obligation_sound :
    forall te x tparams tret ge0 ge P prop
           (GEN : generate_decl_fun_obligation  te ge0 x tparams tret prop = Some P)
           (FAIL : genv_get tabs ge x = fail)
           (HOLD: P)
    ,
    exists ge',
      eval_decl_fun tabs te ge0 ge x tparams tret = Some ge' /\  has_property tabs ge' (x,prop).
  Proof.
    unfold generate_decl_fun_obligation.
    unfold eval_decl_fun.
    intros.
    destruct (mmap (Typing.btyp_to_typ te) (map snd tparams)); try discriminate.
    destruct (Typing.btyp_to_typ te tret); try discriminate.
    simpl in GEN. unfold bind, Res.bind.
    destruct (genv_get tabs ge0 x); try discriminate.
    simpl in GEN.
    destruct (cast_value tabs v (TFun l t)) eqn:CAST ; try discriminate.
    simpl in GEN. inv GEN.
    exploit cast_value_typ_eq;eauto.
    intro R; rewrite R.
    destruct (typ_eq_dec (TFun l t) (TFun l t)) ; try congruence.
    eexists; split.
    {
      unfold genv_update.
      rewrite FAIL. simpl.
      reflexivity.
    }
    {
      apply has_property_set.
      apply same_value_sym.
      eapply cast_value_eq_value; eauto.
    }
  Qed.

(*  Definition has_def (g:globdef) :=
    match g with
    | DefConst _ _ _ | DefFun _ _ => true
    | _ => false
    end.
*)

  Definition wf_env (ge: genv tabs) (prog: list globdef) :=
    forall id,
      In id (List.map globdef_id prog) -> (*has_def d = true ->*) genv_get tabs ge id = fail.

  Lemma wf_env_empty : forall prog,
      wf_env  STree.empty prog.
  Proof.
    unfold wf_env.
    intros.
    unfold genv_get.
    rewrite STree.gempty.
    reflexivity.
  Qed.

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

  Lemma wf_env_set :
    forall ge d prog x v
      (DUP : NoDup (List.map globdef_id (d :: prog))),
      wf_env ge (d :: prog) ->
    globdef_id d = x ->
    wf_env (STree.set x v ge) prog.
  Proof.
    intros.
    subst.
    unfold wf_env in *.
    intros.
    simpl in DUP. inv DUP.
    rewrite genv_gsspec.
    destruct (string_dec (globdef_id d) id).
    - subst. tauto.
    - eapply H.
      simpl. tauto.
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
    eapply wf_env_set; eauto.
  Qed.

  Lemma wf_env_DeclConst :
    forall te ge0 ge ge' x ty prog
           (DUP : NoDup (map ident_of_globdef (DeclConst x  ty :: prog)))
           (WF : wf_env ge (DeclConst x ty :: prog))
           (EVAL : eval_decl_const tabs te ge0 ge x ty = Some ge'),
      wf_env ge' prog.
  Proof.
    unfold eval_decl_const.
    intros.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    simpl in EVAL.
    destruct (genv_get tabs ge0 x) eqn:GET; try discriminate.
    simpl in EVAL.
    destruct (typ_eq_dec t (typeof_value tabs v)) eqn:TYP;
      try discriminate.
    unfold genv_update in EVAL.
    destruct (genv_get tabs ge x) eqn:GET1; try discriminate.
    inv EVAL.
    eapply wf_env_set;eauto.
  Qed.

  Lemma wf_env_DeclFun :
    forall te ge0 ge ge' x targs ty prog
           (DUP : NoDup (map ident_of_globdef (DeclFun x targs ty :: prog)))
           (WF : wf_env ge (DeclFun x targs ty :: prog))
           (EVAL : eval_decl_fun tabs te ge0 ge x targs ty = Some ge'),
      wf_env ge' prog.
  Proof.
    unfold eval_decl_fun.
    intros.
    destruct (mmap (Typing.btyp_to_typ te) (map snd targs)); try discriminate.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    unfold bind, Res.bind in EVAL.
    destruct (genv_get tabs ge0 x) eqn:GET; try discriminate.
    destruct (typ_eq_dec (TFun l t) (typeof_value tabs v)) eqn:TYP;
      try discriminate.
    unfold genv_update in EVAL.
    destruct (genv_get tabs ge x) eqn:GET1; try discriminate.
    inv EVAL.
    eapply wf_env_set;eauto.
  Qed.

  Lemma wf_env_DefFun :
    forall te ge ge' x f prog
           (DUP : NoDup (map ident_of_globdef (DefFun x f :: prog)))
           (WF : wf_env ge (DefFun x f :: prog))
           (EVAL : eval_def_fun tabs te ge x f = Some ge'),
      wf_env ge' prog.
  Proof.
    unfold eval_def_fun. unfold Denot.eval_def_fun.
    intros.
    destruct (MapList.nodup Ident.eq_dec (Syntax.fn_params f)); try discriminate.
    destruct (Typing.btyp_to_typ te (Syntax.fn_return f)); try discriminate.
    simpl in EVAL.
    destruct (MapList.mmap _ (Typing.btyp_to_typ te) (Syntax.fn_params f)); try discriminate.
    simpl in EVAL.
    unfold genv_update in EVAL.
    destruct (genv_get tabs ge x) eqn:GET; try discriminate.
    inv EVAL.
    eapply wf_env_set;eauto.
  Qed.

  Lemma generate_obligations_incl :
    forall ge0 prog te checked props ol vc
           (GEN : generate_obligations te ge0 checked vc prog props = Some ol),
    forall x, In x vc -> In x ol.
  Proof.
    induction prog.
    - simpl. destruct props. intros.
      inv GEN. auto.
      discriminate.
    - simpl.
      destruct a; intros.
      +  destruct (get_prop tabs i props) eqn:GP; try discriminate.
         destruct p as (p,props').
         simpl in GEN.
         apply get_prop_inv in GP.
         subst.
         destruct (generate_const_obligation tabs te i l b p); try discriminate.
         simpl in GEN.
         eapply IHprog in GEN;eauto.
         simpl. tauto.
      + destruct (get_prop tabs i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        subst.
        destruct (generate_def_fun_obligation' i te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p);
          try discriminate.
        simpl in GEN.
        eapply IHprog in GEN;eauto.
        simpl. tauto.
      + destruct (get_prop tabs i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        subst.
        destruct (generate_decl_const_obligation te ge0 i b p); try discriminate.
        simpl in GEN.
        eapply IHprog in GEN;eauto.
        simpl. tauto.
      + destruct (get_prop tabs i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        subst.
        destruct (generate_decl_fun_obligation te ge0 i l b p); try discriminate.
        simpl in GEN.
        eapply IHprog in GEN;eauto.
        simpl. tauto.
  Qed.

(*  Lemma obligation_def_type_eq : forall te tid fields ,
      obligation_def_type te tid fields = eval_def_type te tid fields.
  Proof.
    reflexivity.
  Qed.
*)
  Lemma env_preserve_defs_has_property : forall ge ge' checked,
      Forall (has_property tabs ge) checked ->
      env_preserve_defs tabs ge ge' ->
      Forall (has_property tabs ge') checked.
  Proof.
    intros.
    rewrite Forall_forall in *.
    intros.
    apply H in H1.
    clear H.
    unfold has_property in *.
    destruct x as (id,v).
    simpl in H1. destruct v as (ty,vty).
    destruct H1 as (v' & GET & EQ).
    unfold genv_get in GET.
    destruct (STree.get id ge) eqn:GET1 ; try discriminate.
    inv GET. apply H0 in GET1.
    unfold genv_get.
    simpl. eexists ; split.
    unfold STree.get. rewrite GET1.
    reflexivity.
    destruct v'. unfold same_value in EQ.
    auto.
  Qed.

  Lemma generate_obligations_sound :
    forall prog te checked props ol vc ge0
           (ND : NoDup (map ident_of_globdef prog))
           (GEN : generate_obligations te ge0 checked vc prog props = Some ol)
           (OBL : Forall (fun p => p) ol)
    ,
    forall ge,
      wf_env ge prog ->
      Forall (has_property tabs ge) checked ->
      exists ge', eval_prog_rec tabs te ge0 ge prog = Some ge' /\
                        Forall (has_property tabs ge') props.
  Proof.
    unfold eval_prog_rec.
    unfold Denot.eval_prog_rec.
    induction prog.
    - simpl.
      intros. destruct props ; try discriminate.
      inv GEN.
      eexists. split. reflexivity.
      constructor.
    - simpl.
      destruct a.
      + intros.
        destruct (get_prop tabs i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        destruct (generate_const_obligation tabs te i l b p) eqn:CO; try discriminate.
        simpl in GEN.
        unfold eval_globdef at 1.
        destruct  (generate_const_obligation_sound te i l b p P ge  CO) as (ge' & EF & HP ).
        { unfold wf_env in H.
          eapply H. simpl. tauto.
        }
        {
          apply generate_obligations_incl with (x:= P) in GEN.
          rewrite Forall_forall in OBL.
          apply OBL;auto.
          simpl. tauto.
        }
        setoid_rewrite EF. simpl.
        apply IHprog with (ge0:=ge0)(ge:=ge') in GEN; auto.
        destruct GEN as (ge2 & EQ & ALL).
        eexists ; split. eauto.
        subst.
        constructor.
        apply eval_prog_rec_preserve_properties with (props := (i,p)::nil) in EQ.
        inv EQ ; auto.
        constructor ; auto.
        auto.
        inv ND ; auto.
        eapply wf_env_DefConst; eauto.
        constructor ;auto.
        apply eval_def_const_preserve_defs in EF.
        eapply env_preserve_defs_has_property; eauto.
      + intros.
        destruct (get_prop tabs i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        destruct (generate_def_fun_obligation' i te (Syntax.fn_params f) (Syntax.fn_return f) (Syntax.fn_body f) checked p) eqn:CO; try discriminate.
        simpl in GEN.
        apply generate_def_fun_obligation_impl in CO.
        destruct CO as (o & CO & IMPL).
        destruct  (generate_def_fun_obligation_sound te i f checked  ge p o CO) as (ge' & EF & HP ).
        { eapply H. simpl. tauto.
        }
        auto.
        { apply generate_obligations_incl with (x:=P) in GEN.
          rewrite Forall_forall in OBL. apply IMPL.  apply OBL;auto.
          simpl. tauto.
        }
        unfold eval_globdef at 1.
        unfold eval_def_fun in EF.
        setoid_rewrite EF. simpl.
        apply IHprog with (ge0 := ge0) (ge:=ge') in GEN; auto.
        destruct GEN as (ge2 & EQ & ALL).
        eexists ; split; eauto.
        subst.
        constructor.
        apply eval_prog_rec_preserve_properties with (props := (i,p)::nil) in EQ.
        inv EQ ; auto.
        constructor ; auto.
        auto.
        inv ND ; auto.
        eapply wf_env_DefFun; eauto.
        constructor ;auto.
        apply eval_def_fun_preserve_defs in EF.
        eapply env_preserve_defs_has_property; eauto.
      + intros.
        destruct (get_prop tabs i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        destruct (generate_decl_const_obligation te ge0 i b p) eqn:CO; try discriminate.
        simpl in GEN.
        unfold eval_globdef at 1.
        destruct  (generate_decl_const_obligation_sound _ _ _ _ ge  _ _  CO) as (ge' & EF & HP ).
        { unfold wf_env in H.
          eapply H; simpl. tauto.
        }
        {
          apply generate_obligations_incl with (x:= P) in GEN.
          rewrite Forall_forall in OBL.
          apply OBL;auto.
          simpl. tauto.
        }
        setoid_rewrite EF. simpl.
        apply IHprog with (ge0:=ge0)(ge:=ge') in GEN; auto.
        destruct GEN as (ge2 & EQ & ALL).
        eexists ; split; eauto.
        subst.
        constructor.
        apply eval_prog_rec_preserve_properties with (props := (i,p)::nil) in EQ.
        inv EQ ; auto.
        constructor ; auto.
        auto.
        inv ND ; auto.
        eapply wf_env_DeclConst; eauto.
        constructor ;auto.
        apply eval_decl_const_preserve_defs in EF.
        eapply env_preserve_defs_has_property; eauto.
      + intros.
        destruct (get_prop tabs i props) eqn:GP; try discriminate.
        destruct p as (p,props').
        simpl in GEN.
        apply get_prop_inv in GP.
        destruct (generate_decl_fun_obligation te ge0 i l b p) eqn:CO; try discriminate.
        simpl in GEN.
        unfold eval_globdef at 1.
        destruct  (generate_decl_fun_obligation_sound te i l b ge0 ge  P p  CO) as (ge' & EF & HP ).
        { unfold wf_env in H.
          eapply H; simpl. tauto.
        }
        {
          apply generate_obligations_incl with (x:= P) in GEN.
          rewrite Forall_forall in OBL.
          apply OBL;auto.
          simpl. tauto.
        }
        setoid_rewrite EF. simpl.
        apply IHprog with (ge0:=ge0)(ge:=ge') in GEN; auto.
        destruct GEN as (ge2 & EQ & ALL).
        eexists ; split; eauto.
        subst.
        constructor.
        apply eval_prog_rec_preserve_properties with (props := (i,p)::nil) in EQ.
        inv EQ ; auto.
        constructor ; auto.
        auto.
        inv ND ; auto.
        eapply wf_env_DeclFun; eauto.
        constructor ;auto.
        apply eval_decl_fun_preserve_defs in EF.
        eapply env_preserve_defs_has_property; eauto.
  Qed.

  Lemma eval_prog_has_property : forall te ge0 gds props prog
      (TE : Typing.tenv_of_type_defs (prog_types prog) = Some te)
      (DEFS : prog_defs prog = gds),
      (exists ge ,
      eval_prog_rec tabs te ge0 STree.empty gds = Some ge /\
      Forall (has_property tabs ge) props) ->
  exists (te : Typing.tenv) (ge : genv tabs),
    eval_prog tabs ge0 prog = Some (te, ge) /\
    Forall (has_property tabs ge) props.
  Proof.
    intros.
    destruct H as (ge & EVAL & ALL).
    unfold eval_prog.
    unfold Denot.eval_prog.
    rewrite TE.
    exists te, ge.
    split; auto.
    simpl.
    unfold eval_prog_rec in EVAL.
    rewrite DEFS. setoid_rewrite EVAL.
    reflexivity.
  Qed.

(*
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
 *)

  Inductive globdef_kind : Type :=
  | KindType (* Declaration of types *)
  | KindDef (* Definition *)
  | KindDecl (* Declaration *).

(*  Definition kind_of_globdef (gd:globdef) :=
    match gd with
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
*)

End S.
