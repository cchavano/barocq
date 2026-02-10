(* Extentional equality and compatibility *)
From Coq Require Import ZArith List MSetPositive Bool ZifyBool.
From compcert Require Import Coqlib Integers Maps.
From BarocqComp Require Import Barocq ExtOrdered.
From BarocqComp Require Import Denot Types Target Error Barray Brecord Benum Ident Maps2 Utils.
From Coq Require Import Datatypes List MSetPositive Lia.
From BarocqComp Require Import Typing.



(** [ext_equal t (v1 v2: #t)] defines extentional extentionnality of typed values.
    - For non-functional values, this is equality (=)
    - For first-order functions, this is extentional equality i.e if the arguments are equal the results are equal
    - This is generalised to higher-order functions
 *)
Section S.

    Variable tabs : Maps.PMap.t Type.

  Local Notation "# X" := (Types.eval_typ tabs X) (at level 90).

  Definition propt : Type := string * value tabs.

  Section EQUAL_FUN.
    Variable PRED : forall (t:typ), # t -> # t -> Prop.

    (** [ext_fun f1 f2] holds if the functions [f1] and [f2] are extentionnaly equal *)
    Fixpoint ext_fun (tret: typ) (targs : list typ)  {struct targs}:
      forall (f1 f2 : eval_funtyp (eval_typ tabs) targs (eval_typ tabs tret)), Prop:=
      match targs with
      | nil => fun f1 f2 => res_rel (PRED tret) (f1 tt) (f2 tt)
      | t :: l =>
      fun f1 f2 =>   forall v1 v2 : # t,
          PRED t v1 v2 ->
          match
            l as l0
            return
            ((forall (f1 f2: eval_funtyp (eval_typ tabs) l0 (# tret)), Prop) ->
             (forall f1 f2 : eval_funtyp (eval_typ tabs) (t::l0) (# tret), Prop))
          with
          | nil => fun _  (f3 f4 : # t -> res (# tret)) =>
                     res_rel (PRED tret) (f3 v1) (f4 v2)
          | t0 :: l0 => fun ext_fun f3 f4 => ext_fun (f3 v1) (f4 v2)
          end (ext_fun tret l) f1 f2
      end.

    Lemma ext_fun_rw : forall(tret: typ) (targs : list typ),
        forall (f1 f2 : eval_funtyp (eval_typ tabs) targs (eval_typ tabs tret)),
          (ext_fun tret targs f1 f2) =
            ((      match targs with
      | nil => fun f1 f2 => res_rel (PRED tret) (f1 tt) (f2 tt)
      | t :: l =>
      fun f1 f2 =>   forall v1 v2 : # t,
          PRED t v1 v2 ->
          match
            l as l0
            return
            ((forall (f1 f2: eval_funtyp (eval_typ tabs) l0 (# tret)), Prop) ->
             (forall f1 f2 : eval_funtyp (eval_typ tabs) (t::l0) (# tret), Prop))
          with
          | nil => fun _  (f3 f4 : # t -> res (# tret)) =>
                     res_rel (PRED tret) (f3 v1) (f4 v2)
          | t0 :: l0 => fun ext_fun f3 f4 => ext_fun (f3 v1) (f4 v2)
          end (ext_fun tret l) f1 f2
      end : eval_funtyp (eval_typ tabs) targs (eval_typ tabs tret) -> eval_funtyp (eval_typ tabs) targs (eval_typ tabs tret) -> Prop) f1 f2).
    Proof.
      destruct targs;auto.
    Qed.


  End EQUAL_FUN.

  Section EQUAL_RECORD.
    Variable PRED : forall (t:typ), # t -> # t -> Prop.

    Fixpoint equal_record (fields : list (ident * typ))  {struct fields} : forall (r1 r2: eval_recordtyp (eval_typ tabs) fields), Prop :=
      match fields with
      | nil => fun _ _ => True
      | (i,t) :: lt => fun r1 r2 => PRED t (proj_field (fst r1)) (proj_field (fst r2)) /\
                                      equal_record lt (snd r1) (snd r2)
      end.

    Lemma equal_record_rw : forall fd ty fields (v1 v2:field fd (# ty)) (r1 r2:eval_recordtyp (eval_typ tabs) fields) ,
        equal_record ((fd,ty)::fields) (v1,r1) (v2,r2) =
          (PRED ty (proj_field v1) (proj_field v2) /\
             equal_record fields r1 r2).
    Proof.
      intros.
      reflexivity.
    Qed.

  End EQUAL_RECORD.

  (** [ext_equal v1 v2] holds if the values are equal. For function types, it uses ext_fun (but not recursively) *)
  Fixpoint ext_equal (ty :typ) : forall (v1 v2 : # ty), Prop :=
    match ty as t0 return (# t0 -> # t0 -> Prop) with
    | TFun l t0 => fun (f1 f2: eval_funtyp (eval_typ tabs) l (eval_typ tabs t0)) => ext_fun ext_equal t0 l f1 f2
    | TArray t1 => fun (a1: array (# t1)) (a2:array (# t1)) =>
                     forall x, option_rel (ext_equal t1) (nth_error a1 x) (nth_error a2 x)
    | TRecord id fields => fun (r1 r2:eval_recordtyp (eval_typ tabs) fields) => equal_record ext_equal fields r1 r2
    | _ => eq
    end.

  Lemma ext_equal_rew : forall ty v1 v2,
      ext_equal ty v1 v2 = match ty as t0 return (# t0 -> # t0 -> Prop) with
    | TFun l t0 => fun (f1 f2: eval_funtyp (eval_typ tabs) l (eval_typ tabs t0)) => ext_fun ext_equal t0 l f1 f2
    | TArray t1 => fun (a1: array (# t1)) (a2:array (# t1)) =>
                     forall x, option_rel (ext_equal t1) (nth_error a1 x) (nth_error a2 x)
    | TRecord id fields => fun (r1 r2:eval_recordtyp (eval_typ tabs) fields) => equal_record ext_equal fields r1 r2
    | _ => eq
    end v1 v2.
  Proof.
    destruct ty;reflexivity.
  Qed.

    (** [ext_fun_fo f1 f2] holds if the functions [f1] and [f2] are extentionnaly equal *)
  Fixpoint ext_fun_fo (tret: typ) (targs : list typ)  {struct targs}: forall (f1 f2 : eval_funtyp (eval_typ tabs) targs (#tret)), Prop :=
      match targs with
      | nil => fun f1 f2 =>  (f1 tt) = (f2 tt)
      | t :: l =>
      fun f1 f2 =>   forall v,
          match
            l as l0
            return
            ((forall (f1 f2: eval_funtyp (eval_typ tabs) l0 (# tret)), Prop) ->
             (forall f1 f2 : eval_funtyp (eval_typ tabs) (t::l0) (# tret), Prop))
          with
          | nil => fun _  (f3 f4 : # t -> res (# tret)) =>
                     (f3 v) = (f4 v)
          | t0 :: l0 => fun ext_fun f3 f4 => ext_fun (f3 v) (f4 v)
          end (ext_fun_fo tret l) f1 f2
      end.


  (** [ext_equal_fo v1 v2]  encodes functional extensionality of functions (it is more restricted than ext_equal) *)
  Definition ext_equal_fo (ty:typ)  : eval_typ tabs ty -> eval_typ tabs ty -> Prop:=
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

  Fixpoint ext_equal_refl (t:typ): forall  v,
      fo_typ t = true ->
      ext_equal t v v.
  Proof.
    destruct t; try reflexivity.
    - (* array *)
      simpl.
      intros.
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

  Lemma res_rel_cast_typ_refl : forall ti tf v,
      fo_typ ti = true ->
      res_rel (ext_equal tf) (@cast_typ tabs ti v tf) (@cast_typ tabs ti v tf).
  Proof.
    intros.
    unfold cast_typ.
    destruct (typ_eq_dec ti tf).
    subst. constructor. apply ext_equal_refl. auto.
    constructor.
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

  Definition same_value (v1 v2 : value tabs) :=
    match v1 , v2 with
    | Val _ ty vty , Val _ t2 v2 =>
        match typ_eq_dec t2 ty with
        | left EQ => ext_equal  ty (typ_cast tabs EQ v2) vty
        | _   => False
        end
    end.

  Definition has_property (ge : genv tabs) (p : propt) :=
    exists v', genv_get tabs ge (fst p) = OK v' /\ same_value  (snd p) v'.

  Definition subset_property (ge:genv tabs) (l:list propt) :=
    forall x v', genv_get tabs ge x = OK v' -> exists v, In (x,v) l /\ same_value v v'.

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


  Lemma same_value_refl : forall x,
      fo_typ (typeof_value tabs x) = true ->
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
      fo_typ (typeof_value tabs x) = true ->
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

  Lemma ext_equal_ecast_typ : forall ti tf v1 v2,
      res_rel (ext_equal ti) v1 v2 ->
      res_rel (ext_equal  tf) (@ecast_typ tabs ti v1 tf) (@ecast_typ tabs ti v2 tf).
  Proof.
    intros.
    unfold ecast_typ.
    destruct (typ_eq_dec ti tf). subst.
    apply H.
    constructor.
  Qed.


  Lemma ext_equal_int_ops : forall op32s op32u op64s op64u t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf) (int_op_s tabs op32s op32u op64s op64u t1 t2 v1 v2 tf)
        (int_op_s tabs op32s op32u op64s op64u t1 t2 v1' v2' tf).
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

  Lemma ext_equal_cast_typ : forall ti tf v1 v2,
      ext_equal ti v1 v2 ->
      res_rel (ext_equal tf) (cast_typ tabs v1 tf) (cast_typ tabs v2 tf).
  Proof.
    unfold cast_typ.
    intros. destruct (typ_eq_dec ti tf); try constructor.
    subst.
    simpl. auto.
  Qed.

  Lemma get_cast_fo_typ : forall  ty t r,
      get_cast tabs ty t = OK r ->
      no_TFun ty = true /\ no_TFun t = true.
  Proof.
    unfold get_cast.
    destruct ty,t; try discriminate; simpl; split; reflexivity.
  Qed.


  Lemma ext_equal_eval_cast : forall ty x y t,
      ext_equal ty x y ->
      res_rel (ext_equal t) (eval_cast tabs ty x t) (eval_cast tabs ty y t).
  Proof.
    unfold eval_cast.
    intros.
    destruct (get_cast tabs ty t) eqn:C; try constructor.
    apply get_cast_fo_typ in C as (F1 & F2).
    simpl.
    apply no_TFun_equal in H; auto.
    subst.
    apply res_rel_refl. repeat intro. apply ext_equal_refl.
    apply no_TFun_fo_typ; auto.
  Qed.



  Lemma ext_equal_int_eq_neq : forall (b:bool) t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf)
        (int_eq_neq tabs b eqb Int.eq Int64.eq
           (fun (elems : list Syntax.ident) (v0 v3 : Benum.enum elems) =>
              if Benum.enum_eq_dec v0 v3 then true else false) t1 t2 v1 v2 tf)
        (int_eq_neq tabs b eqb Int.eq Int64.eq
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
      res_rel (ext_equal tf) (cmp_op tabs cmp32s cmp32u cmp64s cmp64u t1 t2 v1 v2 tf)
        (cmp_op tabs cmp32s cmp32u cmp64s cmp64u t1 t2 v1' v2' tf).
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

  Lemma ext_equal_bool_op : forall op t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf) (bool_op tabs op t1 t2 v1 v2 tf) (bool_op tabs op t1 t2 v1' v2' tf).
  Proof.
    unfold bool_op.
    destruct t1,t2; try constructor.
    intros. simpl in *. subst.
    apply ext_equal_cast_typ. reflexivity.
  Qed.

  Lemma ext_equal_int_op : forall op32 op64 t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf) (int_op tabs op32 op64 t1 t2 v1 v2 tf) (int_op tabs op32 op64 t1 t2 v1' v2' tf).
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

  Lemma ext_equal_eval_unary_op : forall op ti x y tf,
      ext_equal ti x y ->
      res_rel (ext_equal tf) (eval_unary_op tabs op ti x tf)
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


  Lemma ext_equal_eval_binary_op : forall op t1 t2 v1 v1' v2 v2' tf,
      ext_equal t1 v1 v1' ->
      ext_equal t2 v2 v2' ->
      res_rel (ext_equal tf) (eval_binary_op tabs op t1 t2 v1 v2 tf) (eval_binary_op tabs op t1 t2 v1' v2' tf).
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
        (eval_array_get arch tabs ta a1 ti i1 ty)
        (eval_array_get arch tabs ta a2 ti i2 ty).
  Proof.
    intros.
    unfold eval_array_get.
    destruct ta; try constructor.
    destruct arch.
    - destruct (typ_eq_dec ti (TInt32 Unsigned)); subst; try constructor.
      eapply ext_equal_ecast_typ.
      unfold Barray.get.
      simpl in H0. subst.
      rewrite ext_equal_valid_index with (a2:= a2).
      simpl in *.
      destruct (valid_index a2 (Intop.U64.of_u32 i2)).
      apply option_rel_res_rel; auto.
      constructor.
      repeat intro. auto.
    - destruct (typ_eq_dec ti (TInt64 Unsigned)); subst; try constructor.
      simpl in *.
      subst.
      eapply ext_equal_ecast_typ.
      unfold Barray.get.
      rewrite ext_equal_valid_index with (a2:= a2).
      destruct (valid_index a2  i2).
      apply option_rel_res_rel;auto.
      constructor.
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
        assert ((n <? length a)%nat = (S n <? S (length a))%nat).
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
      res_rel (ext_equal ty) (eval_array_set arch tabs ta a1 ti i1 tv v1 ty)
        (eval_array_set arch tabs ta a2 ti i2 tv v2 ty).
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
      same_value (Val tabs t y) (Val tabs t x).
  Proof.
    unfold same_value.
    intros. destruct (typ_eq_dec t t); try congruence.
    assert (e = eq_refl) by (apply Eqdep_dec.UIP_dec ; apply typ_eq_dec).
    subst. apply H.
  Qed.

  Lemma ext_equal_eval_record_proj : forall tr x y f ty,
      ext_equal tr x y ->
      res_rel (ext_equal ty) (eval_record_project tabs tr x f ty) (eval_record_project tabs tr y f ty).
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
      res_rel (equal_record ext_equal fields) (eval_record_upd_aux tabs fields r1 f ty v1)
        (eval_record_upd_aux tabs fields r2 f ty v2).
  Proof.
    unfold eval_recordtyp.
    intros.
    unfold eval_record_upd_aux.
    {
      revert r1 r2 H.
      induction fields.
      - simpl. constructor.
      - simpl.
        intros.
        destruct a as(fd,ty1).
        destruct r1 as (f1 & r1').
        destruct r2 as (f2 & r2').
        simpl in f1,f2.
        simpl.
        simpl in H.
        destruct (f =?fd)%string.
        destruct (typ_eq_dec  ty ty1).
        subst.
        constructor.
        subst.
        simpl; auto. tauto.
        constructor.
        destruct H as (FD & RST).
        specialize (IHfields r1' r2' RST).
        inv IHfields.
        constructor.
        simpl. constructor. simpl; auto.
    }
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

      destruct (typeof_field_typ_prf f fields ty); try constructor.
      revert r1 r2 H.
      induction fields.
      - simpl. auto.
      - simpl.
        intros.
        destruct a as(fd,ty1).
        destruct r1 as (f1 & r1').
        destruct r2 as (f2 & r2').
        simpl in f1,f2.
        simpl.
        simpl in H.
        revert e.
        simpl.
        destruct (f =?fd)%string.
        intro.
        simpl.
        split.
        destruct (typ_eq_dec  ty ty1).
        subst.
        assert (e = eq_refl).
        { apply Eqdep_dec.UIP_dec.
          decide equality.
          apply typ_eq_dec.
          repeat decide equality.
        }
        subst.
        simpl; auto.
        congruence.
        tauto.
        destruct H as (FD & RST).
        intros.
        specialize (IHfields e r1' r2' ).
        simpl.
        split; auto.
    }
  Qed.
*)

  Lemma ext_equal_eval_record_update : forall tr r1 r2 tv v1 v2 f ty,
      ext_equal tr r1 r2 ->
      ext_equal tv v1 v2 ->
      res_rel (ext_equal ty)
        (eval_record_update tabs tr r1 f tv v1 ty)
        (eval_record_update tabs tr r2 f tv v2 ty).
  Proof.
    intros.
    unfold eval_record_update.
    destruct tr; try constructor.
    simpl in H.
    eapply equal_upd_record_aux with (f:= f) in H; eauto.
    eapply ext_equal_ecast_typ;eauto.
  Qed.

  Lemma res_rel_ifthenelse : forall x y t1 t2 v1 v2  v1' v2' tr,
      ext_equal TBool x y ->
      res_rel (ext_equal t1) v1 v1' ->
      res_rel (ext_equal t2) v2 v2' ->
      res_rel (ext_equal tr)
        (eval_ifthenelse tabs x t1 v1 t2 v2 tr)
        (eval_ifthenelse tabs y t1 v1' t2 v2' tr).
  Proof.
    intros.
    unfold eval_ifthenelse.
    simpl in H. subst.
    destruct y.
    apply ext_equal_ecast_typ;auto.
    apply ext_equal_ecast_typ;auto.
  Qed.

  Lemma  ext_equal_eval_match : forall te x y tr l1 l2,
      ext_equal te x y ->
      Forall2 (fun x y => fst x = fst y /\ res_rel (ext_equal tr) (snd x) (snd y))  l1 l2 ->
      res_rel (ext_equal tr) (eval_match tabs te x tr l1) (eval_match tabs te y tr l2).
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

  Lemma res_rel_ecast_typ_refl : forall ti tf v,
      fo_typ ti = true ->
      res_rel (ext_equal tf) (@ecast_typ tabs ti v tf) (@ecast_typ tabs ti v tf).
  Proof.
    intros.
    unfold ecast_typ.
    destruct (typ_eq_dec ti tf).
    subst. simpl.
    destruct v.
    constructor. apply ext_equal_refl; auto.
    constructor. constructor.
  Qed.

  Lemma same_value_cast_value : forall x y ty,
      same_value x y ->
      res_rel (ext_equal ty) (cast_value tabs x ty) (cast_value tabs y ty).
  Proof.
    unfold same_value. destruct x,y.
    intros. destruct (typ_eq_dec t0 t); try discriminate.
    subst. unfold cast_value.
    change (cast eq_refl v0) with v0 in H.
    unfold cast_typ.
    destruct (typ_eq_dec t ty); try constructor.
    subst.
    simpl. apply ext_equal_sym. auto.
    tauto.
  Qed.

  Lemma ext_equal_eval_app_res :
    let Ftyp := fun ty : typ => res (# ty) in
    let Pred := fun ty : typ => res_rel (ext_equal ty) in
    forall l0 t x y x0 y0 ty,
      ext_equal (TFun l0 t) x y ->
      DList.Forall2 Ftyp Pred l0 x0 y0 ->
      res_rel (ext_equal ty) (eval_app_res tabs l0 t x x0 ty)
        (eval_app_res tabs l0 t y y0 ty).
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

  Definition val_of_value (v: value tabs) : # (typeof_value tabs v) :=
    match v with
    | Val _ _ v => v
    end.

  Definition eq_value (vl: value tabs) (t:typ) (v: #t) :=
    same_value  vl (Val _ t v).


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

  Lemma same_value_cast_typ_M : forall x y t,
      same_value x y ->
      res_rel (ext_equal t) (cast_typ_M tabs t x) (cast_typ_M tabs t y).
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


  Lemma eq_value_same_value : forall p t v,
      eq_value p t v ->
      same_value p (Val tabs t v).
  Proof.
    unfold eq_value,same_value.
    intros.
    destruct p; auto.
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


  Section EXPR.
    Variable EXPR : Type.

    Variable eval_expr : tenv -> (genv tabs) -> (lenv tabs) -> (forall (ty: typ) (e: EXPR), res (# ty)).

    Lemma eval_prog_rec_preserve_properties : forall arch te ge prog  ge' props
                                                   (ALL : Forall (has_property ge) props),
        eval_prog_rec tabs eval_expr arch  te ge prog = OK ge' ->
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

  Lemma eval_prog_rec_preserve_app_properties : forall arch  p2  te  ge' ge'' p1' p2',
      Forall (has_property ge') p1' ->
      eval_prog_rec tabs eval_expr arch  te ge' p2 = OK ge'' ->
      Forall (has_property ge'') p2' ->
      Forall (has_property ge'') (p1' ++ p2').
  Proof.
    intros.
    rewrite Forall_app.
    split.
    eapply eval_prog_rec_preserve_properties; eauto.
    auto.
  Qed.

  End EXPR.

  Fixpoint genv_has_property (ge: genv tabs)  (l:list propt) :=
    match l with
    | nil => ge
    | (k,p)::l' => genv_has_property (STree.set k p ge) l'
    end.

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


  Definition check_value (v: res (value tabs)) (ty:typ) (prop : value tabs) :=
    match v with
    | OK v' => match cast_value tabs v' ty with
               | OK v' => eq_value prop ty v'
               |  _    => False
               end
    | _    => False
    end.


  Definition generate_const_obligation (te : Typing.tenv) (x:ident) (l:Syntax.literal) (ty:btyp)
    (prop : value tabs) : res Prop :=
    let* ty' := Typing.btyp_to_typ te ty in
    eret (check_value (eval_literal tabs te l) ty' prop).


  Definition get_prop (s:ident) (props : list propt) :=
    match props with
    | nil => fail
    | (s',p)::props' => if String.eqb s s' then
                          eret (p,props')
                        else fail
    end.


End S.
