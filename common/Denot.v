Set Universe Polymorphism.
From Stdlib Require Import String Bool List Eqdep.
From compcert Require Import Coqlib Maps Integers.
From BarocqComp Require Import DList Res Option Utils Types Syntax Barray Benum Brecord Maps2 Typing Intop.
From BarocqComp Require DList.
Import ListNotations.

Local Open Scope option_monad_scope.
Local Open Scope error_monad_scope.



Section DENOT.

  (* Abstract type implementation environment *)
  Variable tabs : PMap.t Type.

  Notation eval_typ := (Types.eval_typ tabs).

  Inductive value : Type :=
    | Val (t: typ) (v: eval_typ t) : value.

  Definition genv := STree.t value.

  Definition lenv := STree.t value.

  Definition genv_get (ge: genv) (x: ident) : option value :=
    STree.get x ge.

  Definition genv_update (ge: genv) (x: ident) (v: value) : option genv :=
    match genv_get ge x with
    | Some _ => None
    | None => Some (STree.set x v ge)
    end.

  Definition lenv_get (le: lenv) (x: ident) : option value :=
    STree.get x le.

  Definition lenv_update (le: lenv) (x: ident) (v: value) : lenv :=
    STree.set x v le.


  Definition get_env (ge:genv) (le:lenv) (x:ident) : option value :=
    match STree.get x le with
    | None => STree.get x ge
    | Some v => Some v
    end.

  Definition match_env (ge1:genv) (le1:lenv) (ge2:genv) (le2:lenv) :=
    forall x, less_def (get_env ge1 le1 x) (get_env ge2 le2 x).


  Definition same_env (s: ident -> Prop) (ge1:genv) (le1:lenv) (ge2:genv) (le2:lenv) :=
    forall x, s x -> get_env ge1 le1 x = get_env ge2 le2 x.


  Definition match_lenv (le1 le2: lenv) : Prop :=
    forall x, less_def (lenv_get le1 x) (lenv_get le2 x).

  Lemma keys_lenv_update : forall le k v,
      STree.keys (lenv_update  le k v) = SSet.add k (STree.keys le).
  Proof.
    unfold STree.keys, lenv_update.
    unfold STree.map1, STree.set.  intros.
    rewrite PTree.map1_set.
    reflexivity.
  Qed.


  Lemma match_lenv_refl:
    forall (le: lenv), match_lenv le le.
  Proof.
    intros. unfold match_lenv. constructor.
  Qed.

  Lemma match_lenv_update1:
    forall (le: lenv) k v,
    lenv_get  le k = None ->
    match_lenv le (lenv_update  le k v).
  Proof.
    unfold match_lenv; intros.
    destruct (Ident.eq_dec x k).
    - subst. rewrite H. constructor.
    - unfold lenv_update. unfold lenv_get in *.
      rewrite STree.gso; auto. constructor.
  Qed.

  Lemma match_lenv_update2:
    forall (le1 le2: lenv) (k: string) v,
      match_lenv le1 le2 ->
      match_lenv (lenv_update le1 k v) (lenv_update le2 k v).
  Proof.
    unfold match_lenv, lenv_get, lenv_update; intros.
    destruct (Ident.eq_dec x k).
    - subst. rewrite STree.gss. rewrite STree.gss. constructor.
    - rewrite! STree.gso in * by auto. auto.
  Qed.

  Lemma match_lenv_trans:
    forall (le1 le2 le3: lenv),
      match_lenv le1 le2 ->
      match_lenv le2 le3 ->
      match_lenv le1 le3.
  Proof.
    unfold match_lenv; intros.
    eapply less_def_trans;eauto.
  Qed.

  (* Defines whether environment e2 shadows some variables of environment e1 *)
  Definition env_noshadow {A B} (e1: STree.t A) (e2: STree.t B) : Prop :=
    forall x v,
      STree.get x e1 = Some v ->
      STree.get x e2 = None.

  Lemma env_noshadow_set:
    forall (A B: Type) (e1: STree.t A) (e2: STree.t B) x,
      env_noshadow e1 e2 ->
      STree.get x e1 = None ->
      (forall b, env_noshadow e1 (STree.set x b e2)).
  Proof.
    unfold env_noshadow. intros.
    specialize (H _ _ H1).
    destruct (string_dec x0 x).
    - subst. congruence.
    - rewrite STree.gso; tauto.
  Qed.

  Lemma match_lenv_match_env : forall ge le1 le2,
      env_noshadow ge le2 ->
      match_lenv le1 le2 ->
      match_env ge le1 ge le2.
  Proof.
    unfold env_noshadow,match_lenv,match_env.
    intros.
    unfold get_env.
    specialize (H0 x).
    unfold lenv_get in H0. inv H0.
    destruct (STree.get x ge) eqn:GET.
    apply H in GET. rewrite GET. constructor.
    constructor.
    rewrite H3.
    constructor.
  Qed.

  Lemma match_env_refl : forall ge1 le1,
      match_env ge1 le1 ge1 le1.
  Proof.
    unfold match_env.
    intros.
    constructor.
  Qed.

  Lemma match_env_trans : forall ge1 le1 ge2 le2 ge3 le3,
      match_env ge1 le1 ge2 le2 -> match_env ge2 le2 ge3 le3 ->
      match_env ge1 le1 ge3 le3.
  Proof.
    unfold match_env.
    intros.
    eapply less_def_trans; eauto.
  Qed.

  Lemma match_env_update : forall ge1 le1 ge2 le2 x v,
      match_env ge1 le1 ge2 le2 ->
      match_env ge1 (lenv_update le1 x v) ge2 (lenv_update le2 x v).
  Proof.
    unfold match_env.
    intros.
    unfold get_env, lenv_update.
    rewrite! STree.gsspec.
    destruct (STree.elt_eq x0 x). constructor.
    apply H.
  Qed.

  Definition match_on (P: ident -> bool) (ge1:genv) (le1:lenv) (ge2:genv) (le2:lenv) :=
    forall x, P x = true -> option_rel eq (get_env ge1 le1 x) (get_env ge2 le2 x).

  Lemma match_on_eq : forall P Q ge1 ge2 le1 le2,
    (forall x, P x = Q x) ->
    match_on P ge1 le1 ge2 le2 <-> match_on Q ge1 le1 ge2 le2.
  Proof.
    unfold match_on. intros.
    split; intros.
    - apply H0; auto.
      rewrite H; auto.
    - apply H0; auto.
      rewrite <- H; auto.
  Qed.

  Lemma match_on_union : forall P Q ge1 ge2 le1 le2,
      match_on (BSet.union P Q) ge1 le1 ge2 le2 <->
        (match_on P ge1 le1 ge2 le2 /\ match_on Q ge1 le1 ge2 le2).
  Proof.
    unfold match_on. intros.
    split ; intros.
    - split ; intros.
      + apply H. unfold BSet.union. rewrite orb_true_iff. tauto.
      + apply H. unfold BSet.union. rewrite orb_true_iff. tauto.
    - unfold BSet.union in H0.
      destruct H.
      rewrite orb_true_iff in H0.
      destruct H0; auto.
  Qed.

  Lemma match_on_bset_union : forall P Q ge1 ge2 le1 le2,
      match_on (SSet.bset (SSet.union P Q)) ge1 le1 ge2 le2 <->
        (match_on (SSet.bset P) ge1 le1 ge2 le2 /\ match_on (SSet.bset Q) ge1 le1 ge2 le2).
  Proof.
    intros.
    rewrite <- match_on_union.
    apply match_on_eq.
    intros.
    apply SSet.bset_union.
  Qed.

  Lemma match_on_trans : forall ge1 le1 P1 ge2 le2 P2 ge3 le3,
      match_on P1 ge1 le1 ge2 le2 ->
      match_on P2 ge2 le2 ge3 le3 ->
      match_on (BSet.inter P1 P2) ge1 le1 ge3 le3.
  Proof.
    unfold match_on.
    intros.
    eapply option_rel_trans.
    { repeat intro; congruence. }
    apply H.
    unfold BSet.inter in *. rewrite andb_true_iff in H1.
    tauto.
    apply H0.
    unfold BSet.inter in *. rewrite andb_true_iff in H1.
    tauto.
  Qed.

  


  Definition nat_of_val {ty:typ} : forall (v: eval_typ ty), option nat :=
    match ty with
    | TInt32 Signed => fun v => Some (I32.to_nat v)
    | TInt32 Unsigned => fun v => Some (U32.to_nat v)
    | TInt64 Signed => fun v => Some (I64.to_nat v)
    | TInt64 Unsigned => fun v => Some (U64.to_nat v)
    |  _       => fun v => None
    end.


  Definition cast_typ  {t2:typ} (v: eval_typ t2) (t1:typ): option (eval_typ t1) :=
    match typ_eq_dec t2 t1 with
    | left EQ => Some (cast (f_equal eval_typ EQ) v)
    | _       => None
    end.

  Remark cast_typ_id:
    forall t x,
    @cast_typ t x t = Some x.
  Proof.
    intros. unfold cast_typ. 
    destruct (typ_eq_dec t t); try contradiction.
    assert (e = eq_refl). apply UIP_refl.
    rewrite H. reflexivity.
  Qed.

  Lemma cast_typ_ok_imp_typ_eq:
    forall t2 t1 v v',
    @cast_typ t2 v t1 = Some v' ->
    t1 = t2.
  Proof.
    unfold cast_typ; intros.
    destruct (typ_eq_dec t2 t1); try discriminate.
    inv H. reflexivity.
  Qed.

  Definition ecast_typ  {t2:typ} (v: option (eval_typ t2)) (t1:typ): option (eval_typ t1) :=
    match typ_eq_dec t2 t1 with
    | left EQ => cast (f_equal option (f_equal eval_typ EQ)) v
    | _       => None
    end.

  Lemma ecast_typ_id: 
    forall t v,
    @ecast_typ t v t = v.
  Proof.
    intros. unfold ecast_typ.
    destruct (typ_eq_dec t t); try contradiction.
    assert (e = eq_refl). apply UIP_refl.
    rewrite H; reflexivity.
  Qed.

  Lemma ecast_typ_ok_imp_typ_eq:
    forall t2 t1 v v',
    @ecast_typ t2 v t1 = Some v' ->
    t2 = t1.
  Proof.
    unfold ecast_typ; intros.
    destruct (typ_eq_dec t2 t1); try tauto.
    destruct v; discriminate.
  Qed.
  
  Definition cast_value  (v:value) (t1:typ) : option (eval_typ t1).
  Proof.
    destruct v.
    apply (cast_typ v t1).
  Defined.

  Definition lenv_of_record (lt : @MapList.t string typ) (r : eval_recordtyp eval_typ lt) (le:lenv) : lenv:=
    grecord_fold_left  (fun x bt e acc => lenv_update  acc x (Val  _ e)) lt r le.

  Fixpoint record_of_lenv (ge:genv) (lt : @MapList.t string typ) (le:lenv) : option (eval_recordtyp eval_typ lt) :=
    match lt as l return (option (grecord eval_typ l)) with
    | [] => Some tt : option (grecord eval_typ [])
    | p :: l =>
        let* v := get_env ge le (fst p) in
        let* vti := cast_value v (snd p) in
        let* r := record_of_lenv ge l le in
        Some (Field (fst p) vti, r)
    end.


  Definition lenv_of_val (ty:typ) : forall (v: eval_typ ty) (le:lenv), option lenv :=
    match ty with
    | TRecord _ l => fun v le => Some (lenv_of_record l v le)
    | _           => fun _ _ => None
    end.

  Definition eval_var  (ge: genv) (le: lenv) (x: ident) (ty:typ) : option (eval_typ ty) :=
    let* v := get_env ge le x in
    cast_value  v ty.

  Lemma eval_var_lenv_update : forall ge le x ty v,
    eval_var  ge (lenv_update  le x (Val  ty v)) x ty = Some v.
  Proof.
    unfold eval_var,lenv_update.
    intros. unfold get_env.
    rewrite STree.gss. simpl.
    apply cast_typ_id.
  Qed.






  Definition eval_constr (te: tenv) (x: ident) (ty:typ) : option (eval_typ ty) :=
    match ty with
    | TEnum eid elems => Benum.make_enum elems x
    | _ => fail
    end.

  Definition partial {A B: Type} (F : A -> B) : A -> option B :=
    fun x => Some (F x).

  Definition partial2 {A B C: Type} (F : A -> B -> C) : A -> B -> option C :=
    fun x y => Some (F x y).

  Definition get_cast (ty:typ) (ty':typ) : option (eval_typ ty -> option (eval_typ ty')) :=
    match ty, ty' with
      (* TBool *)
    | TBool , TBool => Some (fun x => Some x)
    | TBool , TInt32 s => Some (partial (if s then I32.of_bool else U32.of_bool))
    | TBool , TInt64 s => Some (partial (if s then I64.of_bool else U64.of_bool))
    | TBool , TEnum eid elems => Some (fun x => Benum.of_bool elems x)
       (* TInt32 *)
    | TInt32 s , TBool =>  Some (partial (if s then I32.to_bool else U32.to_bool))
    | TInt32 s , TInt32 s' => Some (partial (match s , s' with
                                              | Signed , Unsigned => U32.of_i32
                                              | Unsigned , Signed => I32.of_u32
                                              |  _       ,   _    => fun x => x
                                              end))
    | TInt32 s , TInt64 s' => Some (partial (match s, s' with
                                              | Signed, Signed => I64.of_i32
                                              | Signed, Unsigned => U64.of_i32
                                              | Unsigned, Signed => I64.of_u32
                                              | Unsigned, Unsigned => U64.of_u32
                                              end))
    | TInt32 s ,  TEnum eid elems => Some (fun x => Benum.of_Z elems (if s then I32.to_Z x else U32.to_Z x))
                 (*  Tint64 *)
    | TInt64 s , TBool => Some (partial (if s then I64.to_bool else U64.to_bool))
    | TInt64 s , TInt32 s' => Some (partial (
                                      match s, s' with
                                      | Signed, Signed =>  I32.of_i64
                                      | Signed, Unsigned => U32.of_i64
                                      | Unsigned, Signed => I32.of_u64
                                      | Unsigned, Unsigned => U32.of_u64
                                      end))
    | TInt64 s ,  TInt64 s' => Some (partial (
                                       match s, s' with
                                       | Signed, Unsigned => U64.of_i64
                                       | Unsigned, Signed => I64.of_u64
                                       | _, _ => fun x => x
                                       end))
    | TInt64 s , TEnum eid elems => Some (fun x => Benum.of_Z elems (if s then I64.to_Z x else U64.to_Z x))
            (* Tenum *)
    | TEnum tid elems , TBool  => Some (partial (fun x => Benum.to_bool x))
    | TEnum tid elems , TInt32 s => Some (partial (fun x => (if s then I32.of_Z else U32.of_Z) (Benum.to_Z x)))
    | TEnum tid elems , TInt64 s => Some (partial (fun x => (if s then I64.of_Z else U64.of_Z) (Benum.to_Z x)))
    | _ , _ => fail
    end.

  (* Definition get_cast_operator (ty:typ) (ty':typ) : option cast_operator :=
    match ty, ty' with
      (* TBool *)
    | TBool , TBool => Some Cid
    | TBool , TInt32 s => Some (if s then I32_of_bool else U32_of_bool)
    | TBool , TInt64 s => Some (if s then I64_of_bool else U64_of_bool)
    | TBool , TEnum eid elems => Some (Benum_of_i32_I32_of_bool elems)
       (* TInt32 *)
    | TInt32 s , TBool =>  Some (if s then I32_to_bool else U32_to_bool)
    | TInt32 s , TInt32 s' => Some (match s , s' with
                                  | Signed , Unsigned => U32_of_i32
                                  | Unsigned , Signed => I32_of_u32
                                  |  _       ,   _    => Cid
                                  end)
    | TInt32 s , TInt64 s' => Some (match s, s' with
                                  | Signed, Signed => I64_of_i32
                                  | Signed, Unsigned => U64_of_i32
                                  | Unsigned, Signed => I64_of_u32
                                  | Unsigned, Unsigned => U64_of_u32
                                  end)
    | TInt32 s ,  TEnum eid elems => Some (
                                         if s then Benum_of_i32_I32_of_u32 elems
                                         else Benum_of_i32 elems )
    (*  Tint64 *)
    | TInt64 s , TBool => Some (if s then I64_to_bool else U64_to_bool)
    | TInt64 s , TInt32 s' => Some (
                                  match s, s' with
                                  | Signed, Signed =>  I32_of_i64
                                  | Signed, Unsigned => U32_of_i64
                                  | Unsigned, Signed => I32_of_u64
                                  | Unsigned, Unsigned => U32_of_u64
                                  end)
    | TInt64 s ,  TInt64 s' => Some (
                                   match s, s' with
                                   | Signed, Unsigned => U64_of_i64
                                   | Unsigned, Signed => I64_of_u64
                                   | _, _ => Cid
                                   end)
    | TInt64 s , TEnum eid elems => Some (if s then  Benum_of_i32_I32_of_i64 elems
                                        else Benum_of_i32_I32_of_u64 elems)
            (* Tenum *)
    | TEnum tid elems , TBool  => Some (I32_to_bool_Benum_to_i32 elems )
    | TEnum tid elems , TInt32 s => Some (if s then Benum_to_i32  else U32_of_i32_Benum_to_i32)
    | TEnum tid elems , TInt64 s => Some (if s then I64_of_i32_Benum_to_i32
                                        else  U64_of_i32_Benum_to_i32 )
    | _ , _ => fail
    end. *)

  Definition eval_cast (ty:typ) (v1:eval_typ ty) (tr:typ) : option(eval_typ tr) :=
    let* f := get_cast ty tr in f  v1.

  Definition eval_unary_op (op: unary_op) (ty:typ) : forall (v: eval_typ ty) (tyr : typ), option(eval_typ tyr):=
    match op, ty with
    | UopNotbool, TBool    => (fun v tyr => @cast_typ TBool (negb v) tyr)
    | UopNotint,  TInt32 s => (fun v tyr => @cast_typ (TInt32 s) (Int.not v) tyr)
    | UopNeg,  TInt32 s    => (fun v tyr => @cast_typ (TInt32 s) (Int.neg v) tyr)
    | UopPlus, TInt32 s    => (fun v tyr => @cast_typ (TInt32 s) v tyr)
    | UopNotint, TInt64 s  => (fun v tyr => @cast_typ (TInt64 s) (Int64.not v) tyr)
    | UopNeg, TInt64 s     => (fun v tyr => @cast_typ (TInt64 s) (Int64.neg v) tyr)
    | UopPlus, TInt64 s    => (fun v tyr => cast_typ  v tyr)
    | _, _ => (fun _ _ => fail)
    end.

  Definition bool_bool_bool (t1 t2:typ) :=
    match t1 , t2 with
    | TBool , TBool => Some TBool
    |   _   ,   _    => fail
    end.

  Definition int_int_int (t1 t2:typ) :=
    match t1,t2 with
    | TInt32 Signed , TInt32 Signed => Some (TInt32 Signed)
    | TInt32 Unsigned , TInt32 Unsigned => Some (TInt32 Unsigned)
    | TInt64 Signed , TInt64 Signed   => Some (TInt64 Signed)
    | TInt64 Unsigned , TInt64 Unsigned   => Some (TInt64 Unsigned)
    |  _ , _ => fail
    end.

  Definition int_int_bool (t1 t2:typ) :=
    match t1,t2 with
    | TInt32 Signed , TInt32 Signed => Some TBool
    | TInt32 Unsigned , TInt32 Unsigned => Some TBool
    | TInt64 Signed , TInt64 Signed   => Some TBool
    | TInt64 Unsigned , TInt64 Unsigned   => Some TBool
    |  _ , _ => fail
    end.

  Definition eq_neq_bool (t1 t2:typ) :=
    match t1,t2 with
    | TBool , TBool => Some TBool
    | TInt32 Signed , TInt32 Signed => Some TBool
    | TInt32 Unsigned , TInt32 Unsigned => Some TBool
    | TInt64 Signed , TInt64 Signed   => Some TBool
    | TInt64 Unsigned , TInt64 Unsigned   => Some TBool
    | TEnum _ _ , TEnum _ _ => if typ_eq_dec t1 t2 then Some TBool else fail
    |  _ , _ => fail
    end.



  Definition typof_binary_op (op:binary_op)  :=
    match op with
    | BopAndbool => bool_bool_bool
    | BopOrbool => bool_bool_bool
    | BopXorbool => bool_bool_bool
    | BopAdd => int_int_int
    | BopSub => int_int_int
    | BopMul => int_int_int
    | BopDiv => int_int_int
    | BopMod => int_int_int
    | BopAndint => int_int_int
    | BopOrint => int_int_int
    | BopXorint => int_int_int
    | BopShl => int_int_int
    | BopShr => int_int_int
    | BopEq => eq_neq_bool
    | BopNeq => eq_neq_bool
    | BopLt => int_int_bool
    | BopGt => int_int_bool
    | BopLe => int_int_bool
    | BopGe => int_int_bool
    end.

  Definition bool_op (F : bool -> bool -> bool) (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),option(eval_typ tyr) :=
    match t1, t2 with
    | TBool , TBool => (fun v1 v2 tyr => @cast_typ TBool (F v1 v2) tyr)
    | _, _ =>   (fun _ _ _ => fail)
    end.


  Definition int_op (F32 : int -> int -> int) (F64 : int64 -> int64 -> int64)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),option(eval_typ tyr) :=
    match t1, t2 with
    | TInt32 s , TInt32 s' => if signedness_eq_dec s s' then
                                (fun v1 v2 tyr => @cast_typ (TInt32 s) (F32 v1 v2) tyr)
                              else (fun _ _ _ => fail)
    | TInt64 s , TInt64 s' => if signedness_eq_dec s s' then
                                (fun v1 v2 tyr => @cast_typ (TInt64 s) (F64 v1 v2) tyr)
                              else (fun _ _ _ => fail)
    | _, _ =>   (fun _ _ _ => fail)
    end.


  Definition int_op_s (F32s : int -> int -> option int) (F32u : int -> int -> option int)
    (F64s : int64 -> int64 -> option int64) (F64u : int64 -> int64 -> option int64)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),option(eval_typ tyr) :=
    match t1, t2 with
    | TInt32 s , TInt32 s'  =>
        match s , s' with
        | Signed , Signed => (fun v1 v2 tyr => @ecast_typ (TInt32 Signed) (F32s v1 v2) tyr)
        | Unsigned , Unsigned => (fun v1 v2 tyr => @ecast_typ (TInt32 Unsigned) (F32u v1 v2) tyr)
        | _   , _ => (fun _ _ _ => fail)
        end
    | TInt64 s , TInt64 s'  =>
        match s , s' with
        | Signed , Signed => (fun v1 v2 tyr => @ecast_typ (TInt64 Signed) (F64s v1 v2) tyr)
        | Unsigned , Unsigned => (fun v1 v2 tyr => @ecast_typ (TInt64 Unsigned) (F64u v1 v2) tyr)
        | _   , _ => (fun _ _ _ => fail)
        end
    | _, _ =>   (fun _ _ _ => fail)
    end.

  Definition int_eq_neq (equal:bool) (Fbool : bool -> bool -> bool)
    (F32 : int -> int -> bool) (F64 : int64 -> int64 -> bool) (Fenum : forall (elems : list ident), enum elems -> enum elems -> bool)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),option(eval_typ tyr) :=
    let map b := if equal then b else negb b in
    match t1, t2 with
    | TBool , TBool => (fun v1 v2 tyr => @cast_typ TBool (map (eqb v1 v2)) tyr)
    | TInt32 s , TInt32 s'  => (fun v1 v2 tyr => if signedness_eq_dec s s' then @cast_typ TBool (map (F32 v1 v2)) tyr else fail)
    | TInt64 s , TInt64 s'  => (fun v1 v2 tyr => if signedness_eq_dec s s' then @cast_typ TBool (map (F64 v1 v2)) tyr else fail)
    | ((TEnum n1 elems1) as t1) , ((TEnum n2 elems2) as t2) =>
        (fun v1 v2 tyr =>
           match typ_eq_dec t1 t2 with
           | left Eqt => @cast_typ TBool (map (Fenum elems2  (typ_cast tabs Eqt v1) v2)) tyr
           |  _       => fail
           end
        )
    | _, _ =>   (fun _ _ _ => fail)
    end.

  Definition cmp_op (cmp32s : int -> int -> bool) (cmp32u:int -> int -> bool) (cmp64s : int64 -> int64 -> bool) (cmp64u : int64 -> int64 -> bool)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),option(eval_typ tyr) :=
    match t1, t2 with
    | TInt32 s , TInt32 s'  =>
        match s , s' with
        | Signed , Signed => (fun v1 v2 tyr => @cast_typ TBool (cmp32s v1 v2) tyr)
        | Unsigned , Unsigned => (fun v1 v2 tyr => @cast_typ TBool (cmp32u v1 v2) tyr)
        |  _   , _ => (fun _ _ _ => fail)
        end
    | TInt64 s , TInt64 s' =>
        match s , s' with
        | Signed , Signed => (fun v1 v2 tyr => @cast_typ TBool (cmp64s v1 v2) tyr)
        | Unsigned , Unsigned => (fun v1 v2 tyr => @cast_typ TBool (cmp64u v1 v2) tyr)
        |  _   , _ => (fun _ _ _ => fail)
        end
    |  _ ,  _ => (fun _ _ _ => fail)
    end.

  Definition eval_binary_op (op: binary_op) : forall (t1:typ) (t2: typ)  (v1: eval_typ t1)  (v2: eval_typ t2) (tyr : typ), option(eval_typ tyr) :=
    match op with
    | BopAndbool => bool_op andb
    | BopOrbool  => bool_op orb
    | BopXorbool => bool_op xorb
    | BopAdd => int_op Int.add Int64.add
    | BopSub => int_op Int.sub Int64.sub
    | BopMul => int_op Int.mul Int64.mul
    | BopDiv => int_op_s I32.div U32.div I64.div U64.div
    | BopMod => int_op_s I32.mod U32.mod I64.mod U64.mod
    | BopAndint => int_op Int.and Int64.and
    | BopOrint => int_op Int.or Int64.or
    | BopXorint => int_op Int.xor Int64.xor
    | BopShl => int_op Int.shl Int64.shl
    | BopShr => int_op_s (partial2 Int.shr) (partial2 Int.shru) (partial2 Int64.shr)  (partial2 Int64.shru)
    | BopEq => int_eq_neq true eqb Int.eq Int64.eq  (fun elems v1 v2 =>
                                                  if enum_eq_dec v1 v2 then true else false)
    | BopNeq => int_eq_neq false eqb Int.eq Int64.eq  (fun elems v1 v2 =>
                                                  if enum_eq_dec v1 v2 then true else false)
    | BopLt => cmp_op Int.lt Int.ltu Int64.lt Int64.ltu
    | BopGt => cmp_op (Int.cmp Cgt) (Int.cmpu Cgt) (Int64.cmp Cgt) (Int64.cmpu Cgt)
    | BopLe => cmp_op (Int.cmp Cle) (Int.cmpu Cle) (Int64.cmp Cle) (Int64.cmpu Cle)
    | BopGe => cmp_op (Int.cmp Cge) (Int.cmpu Cge) (Int64.cmp Cge) (Int64.cmpu Cge)
    end.

  Fixpoint eval_array_lit (a: array value) : option value :=
    match a with
    | nil => fail
    | Val tx x :: nil => ret (Val (TArray tx) (x :: nil))
    | Val tx x :: a' =>
        let* va := eval_array_lit a' in
        match va with
        | Val (TArray ta) xa =>
            match (typ_eq_dec tx ta) with
            | left eq =>
                ret (Val (TArray ta) ((typ_cast tabs eq x) :: xa))
            | _ => fail
            end
        | _ => fail
        end
    end.

  Fixpoint eval_record_lit_rec (lv: smaplist value) (fields: smaplist typ) : option(eval_recordtyp eval_typ fields).
    destruct lv as [|[x [tv v]] lv'] eqn:Elv; destruct fields as [| [y t] fields'] eqn:Efields.
    - apply (ret tt).
    - apply fail.
    - apply fail.
    - destruct (Ident.eq_dec x y).
      + subst. destruct (typ_eq_dec tv t).
        * subst. destruct (eval_record_lit_rec lv' fields') as [rc |].
          -- unfold eval_recordtyp in *. simpl in *.
             apply (ret (Field y v, rc)).
          -- apply fail.
        * apply fail.
      + apply fail.
  Defined.

  Definition eval_record_lit (n: ident) (lv: smaplist value) (fields: smaplist typ) : option value.
    destruct lv as [|x lv'].
    - apply fail.
    - destruct (eval_record_lit_rec (x :: lv') fields) as [r |].
      * apply (ret (Val (TRecord (Some n) fields) r)).
      * apply fail.
  Defined.

  Definition cast_index {ti: typ} (i: eval_typ ti) : option usize :=
    match ti as t return (eval_typ t -> option usize) with
    | TInt32 Unsigned => (fun i => ret (USIZE.of_u32 i))
    | TInt64 Unsigned => (fun i => ret (USIZE.of_u64 i))
    | _ => (fun _ => fail)
    end i.

  Definition eval_array_get (ta:typ) (a: eval_typ ta) (t2:typ) (i: eval_typ t2) (tyr:typ): option (eval_typ tyr) :=
    match ta as t return (eval_typ t -> option (eval_typ tyr)) with
    | TArray t =>
      (fun  (a0 : array (eval_typ t)) =>
        let* i := cast_index i in
        ecast_typ (Barray.get a0 i) tyr)
    | _ => fun _ => fail
    end a.

  Definition eval_array_set (ta: typ) (a : eval_typ ta) (t2:typ)
      (i : eval_typ t2) (tv:typ) (v: eval_typ tv) (tyr : typ): option (eval_typ tyr) :=
    (match ta as t return (eval_typ t -> option (eval_typ tyr)) with
    | TArray t =>
        (fun (t0: typ) (a0: eval_typ (TArray t0)) =>
          let* i := cast_index i in
          let* v := cast_typ v t0 in
          @ecast_typ (TArray t0) (Barray.set a0 i v) tyr) t
    | _ => (fun _ => fail)
    end) a.

  Fixpoint exists_typeof_field (F: typ -> Type) (k:key) (fields : smaplist typ) :
    forall (GP : good_proj k  fields = true),
      { ty| gtypeof_field F k  fields GP = F ty}.
  Proof.
    destruct fields;simpl.
    - intros. discriminate.
    - destruct p.
      simpl.
      intros.
      destruct ((k=?s)%string).
      exists t. reflexivity.
      apply exists_typeof_field.
  Defined.

  Definition cast_typof_field (k:key) (fields :smaplist typ):
    forall (GP :good_proj k  fields = true),
    gtypeof_field eval_typ k  fields GP ->
    value.
  Proof.
    intros.
    destruct (exists_typeof_field eval_typ _ _ GP) as (ty & EQ).
    apply (Val ty (cast EQ X)).
  Defined.

  Definition eval_record_project_aux (fields: smaplist typ) (rc: eval_recordtyp eval_typ fields) (k: ident) (ty:typ) : option(eval_typ ty).
    simpl in rc.
    unfold eval_recordtyp in rc.
    destruct (Bool.bool_dec (good_proj k fields) true) as [GP| BP].
    - specialize (gproject eval_typ rc k GP).
      intro.
      destruct (exists_typeof_field eval_typ _ _ GP) as (ty1 & EQ).
      apply (cast EQ) in X.
      exact (cast_typ X ty).
    - exact fail.
  Defined.

(*  Definition eval_record_project_aux (fields: smaplist typ) (rc: eval_recordtyp eval_typ fields) (k: ident) (ty:typ) : option(eval_typ ty).
    simpl in rc.
    unfold eval_recordtyp in rc.
    destruct (good_proj k fields) eqn:GP.
    - specialize (gproject eval_typ rc k GP).
      intro.
      destruct (exists_typeof_field eval_typ _ _ GP) as (ty1 & EQ).
      apply (cast EQ) in X.
      exact (cast_typ X ty).
    - exact fail.
  Defined.
    *)


  Definition eval_record_project (ty:typ) : forall (v: eval_typ ty) (k: ident) (tyr : typ), option(eval_typ tyr) :=
    match ty with
    | TRecord _ fields => fun v k tyr => eval_record_project_aux fields v k tyr
    | _ => fun _ _ _ => fail
    end.


  Definition typeof_value  (v : value ) :=
    match v with
    | Val t _ => t
    end.

  Definition typof_field_dec (k:ident) (fields: smaplist typ) : option{t : typ| typof_field k fields = Some t}.
  Proof.
    destruct (typof_field k fields) as [t |] eqn:Etyp.
    apply Some. exists t. reflexivity.
    apply fail.
  Defined.

Ltac change_good_proj :=
  match goal with
  | |- context[good_proj ?K ((?S,?V)::?L)] =>
      change (good_proj K ((S,V)::L)) with ((K=?S)%string || good_proj K L)
  end.

Fixpoint good_proj_map  (A B: Type) (F : A -> B) (k:key) (fields:smaplist A):
    good_proj k fields = good_proj k (MapList.map F fields).
Proof.
  destruct fields.
  - simpl. reflexivity.
  - destruct p; simpl.
    repeat change_good_proj.
    destruct (k =? s)%string.
    reflexivity.
    apply good_proj_map.
Defined.

Definition good_proj_map_app     {A B: Type} (F : A -> B) {k:key} {fields :smaplist A}:
  forall (GP : good_proj k fields = true), good_proj k (MapList.map F fields) = true.
Proof.
  intros.
  rewrite <- GP.
  symmetry. apply good_proj_map.
Defined.

Fixpoint typeof_field_typ (k:key) (fields : smaplist typ) (GK: good_proj k fields = true) :
  { ty : typ | find_type_of_field k fields = Some ty}.
Proof.
  destruct fields.
  - exfalso. apply (good_proj_nil GK).
  - destruct p.
    simpl.
    revert GK.
    simpl.
    repeat change_good_proj.
    destruct (k=? s)%string.
    + intro.
      exists t;reflexivity.
    + simpl.
      intros.
      apply (typeof_field_typ k fields GK).
Defined.

Fixpoint no_TFun (t:typ) :=
  match t with
  | TFun _ _ => false
  | TArray t => no_TFun t
  | TRecord _ l => List.forallb (fun x => no_TFun (snd x)) l
  | _  => true
  end.

Definition fo_typ (t:typ) :=
  match t with
  | TFun l r => List.forallb no_TFun l && no_TFun r
  | TArray t => no_TFun t
  | TRecord _ l => List.forallb (fun x => no_TFun (snd x)) l
  |   _         => true
  end.

Definition cast_etyp {k:key} {fields : smaplist typ} {tv: typ} (v:  eval_typ tv)
  (EQ : find_type_of_field k fields = Some tv):
  gtype_of_field eval_typ k fields.
Proof.
  unfold gtype_of_field.
  rewrite EQ. apply  v.
Defined.

Definition eval_record_upd_aux  (fields: smaplist typ) (rc: eval_recordtyp eval_typ fields) (k: ident) (tv: typ) (v: eval_typ tv) :
  option(eval_recordtyp eval_typ fields) :=
  dyn_upd eval_typ typ_eq_dec rc k tv v.

  Definition eval_record_update (t1:typ) : forall (v1: eval_typ t1) (k: ident) (tv : typ) (v: eval_typ tv) (tyr:typ), option(eval_typ tyr) :=
    match t1 with
    | TRecord n fields => fun st k tv v tyr =>
                            @ecast_typ (TRecord n fields) (eval_record_upd_aux fields st k tv v) tyr
    | _ => fun _ _ _ _ _ => fail
    end.

  Definition typof_record_project (ty:typ) (f:ident): option typ :=
    match ty with
    | TRecord _ l => find_err key_eq f l
    |    _      => fail
    end.

  Definition typof_array (ty:typ) : option typ :=
    match ty with
    | TArray e => Some e
    |    _      => fail
    end.


  Definition eval_ifthenelse (c:bool) (t2: typ) (v2:option(eval_typ t2)) (t3: typ)  (v3: option(eval_typ t3)) (tr:typ) : option(eval_typ tr) :=
    if c then ecast_typ v2 tr else ecast_typ v3 tr.

  Definition eval_match {A:Type} (tv:typ) (v: eval_typ tv)  (cases: list (pattern * (option A))) : option A :=
    (match tv as t0 return (eval_typ t0 -> option A) with
    | TEnum _ elems => 
        (fun v0 => ematch_with v0 cases)
    | _ => (fun _ => fail)
    end) v.


  Fixpoint eval_app (tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams (eval_typ tret)) (args: DList.dlist eval_typ tparams) (ty: typ):
    option(eval_typ ty).
  Proof.
    destruct args.
    - simpl in f. apply (ecast_typ (f tt) ty).
    - simpl in f.
      destruct l.
      + apply (ecast_typ (f e) ty).
      + apply (eval_app _ _ (f e) args ty).
  Defined.

  (* Fixpoint eval_app_typ (tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams (eval_typ tret)) (args: DList.dlist eval_typ tparams) (ty:typ):
    option(eval_typ ty).
  Proof.
    destruct args.
    - simpl in f. apply (ecast_typ (f tt) ty).
    - simpl in f.
      destruct l.
      +  apply (ecast_typ (f e) ty).
      + apply (eval_app_typ _ _ (f e) args ty).
  Defined. *)

  Fixpoint eval_app_option(tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams (eval_typ tret))
    (args: DList.dlist (fun (ty:typ) => option(eval_typ ty)) tparams) (ty:typ):
    option(eval_typ ty).
  Proof.
    destruct args.
    - simpl in f. apply (ecast_typ (f tt) ty).
    - simpl in f.
      destruct l.
      + apply (let* e' := e in ecast_typ (f e') ty).
      + eapply bind. apply e.
      apply (fun x => eval_app_option _ _ (f x) args ty).
  Defined.

  Lemma eval_app_res_eval_app : forall {B:Type} (F : forall (ty:typ), B -> option (eval_typ  ty)) lt l args,
      DList.map2 (eval_typ ) F l lt = Some args ->
      forall tret f ty v,
      eval_app_option lt tret f args ty = Some v ->
      exists vargs,
        DList.mmap (eval_typ ) F l lt = Some vargs /\ eval_app  lt tret f vargs ty = Some v.
  Proof.
    induction lt.
    - destruct l; try discriminate.
      simpl;intros. inv H.
      simpl in H0. eexists.
      split. reflexivity.
      simpl. auto.
    - intros.
      cbn in f.
      destruct l; try discriminate.
      simpl in H.
      destruct (DList.map2 eval_typ F l lt) eqn:MAP2 ;
        try discriminate.
      simpl in H.
      inv H.
      specialize (IHlt l d MAP2 tret).
      simpl in H0.
      destruct lt.
      + destruct l; try discriminate.
        destruct (F a b) eqn:Fab; try discriminate.
        simpl in H0.
        eexists. split;simpl.
        rewrite Fab.
        reflexivity.
        simpl. auto.
      + destruct (F a b) eqn:Fab; try discriminate.
        simpl in H0.
        specialize (IHlt (f e) ty v H0).
        destruct IHlt as (vargs' & MAP & EVAL).
        eexists.
        split.
        cbn. rewrite Fab. simpl. rewrite MAP.
        reflexivity.
        cbn.
        auto.
  Qed.

  Section EVAL.

    Context {T : Type}.

    Variable eval : tenv -> genv -> lenv -> (forall (ty: typ) (e: T), option(eval_typ ty)).


  Fixpoint eval_act_record (te:tenv) (ge:genv) (l:list (string * T)) (fields : list (string * typ)) (le:lenv) : option (eval_recordtyp eval_typ fields):=
      match l with
      | nil => match fields with
               | nil => Some tt
               | _   => None
               end
      | (x1,e1)::l' => match fields with
                       | nil => None
                       | (x1',t1)::fields' =>
                           if string_dec x1 x1'
                           then
                             let* v1 := eval te ge le t1 e1 in
                             let* r  := eval_act_record te ge l' fields' le in
                             Some (Field x1' v1 , r)
                           else None
                       end
      end.

  End EVAL.




  Fixpoint eval_atom (te: tenv) (ge: genv) (le: lenv) (ty: typ) (a: atom) : option (eval_typ ty) :=
    match a with
    | ATrue  => @cast_typ TBool true ty
    | AFalse => @cast_typ TBool false ty
    | AInt32 i s => @cast_typ (TInt32 s) i ty
    | AInt64 i s => @cast_typ (TInt64 s) i ty
    | AConstr x _ _ => eval_constr te x ty
    | AVar x _ => eval_var ge le x ty
    | ACast a1 tr =>
        let* tr' := btyp_to_typ te tr in
        let* ta1  := typof_atom te a1 in
        let* v1 := eval_atom te ge le ta1 a1 in
        ecast_typ (eval_cast ta1 v1 tr') ty
    | AUnaryOp op a1 _ =>
        let* ta1 := typof_atom te a1 in
        let* v := eval_atom te ge le ta1 a1 in
        eval_unary_op op ta1 v ty
    | ABinaryOp op a1 a2 _ =>
        let* ta1 := typof_atom te a1 in
        let* ta2  := typof_atom te a2 in
        let* v1 := eval_atom te ge le ta1 a1  in
        let* v2 := eval_atom te ge le ta2 a2  in
        eval_binary_op op ta1 ta2 v1 v2 ty
    | AArrayGet a1 a2 _ _ =>
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* v1 := eval_atom te ge le ta1 a1  in
        let* v2 := eval_atom te ge le ta2 a2  in
        eval_array_get ta1 v1 ta2 v2 ty
    | ARecordProj a1 k _ _ =>
        let* ta1 := typof_atom te a1 in
        let* v := eval_atom te ge le ta1 a1 in
        eval_record_project ta1 v k ty
    | APureCall f btf args _ =>
        let* tf := btyp_to_typ te btf in
        match tf with
        | TFun tparams tret =>
            let* f := eval_var ge le f (TFun tparams tret) in
            let* vargs := DList.map2 _ (eval_atom te ge le) args tparams in
            eval_app_option tparams tret f vargs ty
              (* let* vargs := DList.mmap _ (eval_atom te ge le) args tparams in
            eval_app tparams tret f vargs ty *)
        |  _  => fail
        end
    end.

  Definition eval_comp (te: tenv) (ge: genv) (le: lenv) (ty: typ) (c: comp) : option (eval_typ ty) :=
    match c with
    | CpAtom a => eval_atom te ge le ty a
    | CpArraySet a1 a2 a3 bt =>
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* ta3 := typof_atom te a3 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        let* v3 := eval_atom te ge le ta3 a3 in
        eval_array_set ta1 v1 ta2 v2 ta3 v3 ty
    | CpRecordUpdate a1 k a2 bt =>
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        eval_record_update ta1 v1 k ta2 v2 ty
    | CpCall f btf args btr =>
        let* tf := btyp_to_typ te btf in
        match tf with
        | TFun tparams tret =>
            let* f := eval_var ge le f (TFun tparams tret) in
            let* vargs := DList.map2 _ (eval_atom te ge le) args tparams in
            eval_app_option tparams tret f vargs ty
            (*let* vargs := DList.mmap _ (eval_atom te ge le) args tparams in
            eval_app tparams tret f vargs ty *)
        |  _  => fail
        end
    end.

  Definition comp_has_var (c:comp) :=
    match c with
    | CpAtom a => AtomOrdered.has_var a
    | CpArraySet a1 a2 a3 bt =>
        BSet.union (AtomOrdered.has_var a1)
          (BSet.union (AtomOrdered.has_var a2)
          (AtomOrdered.has_var a3))
    | CpRecordUpdate a1 k a2 bt =>
        BSet.union (AtomOrdered.has_var a1)
          (AtomOrdered.has_var a2)
    | CpCall f btf args btr =>
        BSet.union (BSet.singleton  String.string_dec f)
                   (BSet.union_list AtomOrdered.has_var args)
    end.



  Lemma less_def_eval_var :
    forall ge1 (le1 : lenv) ge2 (le2 : STree.t value) (ty : typ) (x:ident)
           (MATCH: match_env  ge1 le1 ge2 le2),
      less_def (eval_var  ge1 le1 x ty) (eval_var  ge2 le2 x ty).
  Proof.
    unfold eval_var.
    intros.
    apply less_def_bind_less_def.
    apply MATCH. intros.
    apply less_def_refl.
  Qed.

  Lemma less_def_eval_app_option :
    forall lt f ty ty' a1 a2,
           (DList.forall2
              (fun (ty : typ) (v1 v2 : option (eval_typ ty)) =>
                 less_def v1 v2)
              lt a1 a2) ->
  less_def (eval_app_option  lt f ty a1 ty')
    (eval_app_option  lt f ty a2 ty').
  Proof.
    induction lt.
    - intros.
      simpl in H.
      rewrite DList.dlist_nil with (x:= a1).
      rewrite DList.dlist_nil with (x:= a2).
      simpl. constructor.
    - intros.
      simpl in H.
      destruct H as (H1 & H2).
      rewrite DList.car_cdr with (dl := a1).
      rewrite DList.car_cdr with (dl := a2).
      simpl. destruct lt.
      + apply less_def_bind_less_def; auto.
        intro. constructor.
      + apply less_def_bind_less_def; auto.
  Qed.

  Lemma less_def_eval_app_option_args :
    forall
      (less_def_eval_atom :
        forall (ge1 : genv) (ge2: genv) (te : tenv) (a : atom)
               (le1 : lenv) (le2 : STree.t value) (ty : typ),
          match_env  ge1 le1 ge2 le2 ->
          less_def (eval_atom te ge1 le1 ty a) (eval_atom te ge2 le2 ty a))
      (ge1 ge2 : genv) (te : tenv)
      (le1 le2 : lenv)
      (MATCH : match_env  ge1 le1 ge2 le2)
      (ty : typ)
      (lt : list typ)
      (ty ty': typ)
      (f : eval_funtyp eval_typ lt (eval_typ ty))
      l,
      less_def
      (let* vargs := DList.map2 eval_typ (eval_atom te ge1 le1) l lt
     in eval_app_option  lt ty f vargs ty')
    (let* vargs := DList.map2 eval_typ (eval_atom te ge2 le2) l lt
     in eval_app_option  lt ty f vargs ty').
  Proof.
    intros.
    assert (
        option_rel (fun l1 l2 => DList.forall2
                                   (fun ty (v1:option (eval_typ ty))
                                        (v2:option (eval_typ ty)) =>
                                      less_def v1 v2) lt l1 l2)
          (DList.map2 eval_typ (eval_atom te ge1 le1) l lt)
          (DList.map2 eval_typ (eval_atom te ge2 le2) l lt)).
    clear f.
    revert lt.
    { induction l; simpl.
      - destruct lt. constructor.
        constructor. constructor.
      - destruct lt; try constructor.
        eapply option_rel_bind_rel.
        apply IHl.
        intros.
        simpl.
        constructor.
        split; auto.
        unfold DList.car.
        unfold DList.inj_list_hd. simpl.
        unfold DList.cast. simpl.
        apply less_def_eval_atom; auto.
    }
    inv H.
    + simpl. constructor.
    + simpl.
      apply less_def_eval_app_option; auto.
  Defined.



  Fixpoint less_def_eval_atom (ge1 ge2:genv) (te:tenv) (a:atom):
    forall le1 le2 ty
           (MATCH : match_env  ge1 le1 ge2 le2),
      less_def (eval_atom te ge1 le1 ty a) (eval_atom te ge2 le2 ty a).
  Proof.
    destruct a; simpl; try constructor.
    - intros. eapply less_def_eval_var; eauto.
    - intros. apply less_def_bind_eq.
      intros. apply less_def_bind_eq.
      intros.
      apply less_def_bind_less_def.
      auto.
      intros. constructor.
    - intros. apply less_def_bind_eq.
      intros. apply less_def_bind_less_def.
      auto.
      intros. constructor.
    - intros. apply less_def_bind_eq.
      intros. apply less_def_bind_eq.
      intros. apply less_def_bind_less_def.
      auto.
      intros. apply less_def_bind_less_def.
      auto.
      intros ; constructor.
    - intros. apply less_def_bind_eq.
      intros. apply less_def_bind_eq.
      intros. apply less_def_bind_less_def.
      auto.
      intros. apply less_def_bind_less_def.
      auto.
      intros ; constructor.
    - intros. apply less_def_bind_eq.
      intros. apply less_def_bind_less_def.
      auto.
      intros ; constructor.
    - intros.
      apply less_def_bind_eq.
      intros. destruct x; try constructor.
      intros. apply less_def_bind_less_def.
      apply less_def_eval_var with (ty:= TFun l0 x); auto.
      intros.
      apply less_def_eval_app_option_args; auto.
  Qed.

  Fixpoint eval_atom_match_on (ge1 ge2:genv) (te:tenv) (a:atom):
    forall le1 le2 ty
           (MATCH : match_on (AtomOrdered.has_var a)  ge1 le1 ge2 le2),
      option_rel eq (eval_atom te ge1 le1 ty a) (eval_atom te ge2 le2 ty a).
  Proof.
    destruct a; intros; simpl; try (apply option_rel_refl; auto; fail).
    - unfold eval_var.
      eapply option_rel_bind_rel.
      apply MATCH. simpl.  auto with bset.
      intros. subst. apply option_rel_refl;auto.
    - repeat (intros; apply option_rel_bind_equal).
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; auto.
      intros. subst. apply option_rel_refl;auto.
    - repeat (intros; apply option_rel_bind_equal).
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; auto.
      intros. subst. apply option_rel_refl;auto.
    - repeat (intros; apply option_rel_bind_equal).
      apply match_on_union in MATCH.
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; auto.
      tauto.
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; auto. tauto.
      intros. subst.
      apply option_rel_refl;auto.
    - repeat (intros; apply option_rel_bind_equal).
      apply match_on_union in MATCH.
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; auto.
      tauto.
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; auto. tauto.
      intros. subst.
      apply option_rel_refl;auto.
    - repeat (intros; apply option_rel_bind_equal).
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; auto.
      intros. subst.
      apply option_rel_refl;auto.
    - intros; apply option_rel_bind_equal.
      intros. destruct a; try constructor.
      apply match_on_union in MATCH as (M1 & M2).
      eapply option_rel_bind_rel.
      unfold eval_var. eapply option_rel_bind_rel.
      apply M1. auto with bset.
      intros. subst.
      apply option_rel_refl. apply RelationClasses.eq_Reflexive.
      intros.
      eapply option_rel_bind_rel with (RA:=eq).
      { clear - eval_atom_match_on M2.
        revert l0.
        induction l; destruct l0; simpl; try constructor.
        - reflexivity.
        -
          simpl in M2. apply match_on_union in M2.
          eapply option_rel_bind_rel.
          apply IHl; auto.
          tauto.
          intros; subst.
          constructor.
          f_equal.
          apply option_rel_eq_eq.
          apply eval_atom_match_on; tauto.
      }
      intros; subst.
      apply option_rel_refl; auto.
  Qed.

  Lemma eval_comp_match_on (ge1 ge2:genv) (te:tenv) (c:comp):
    forall le1 le2 ty
           (MATCH : match_on  (comp_has_var c)  ge1 le1 ge2 le2),
      option_rel eq (eval_comp te ge1 le1 ty c) (eval_comp te ge2 le2 ty c).
  Proof.
    destruct c; try (intros; simpl; apply option_rel_refl; auto; fail).
    - intros.
      apply eval_atom_match_on; auto.
    - repeat (intros; apply option_rel_bind_equal).
      simpl in MATCH.
      rewrite! match_on_union in MATCH.
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; tauto.
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; tauto.
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; tauto.
      intros ; subst. apply option_rel_refl;auto.
    - repeat (intros; apply option_rel_bind_equal).
      simpl in MATCH.
      rewrite! match_on_union in MATCH.
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; tauto.
      intros. eapply option_rel_bind_rel.
      apply eval_atom_match_on; tauto.
      intros. subst. apply option_rel_refl;auto.
    - repeat (intros; apply option_rel_bind_equal).
      unfold comp_has_var in MATCH.
      rewrite! match_on_union in MATCH.
      intros. destruct a; try constructor.
      destruct MATCH as (M1 & M2).
      eapply option_rel_bind_rel.
      unfold eval_var. eapply option_rel_bind_rel.
      apply M1. auto with bset.
      intros. subst.
      apply option_rel_refl. apply RelationClasses.eq_Reflexive.
      intros.
      eapply option_rel_bind_rel with (RA:=eq).
      { clear -  M2.
        revert l0.
        induction l; destruct l0; simpl; try constructor.
        - reflexivity.
        -
          simpl in M2. apply match_on_union in M2.
          eapply option_rel_bind_rel.
          apply IHl; auto.
          tauto.
          intros; subst.
          constructor.
          f_equal.
          apply option_rel_eq_eq.
          apply eval_atom_match_on; tauto.
      }
      intros; subst.
      apply option_rel_refl; auto.
  Qed.


  Definition cast_int (t:typ) (i:int) : option(eval_typ t) :=
    match t with
    | TInt32 s => Some i
    |  _       => fail
    end.

  Definition cast_int64 (t:typ) (i:int64) : option(eval_typ t) :=
    match t with
    | TInt64 s => Some i
    |  _       => fail
    end.

  Fixpoint eval_literal (te: tenv) (l: literal) : option value :=
    match l with
    | LTrue => ret (Val TBool true)
    | LFalse => ret (Val TBool false)
    | LInt32 i s => ret (Val (TInt32 s) i)
    | LInt64 i s => ret (Val (TInt64 s) i)
    | LArray a _ _ =>
        let* av := mmap (eval_literal te) a in
        eval_array_lit av
    | LRecord rc _ rid =>
        let* rcv := MapList.mmap _ (eval_literal te) rc in
        let* fields := TEnv.get_rdef te rid in
        eval_record_lit rid rcv fields
    end.

  Definition cast_typ_M (tret:typ) (v: value) : option (eval_typ tret) :=
    match v with
      | Val tv v =>
          match typ_eq_dec tv tret with
          | left e =>  (ret (typ_cast tabs e v))
          |  _     => fail
          end
    end.

  Definition eval_def_const (te: tenv) (ge: genv) (x: ident) (l: literal) (ty: btyp) : option genv :=
    let* ty' := btyp_to_typ te ty in
    let* vv := eval_literal te l in
    let* v'  := cast_value vv ty' in
    genv_update ge x (Val ty' v').

  Section PRESERVE_ENV.

    Definition env_preserve_defs (ge1 ge2: genv) :=
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
      genv_update ge k v = Some ge' ->
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

  Lemma eval_def_const_preserve_defs : forall te ge ge' x l ty,
      eval_def_const te ge x l ty = Some ge' ->
      env_preserve_defs ge ge'.
  Proof.
    unfold eval_def_const.
    intros.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    destruct (eval_literal te l); try discriminate.
    simpl in H.
    destruct (cast_value v t); try discriminate.
    simpl in H.
    eapply genv_update_preserve_defs;eauto.
  Qed.

  Definition eval_decl_const (te: tenv) (impl ge: genv) (x:ident) (bt:btyp) : option genv :=
    let* ty :=  Typing.btyp_to_typ te bt  in
    let* v  := genv_get impl x in
    if typ_eq_dec ty (typeof_value v) then
      genv_update ge x v
    else fail.

  Lemma eval_decl_const_preserve_defs : forall te impl ge ge' x  ty,
      eval_decl_const te impl ge x ty = Some ge' ->
      env_preserve_defs ge ge'.
  Proof.
    unfold eval_decl_const.
    intros.
    destruct (Typing.btyp_to_typ te ty); try discriminate.
    simpl in H.
    destruct (genv_get impl x) eqn:GE; try discriminate.
    simpl in H.
    destruct (typ_eq_dec t (typeof_value v)) eqn:TE; try discriminate.
    eapply genv_update_preserve_defs;eauto.
  Qed.


  Lemma genv_update_gss : forall ge ge' id v,
      genv_update ge id v = Some ge' ->
      ge' ! (StringIndexed.index id) = Some v.
  Proof.
    unfold genv_update; intros.
    unfold genv_get in H.
    unfold STree.get in H.
    destruct (ge ! (StringIndexed.index id)) eqn:G ; try discriminate.
    simpl in H. unfold STree.set in H.
    inv H. rewrite PTree.gss. reflexivity.
  Qed.

  (* [lenv_of_record_of_lenv] the [BOUND] hyp is necessary.
     Otherwise, we could overwrite the local environment
     with a value of the global environment.
     NB: I think the issue disappear if there is a single environment *)
  Lemma lenv_of_record_of_lenv :
    forall ge rt le r
           (BOUND : forall x v, List.In (x,v) rt -> SSet.mem x (STree.keys le) = true)
           (NODU  : MapList.nodup String.string_dec rt = true),
      record_of_lenv  ge rt le = Some r ->
      lenv_of_record  rt r le = le.
  Proof.
    induction rt.
    - simpl. reflexivity.
    - simpl.
      intros.
      monadInv H.
      simpl.
      destruct a.
      destruct (MapList.mem string_dec t rt) eqn:MEM; try discriminate.
      simpl in EQ.
      simpl in EQ1.
      unfold cast_value in EQ1.
      destruct x.
      simpl in x0.
      assert (t1 = t0).
      { apply cast_typ_ok_imp_typ_eq in EQ1.
        congruence.
      }
      subst.
      rewrite cast_typ_id in EQ1.
      inv EQ1. simpl.
      unfold get_env in EQ.
      destruct (STree.get t le) eqn:GET.
      + inv GET. inv EQ.
        unfold lenv_update.
        rewrite STree.get_set_same by auto.
        apply IHrt; auto.
        intros.
        eapply BOUND. right; eauto.
      + rewrite STree.keys_get_mem_false_iff in GET.
        erewrite BOUND in GET. discriminate.
        left ; reflexivity.
  Qed.

  Lemma keys_lenv_of_record : forall rt le r,
      forall x, SSet.mem x (STree.keys (lenv_of_record rt r le)) = SSet.mem x (STree.keys le) || MapList.mem string_dec x rt.
  Proof.
    induction rt;simpl; auto.
    - intros. rewrite orb_comm. reflexivity.
    - destruct a.
      intros.
      rewrite IHrt.
      simpl.
      rewrite keys_lenv_update.
      rewrite SSet.mem_add.
      destruct (string_dec x s) ; destruct (string_dec s x); try congruence.
      simpl. rewrite orb_comm. reflexivity.
  Qed.


  Section EVAL_EXPR.

    Context {EXPR : Type}.

    Variable eval_expr : tenv -> genv -> lenv -> (forall (ty: typ) (e: EXPR), option(eval_typ ty)).


    Fixpoint eval_fun_rec (te: tenv) (ge: genv) (le: lenv) (params: smaplist typ) (tret: typ) (e: EXPR) :
    eval_funtyp eval_typ (List.map snd  params) (eval_typ tret) :=
    match params  with
    | [] => fun _ : unit => eval_expr te ge le tret e
    | p :: l =>
        fun y : eval_typ (snd p) =>
          (match
            l as l0
            return
            (eval_funtyp eval_typ (List.map (fun x : string * typ => snd x) l0) (eval_typ tret) ->
             let l1 := List.map snd l0 in
             match l1 with
             | [] => option(eval_typ tret)
             | _ :: _ => eval_funtyp eval_typ l1 (eval_typ tret)
            end)
          with
          | [] =>
              fun _ => eval_expr te ge (lenv_update le (fst p) (Val (snd p) y)) tret e
          | p0 :: l0 =>
              fun
                eval_fun_rec  => eval_fun_rec
          end) (eval_fun_rec te ge (lenv_update le (fst p) (Val (snd p) y)) l tret e)
  end.

  Lemma eval_fun_rec_rw : forall (te: tenv) (ge: genv) (le: lenv) (params: smaplist typ) (tret: typ) (e: EXPR),
    eval_fun_rec te ge le params tret e =
    match params  with
    | [] => fun _ : unit => eval_expr te ge le tret e
    | p :: l =>
        fun y : eval_typ (snd p) =>
          match
            l as l0
            return
            (eval_funtyp eval_typ (List.map (fun x : string * typ => snd x) l0) (eval_typ tret) ->
             match List.map snd l0 with
           | [] => option(eval_typ tret)
           | _ :: _ => eval_funtyp eval_typ (List.map (fun x : string * typ => snd x) l0) (eval_typ tret)
           end)
      with
      | [] =>
          fun _ => eval_expr te ge (lenv_update le (fst p) (Val (snd p) y)) tret e
      | p0 :: l0 =>
          fun
            eval_fun_rec  => eval_fun_rec
      end (eval_fun_rec te ge (lenv_update le (fst p) (Val (snd p) y)) l tret e)
  end.
  Proof.
    destruct params;reflexivity.
  Qed.

  Definition eval_fun (te: tenv) (ge: genv) (params: smaplist typ) (tret: typ) (e: EXPR) : eval_typ (TFun (List.map (fun x => snd x) params) tret) :=
    eval_fun_rec te ge STree.empty params tret e.

  (* Definition mk_fun_value (te: tenv) (ge: genv) (params: smaplist btyp) (tret: btyp) (e: EXPR) : optionvalue :=
    if MapList.nodup Ident.eq_dec params then
      let* tret' := btyp_to_typ te tret in
      let* params' := MapList.map_err (btyp_to_typ te) params in
      ret (Val (TFun (List.map (fun x => snd x) params') tret') (eval_fun te ge params' tret' e))
    else fail. *)

  Definition eval_def_fun (te: tenv) (ge: genv) (x: ident) (f: Syntax.function EXPR btyp) : option genv :=
    let '(tret, params) := (fn_return f, fn_params f) in
    if MapList.nodup Ident.eq_dec params then
      let* tret' := btyp_to_typ te tret in
      let* params' := MapList.mmap _ (btyp_to_typ te) params in
      let fv := Val (TFun (List.map (fun x => snd x) params') tret') (eval_fun te ge params' tret' (fn_body f)) in
      genv_update ge x fv
    else fail.

  Definition fields_btyp_to_typ (te: tenv) (fields: smaplist btyp) : option (smaplist typ) :=
    MapList.mmap _ (btyp_to_typ te) fields.

  Definition eval_decl_fun (te:tenv) (impl ge : genv) (x: ident) (params : list (Syntax.param_attr * btyp)) (tret:btyp) : option genv :=
    let* tparams := mmap (Typing.btyp_to_typ te) (List.map snd params) in
    let* tret   := Typing.btyp_to_typ te tret in
    let* v := genv_get impl x in
    if (typ_eq_dec (TFun tparams tret) (typeof_value v)) then
      genv_update ge x v
    else fail.

  Definition eval_globdef (te: tenv) (impl ge: genv) (def: globdef EXPR btyp literal) : option genv :=
    match def with
    | DefConst x l ty => eval_def_const te ge x l ty
    | DefFun x f => eval_def_fun te ge x f
    | DeclConst y bt => eval_decl_const te impl ge y bt
    | DeclFun y params tret => eval_decl_fun te impl ge y params tret
    end.

  Lemma eval_globdef_add_gid:
    forall te impl ge ge' def, 
      eval_globdef te impl ge def = Some ge' ->
      STree.keys ge' = SSet.add (globdef_id def) (STree.keys ge).
  Proof.
    intros; destruct def; simpl in H.
    - unfold eval_def_const in H. monadInv H.
      unfold genv_update in EQ3.
      destruct (genv_get ge i); try discriminate.
      inv EQ3. simpl. apply STree.keys_set.
    - unfold eval_def_fun in H.
      destruct (MapList.nodup Ident.eq_dec (fn_params f)); try discriminate.
      monadInv H. unfold genv_update in EQ2.
      destruct (genv_get ge i); try discriminate.
      inv EQ2. simpl. apply STree.keys_set. 
    - unfold eval_decl_const in H. monadInv H.
      destruct (typ_eq_dec x (typeof_value x0)); try discriminate.
      unfold genv_update in EQ2.
      destruct (genv_get ge i); try discriminate.
      inv EQ2. simpl. apply STree.keys_set. 
    - unfold eval_decl_fun in H.
      Opaque typ_eq_dec. monadInv H.
      destruct (typ_eq_dec (TFun x x0) (typeof_value x1)); try discriminate.
      unfold genv_update in EQ3. destruct (genv_get ge i); inv EQ3.
      simpl. apply STree.keys_set.
  Qed. 

  Definition eval_prog_rec (te:tenv) (impl:genv) (ge:genv) (prog:list (globdef EXPR btyp literal)) : option genv :=
    fold_left_err
      (fun acc d => eval_globdef te impl acc d)
      prog ge.


  Definition eval_prog (impl: genv) (prog: program EXPR btyp literal) : option(tenv * genv) :=
    let* te := tenv_of_type_defs (prog_types prog) in
    let* ge' := eval_prog_rec te impl STree.empty (prog_defs prog)  in
    ret (te, ge').

  Lemma eval_def_fun_preserve_defs : forall te ge x f ge',
      eval_def_fun te ge x f = Some ge' ->
      env_preserve_defs ge ge'.
  Proof.
    unfold eval_def_fun.
    intros.
    destruct (MapList.nodup Ident.eq_dec (fn_params f)); try discriminate.
    destruct (btyp_to_typ te (fn_return f)); try discriminate.
    simpl in H. destruct (MapList.mmap _ (btyp_to_typ te) (fn_params f)); try discriminate.
    simpl in H.
    eapply genv_update_preserve_defs;eauto.
  Qed.

  Lemma eval_decl_fun_preserve_defs : forall te impl ge ge' f targs tret,
      eval_decl_fun te impl ge f targs tret = Some ge' ->
      env_preserve_defs ge ge'.
  Proof.
    unfold eval_decl_fun.
    intros.
    destruct (mmap (btyp_to_typ te) (List.map snd targs)) eqn:P; try discriminate.
    destruct (btyp_to_typ te tret); try discriminate.
    destruct (genv_get impl f) eqn:GET; try discriminate.
    unfold bind, Res.bind in H.
    destruct (typ_eq_dec (TFun l t) (typeof_value v)); try discriminate.
    eapply genv_update_preserve_defs; eauto.
  Qed.


  Lemma eval_globdef_preserve_defs : forall te impl ge ge' a,
      eval_globdef te impl ge a = Some ge' ->
      env_preserve_defs ge ge'.
  Proof.
    destruct a; simpl.
    - intros.
      eapply eval_def_const_preserve_defs; eauto.
    - intros.
      eapply eval_def_fun_preserve_defs; eauto.
    - intros.
      eapply eval_decl_const_preserve_defs in H ; eauto.
    - intros.
      eapply eval_decl_fun_preserve_defs in H ; eauto.
  Qed.


  Lemma eval_prog_rec_preserve_defs :
    forall  prog impl ge  te ge'
           (EVAL: eval_prog_rec te impl ge prog = Some  ge'),
      env_preserve_defs ge ge'.
  Proof.
    unfold eval_prog_rec.
    induction prog.
    - simpl; intros. inv EVAL. apply env_preserve_defs_refl.
    - simpl; intros.
      destruct (eval_globdef te impl ge a) eqn:GD; try discriminate.
      simpl in EVAL.
      eapply IHprog in EVAL ;eauto.
      eapply env_preserve_defs_trans;eauto.
      eapply eval_globdef_preserve_defs;eauto.
  Qed.


  Lemma genv_get_preserve_defs :
    forall  prog te impl ge   ge' x v
           (EVAL: eval_prog_rec te impl ge prog = Some ge')
           (GET : genv_get  ge x = Some v),
      genv_get  ge' x = Some v.
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

  End EVAL_EXPR.

  End PRESERVE_ENV.

End DENOT.

Ltac erase_cast H :=
  let EQt := fresh "EQt" in
  match type of H with
  | @cast_typ _ _ _ _ = Some _ =>
      pose proof (cast_typ_ok_imp_typ_eq _ _ _ _ _ H) as EQt;
      subst; rewrite cast_typ_id in H
  | @ecast_typ _ _ _ _ = Some _ =>
      pose proof (ecast_typ_ok_imp_typ_eq _ _ _ _ _ H) as EQt;
      subst; rewrite ecast_typ_id in H
  end.
