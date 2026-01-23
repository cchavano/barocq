From Coq Require Import String Bool List Eqdep.
From compcert Require Import Coqlib Maps Integers.
From BarocqComp Require Import Error Utils Types Syntax Barray Benum Brecord Maps2 Typing Intop.
From BarocqComp Require DList.
Import ListNotations.

Section DENOT.

  Variable arch : Target.archi.

  (* Abstract type implementation environment *)
  Variable tabs : PMap.t Type.

  Notation eval_typ := (Types.eval_typ tabs).

  Inductive value : Type :=
    | Val (t: typ) (v: eval_typ t) : value.

  Definition typof_index : typ :=
    match arch with
    | Target.Ptr32 => TInt32 Unsigned
    | Target.Ptr64 => TInt64 Unsigned
    end.

  Definition genv := STree.t value.

  Definition lenv := STree.t value.

  Definition genv_get (ge: genv) (x: ident) : res value :=
    err_of_opt (STree.get x ge).

  Definition genv_update (ge: genv) (x: ident) (v: value) : res genv :=
    match genv_get ge x with
    | OK _ => fail
    | Error _ => ret (STree.set x v ge)
    end.

  Definition lenv_get (le: lenv) (x: ident) : res value :=
    err_of_opt (STree.get x le).

  Definition lenv_update (le: lenv) (x: ident) (v: value) : lenv :=
    STree.set x v le.

  Definition cast_typ  {t2:typ} (v: eval_typ t2) (t1:typ): res (eval_typ t1) :=
    match typ_eq_dec t2 t1 with
    | left EQ => OK (cast (f_equal eval_typ EQ) v)
    | _       => fail
    end.

  Definition ecast_typ  {t2:typ} (v: res (eval_typ t2)) (t1:typ): res (eval_typ t1) :=
    match typ_eq_dec t2 t1 with
    | left EQ =>  cast (f_equal res (f_equal eval_typ EQ)) v
    | _       => fail
    end.

  Lemma ecast_same_typ:
    forall t v,
    @ecast_typ t v t = v.
  Proof.
    intros. 
    unfold ecast_typ. destruct (typ_eq_dec t t).
    - assert (e = eq_refl). apply UIP_refl.
      rewrite H. reflexivity.
    - contradiction.
  Qed.

  Definition cast_value  (v:value) (t1:typ) : res (eval_typ t1).
  Proof.
    destruct v.
    apply (cast_typ v t1).
  Defined.

  Definition eval_var  (ge: genv) (le: lenv) (x: ident) (ty:typ) : res (eval_typ ty) :=
    match (lenv_get le x) with
    | OK v => cast_value  v ty
    | Error _ => let* v := genv_get ge x in
                 cast_value v ty
    end.

  Definition eval_constr  (te: tenv) (x: ident) (ty:typ) : res (eval_typ ty) :=
    let* eid := TEnv.get_constr_typ te x in
    let* elems := TEnv.get_edef te eid in
    match (bool_dec (existsb (String.eqb x) elems) true) with
    | left EQ =>  @cast_typ (TEnum eid elems)   (mk_enum elems x EQ) ty
    | right _ => fail
    end.

  Definition partial {A B: Type} (F : A -> B) : A -> res B :=
    fun x => OK (F x).

  Definition partial2 {A B C: Type} (F : A -> B -> C) : A -> B -> res C :=
    fun x y => OK (F x y).


  Definition get_cast (ty:typ) (ty':typ) : res (eval_typ ty -> res (eval_typ ty')) :=
    match ty, ty' with
      (* TBool *)
    | TBool , TBool => OK (fun x => OK x)
    | TBool , TInt32 s => OK (partial (if s then I32.of_bool else U32.of_bool))
    | TBool , TInt64 s => OK (partial (if s then I64.of_bool else U64.of_bool))
    | TBool , TEnum eid elems => OK (fun x => Benum.of_i32 elems (I32.of_bool x))
       (* TInt32 *)
    | TInt32 s , TBool =>  OK (partial (if s then I32.to_bool else U32.to_bool))
    | TInt32 s , TInt32 s' => OK (partial (match s , s' with
                                              | Signed , Unsigned => U32.of_i32
                                              | Unsigned , Signed => I32.of_u32
                                              |  _       ,   _    => fun x => x
                                              end))
    | TInt32 s , TInt64 s' => OK (partial (match s, s' with
                                              | Signed, Signed => I64.of_i32
                                              | Signed, Unsigned => U64.of_i32
                                              | Unsigned, Signed => I64.of_u32
                                              | Unsigned, Unsigned => U64.of_u32
                                              end))
    | TInt32 s ,  TEnum eid elems => OK (fun x => Benum.of_i32 elems (if s then x else I32.of_u32 x))
                 (*  Tint64 *)
    | TInt64 s , TBool => OK (partial (if s then I64.to_bool else U64.to_bool))
    | TInt64 s , TInt32 s' => OK (partial (
                                      match s, s' with
                                      | Signed, Signed =>  I32.of_i64
                                      | Signed, Unsigned => U32.of_i64
                                      | Unsigned, Signed => I32.of_u64
                                      | Unsigned, Unsigned => U32.of_u64
                                      end))
    | TInt64 s ,  TInt64 s' => OK (partial (
                                       match s, s' with
                                       | Signed, Unsigned => U64.of_i64
                                       | Unsigned, Signed => I64.of_u64
                                       | _, _ => fun x => x
                                       end))
    | TInt64 s , TEnum eid elems => OK (fun x => Benum.of_i32 elems (if s then I32.of_i64 x else I32.of_u64 x))
            (* Tenum *)
    | TEnum tid elems , TBool  => OK (partial (fun x => I32.to_bool (Benum.to_i32 x)))
    | TEnum tid elems , TInt32 s => OK (partial (fun x => if s then Benum.to_i32 x else U32.of_i32 (Benum.to_i32 x)))
    | TEnum tid elems , TInt64 s => OK (partial (fun x => if s then I64.of_i32 (Benum.to_i32 x)
                                                          else  U64.of_i32 (Benum.to_i32 x)))
    | _ , _ => fail
    end.

  Definition eval_cast (ty:typ) (v1:eval_typ ty) (tr:typ) : res (eval_typ tr) :=
    let* f := get_cast ty tr in f  v1.

  Definition eval_unary_op (op: unary_op) (ty:typ) : forall (v: eval_typ ty) (tyr : typ), res (eval_typ tyr):=
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
    | TBool , TBool => OK TBool
    |   _   ,   _    => fail
    end.

  Definition int_int_int (t1 t2:typ) :=
    match t1,t2 with
    | TInt32 Signed , TInt32 Signed => OK (TInt32 Signed)
    | TInt32 Unsigned , TInt32 Unsigned => OK (TInt32 Unsigned)
    | TInt64 Signed , TInt64 Signed   => OK (TInt64 Signed)
    | TInt64 Unsigned , TInt64 Unsigned   => OK (TInt64 Unsigned)
    |  _ , _ => fail
    end.

  Definition int_int_bool (t1 t2:typ) :=
    match t1,t2 with
    | TInt32 Signed , TInt32 Signed => OK TBool
    | TInt32 Unsigned , TInt32 Unsigned => OK TBool
    | TInt64 Signed , TInt64 Signed   => OK TBool
    | TInt64 Unsigned , TInt64 Unsigned   => OK TBool
    |  _ , _ => fail
    end.

  Definition eq_neq_bool (t1 t2:typ) :=
    match t1,t2 with
    | TBool , TBool => OK TBool
    | TInt32 Signed , TInt32 Signed => OK TBool
    | TInt32 Unsigned , TInt32 Unsigned => OK TBool
    | TInt64 Signed , TInt64 Signed   => OK TBool
    | TInt64 Unsigned , TInt64 Unsigned   => OK TBool
    | TEnum _ _ , TEnum _ _ => if typ_eq_dec t1 t2 then OK TBool else fail
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

  Definition bool_op (F : bool -> bool -> bool) (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
    match t1, t2 with
    | TBool , TBool => (fun v1 v2 tyr => @cast_typ TBool (F v1 v2) tyr)
    | _, _ =>   (fun _ _ _ => fail)
    end.


  Definition int_op (F32 : int -> int -> int) (F64 : int64 -> int64 -> int64)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
    match t1, t2 with
    | TInt32 s , TInt32 s' => if signedness_eq_dec s s' then
                                (fun v1 v2 tyr => @cast_typ (TInt32 s) (F32 v1 v2) tyr)
                              else (fun _ _ _ => fail)
    | TInt64 s , TInt64 s' => if signedness_eq_dec s s' then
                                (fun v1 v2 tyr => @cast_typ (TInt64 s) (F64 v1 v2) tyr)
                              else (fun _ _ _ => fail)
    | _, _ =>   (fun _ _ _ => fail)
    end.


  Definition int_op_s (F32s : int -> int -> res int) (F32u : int -> int -> res int)
    (F64s : int64 -> int64 -> res int64) (F64u : int64 -> int64 -> res int64)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
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
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
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
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
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


  Definition eval_binary_op (op: binary_op) : forall (t1:typ) (t2: typ)  (v1: eval_typ t1)  (v2: eval_typ t2) (tyr : typ), res (eval_typ tyr) :=
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

  Fixpoint eval_array_lit (a: array value) : res value :=
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

  Fixpoint eval_record_lit_rec (lv: smaplist value) (fields: smaplist typ) : res (eval_recordtyp eval_typ fields).
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

  Definition eval_record_lit (n: ident) (lv: smaplist value) (fields: smaplist typ) : res value.
    destruct lv as [|x lv'].
    - apply fail.
    - destruct (eval_record_lit_rec (x :: lv') fields) as [r |].
      * apply (ret (Val (TRecord n fields) r)).
      * apply fail.
  Defined.

  Definition eval_array_get (ta:typ) (a: eval_typ ta) (t2:typ) (i: eval_typ t2) (tyr:typ): res (eval_typ tyr) :=
    match ta as t return (eval_typ t -> res (eval_typ tyr)) with
    | TArray t =>
    (fun  (a0 : array (eval_typ t)) =>
     match arch with
     | Target.Ptr32 =>
         match typ_eq_dec t2 (TInt32 Unsigned) with
         | left EQ => ecast_typ (get a0 (U64.of_u32 (cast (f_equal eval_typ EQ) i))) tyr
         | right _ => fail
         end
     | Target.Ptr64 =>
         match typ_eq_dec t2 (TInt64 Unsigned) with
         | left EQ => ecast_typ (get a0 (cast (f_equal eval_typ EQ) i)) tyr
         | right _ => efail
         end
     end)
    | _ => fun _ => efail
    end a.

  Definition eval_array_set (ta: typ) (a : eval_typ ta) (t2:typ)
    (i : eval_typ t2) (t:typ) (v: eval_typ t) (tyr : typ): res (eval_typ tyr).
  Proof.
    destruct ta.
    4 :
    {
      destruct arch eqn:Earch.
      - destruct (typ_eq_dec t2 (TInt32 Unsigned)).
        + destruct (typ_eq_dec ta t).
          * subst. simpl in i. simpl in a.
            apply (@ecast_typ (TArray t) (Barray.set a (U64.of_u32 i) v)).
          * apply fail.
        + apply fail.
      - destruct (typ_eq_dec t2 (TInt64 Unsigned)).
        + destruct (typ_eq_dec ta t).
          * subst. simpl in i. simpl in a.
            apply (@ecast_typ (TArray t) (Barray.set a  i v)).
          * apply fail.
        + apply fail.
    }
    all: apply fail.
  Defined.

  Import MapList.

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
      exists t0. reflexivity.
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

  Definition eval_record_project_aux (fields: smaplist typ) (rc: eval_recordtyp eval_typ fields) (k: ident) (ty:typ) : res (eval_typ ty).
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

  Definition eval_record_project (ty:typ) : forall (v: eval_typ ty) (k: ident) (tyr : typ), res (eval_typ tyr) :=
    match ty with
    | TRecord _ fields => fun v k tyr => eval_record_project_aux fields v k tyr
    | _ => fun _ _ _ => fail
    end.


  Definition typeof_value  (v : value ) :=
    match v with
    | Val t _ => t
    end.

  Definition typof_field_dec (k:ident) (fields: smaplist typ) : res {t : typ| typof_field k fields = OK t}.
  Proof.
    destruct (typof_field k fields) as [t |] eqn:Etyp.
    apply OK. exists t. reflexivity.
    apply fail.
  Defined.

Ltac change_good_proj :=
  match goal with
  | |- context[good_proj ?K ((?S,?V)::?L)] =>
      change (good_proj K ((S,V)::L)) with ((K=?S)%string || good_proj K L)
  end.

Fixpoint good_proj_map  (A B: Type) (F : A -> B) (k:key) (fields :smaplist A):
    good_proj k fields = good_proj k (map F fields).
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
  forall (GP : good_proj k fields = true), good_proj k (map F fields) = true.
Proof.
  intros.
  rewrite <- GP.
  symmetry. apply good_proj_map.
Defined.

Fixpoint typeof_field_typ (k:key) (fields : smaplist typ) (GK: good_proj k fields = true) :
  { ty : typ | find_type_of_field k fields = OK ty}.
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
      exists t0;reflexivity.
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
  (EQ : find_type_of_field k fields = OK tv):
  gtype_of_field eval_typ k fields.
Proof.
  unfold gtype_of_field.
  rewrite EQ. apply  v.
Defined.

Definition eval_record_upd_aux  (fields: smaplist typ) (rc: eval_recordtyp eval_typ fields) (k: ident) (tv: typ) (v: eval_typ tv) :
  res (eval_recordtyp eval_typ fields) :=
  dyn_upd eval_typ typ_eq_dec rc k tv v.

  Definition eval_record_update (t1:typ) : forall (v1: eval_typ t1) (k: ident) (tv : typ) (v: eval_typ tv) (tyr:typ), res (eval_typ tyr) :=
    match t1 with
    | TRecord n fields => fun st k tv v tyr =>
                            @ecast_typ (TRecord n fields) (eval_record_upd_aux fields st k tv v) tyr
    | _ => fun _ _ _ _ _ => fail
    end.

  Definition typof_record_project (ty:typ) (f:ident): res typ :=
    match ty with
    | TRecord _ l => find_err key_eq f l
    |    _      => fail
    end.

  Definition typof_array (ty:typ) : res typ :=
    match ty with
    | TArray e => OK e
    |    _      => fail
    end.

  Definition res_eq_typ (v1 v2 : res value) : bool :=
    match v1 , v2 with
    | Error _ , _ | _ , Error _ => true
    | OK v1 , OK v2 => proj_sumbool (typ_eq_dec (typeof_value v1) (typeof_value v2))
    end.

  Definition eval_ifthenelse (c:bool) (t2: typ) (v2:res (eval_typ t2)) (t3: typ)  (v3: res (eval_typ t3)) (tr:typ) : res (eval_typ tr) :=
    if c then ecast_typ v2 tr else ecast_typ v3 tr.



  Definition eval_match (tv:typ) (v: eval_typ tv) (tr: typ) (cases: list (pattern * (res (eval_typ tr)))) : res (eval_typ tr) :=
    (match tv as t0 return (eval_typ t0 -> res (eval_typ tr)) with
    | TEnum _ elems => 
        (fun v0 => match_with_err v0 cases)
    | _ => (fun _ => fail)
    end) v.

  Fixpoint eval_app (tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams (eval_typ tret)) (args: DList.dlist eval_typ tparams) (ty: typ):
    res (eval_typ ty).
  Proof.
    destruct args.
    - simpl in f. apply (ecast_typ (f tt) ty).
    - simpl in f.
      destruct l.
      + apply (ecast_typ (f e) ty).
      + apply (eval_app _ _ (f e) args).
  Defined.

  Fixpoint eval_app_typ (tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams (eval_typ tret)) (args: DList.dlist eval_typ tparams) (ty:typ):
    res (eval_typ ty).
  Proof.
    destruct args.
    - simpl in f. apply (ecast_typ (f tt) ty).
    - simpl in f.
      destruct l.
      +  apply (ecast_typ (f e) ty).
      + apply (eval_app_typ _ _ (f e) args ty).
  Defined.

  Fixpoint eval_app_res (tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams (eval_typ tret))
    (args: DList.dlist (fun (ty:typ) => res (eval_typ ty)) tparams) (ty:typ):
    res (eval_typ ty).
  Proof.
    destruct args.
    - simpl in f. apply (ecast_typ (f tt) ty).
    - simpl in f.
      destruct l.
      + apply (let* e' := e in ecast_typ (f e') ty).
      + eapply bind. apply e.
      apply (fun x => eval_app_res _ _ (f x) args ty).
  Defined.

  Definition typof_atom (te: tenv) (a: atom) : res typ :=
    btyp_to_typ te (typof_atom a).

  Fixpoint eval_atom (te: tenv) (ge: genv) (le: lenv) (ty: typ) (a: atom) : res (eval_typ ty) :=
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
    | AUnaryOp op a1 bt =>
        let* ta1 := btyp_to_typ te bt in
        let* v := eval_atom te ge le ta1 a1 in
        eval_unary_op op ta1 v ty
    | ABinaryOp op a1 a2 bt =>
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
            (* let* vargs := DList.map2 _ (eval_atom te ge le) args tparams in
            eval_app_res tparams tret f vargs ty *)
            let* vargs := DList.mmap _ (eval_atom te ge le) args tparams in
            eval_app tparams tret f vargs ty
        |  _  => fail
        end
    end.

  Definition eval_comp (te: tenv) (ge: genv) (le: lenv) (ty: typ) (c: comp) : res (eval_typ ty) :=
    match c with
    | CpAtom a _ => eval_atom te ge le ty a
    | CpArraySet a1 a2 a3 _ =>
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* ta3 := typof_atom te a3 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        let* v3 := eval_atom te ge le ta3 a3 in
        eval_array_set ta1 v1 ta2 v2 ta3 v3 ty
    | CpRecordUpdate a1 k a2 _ =>
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
            (* let* vargs := DList.map2 _ (eval_atom te ge le) args tparams in
            eval_app_res tparams tret f vargs ty *)
            let* vargs := DList.mmap _ (eval_atom te ge le) args tparams in
            eval_app tparams tret f vargs ty
        |  _  => fail
        end
    end.

  Definition cast_int (t:typ) (i:int) : res (eval_typ t) :=
    match t with
    | TInt32 s => OK i
    |  _       => fail
    end.

  Definition cast_int64 (t:typ) (i:int64) : res (eval_typ t) :=
    match t with
    | TInt64 s => OK i
    |  _       => fail
    end.

  Fixpoint eval_literal (te: tenv) (l: literal) : res value :=
    match l with
    | LTrue => ret (Val TBool true)
    | LFalse => ret (Val TBool false)
    | LInt32 i s => ret (Val (TInt32 s) i)
    | LInt64 i s => ret (Val (TInt64 s) i)
    | LArray a _ _ =>
        let* av := mmap (eval_literal te) a in
        eval_array_lit av
    | LRecord rc _ rid =>
        let* rcv := MapList.map_err (eval_literal te) rc in
        let* fields := TEnv.get_rdef te rid in
        eval_record_lit rid rcv fields
    end.

  Definition cast_typ_M (tret:typ) (v: value) : M (eval_typ tret) :=
    match v with
      | Val tv v =>
          match typ_eq_dec tv tret with
          | left e =>  (ret (typ_cast tabs e v))
          |  _     => fail
          end
    end.

  Section EVAL_EXPR.

  Variable EXPR : Type.

  Variable eval_expr : tenv -> genv -> lenv -> (forall (ty: typ) (e: EXPR), res (eval_typ ty)).

  Fixpoint build_funval_rec (te: tenv) (ge: genv) (le: lenv) (params: smaplist typ) (tret: typ) (e: EXPR) :
    eval_funtyp eval_typ (List.map snd  params) (eval_typ tret) :=
    match params  with
    | [] => fun _ : unit => eval_expr te ge le tret e
    | p :: l =>
        fun y : eval_typ (snd p) =>
          match
            l as l0
            return
            (eval_funtyp eval_typ (List.map (fun x : string * typ => snd x) l0) (eval_typ tret) ->
             let l1 := List.map snd l0 in
             match l1 with
             | [] => res (eval_typ tret)
             | _ :: _ => eval_funtyp eval_typ l1 (eval_typ tret)
           end)
      with
      | [] =>
          fun _ => eval_expr te ge (lenv_update le (fst p) (Val (snd p) y)) tret e
      | p0 :: l0 =>
          fun
            build_funval_rec  => build_funval_rec
      end (build_funval_rec te ge (lenv_update le (fst p) (Val (snd p) y)) l tret e)
  end.

  Lemma build_funval_rec_rw : forall (te: tenv) (ge: genv) (le: lenv) (params: smaplist typ) (tret: typ) (e: EXPR),
    build_funval_rec te ge le params tret e =
    match params  with
    | [] => fun _ : unit => eval_expr te ge le tret e
    | p :: l =>
        fun y : eval_typ (snd p) =>
          match
            l as l0
            return
            (eval_funtyp eval_typ (List.map (fun x : string * typ => snd x) l0) (eval_typ tret) ->
             match List.map snd l0 with
           | [] => res (eval_typ tret)
           | _ :: _ => eval_funtyp eval_typ (List.map (fun x : string * typ => snd x) l0) (eval_typ tret)
           end)
      with
      | [] =>
          fun _ => eval_expr te ge (lenv_update le (fst p) (Val (snd p) y)) tret e
      | p0 :: l0 =>
          fun
            build_funval_rec  => build_funval_rec
      end (build_funval_rec te ge (lenv_update le (fst p) (Val (snd p) y)) l tret e)
  end.
  Proof.
    destruct params;reflexivity.
  Qed.

  Definition build_funval (te: tenv) (ge: genv) (params: smaplist typ) (tret: typ) (e: EXPR) : eval_typ (TFun (List.map (fun x => snd x) params) tret) :=
    build_funval_rec te ge STree.empty params tret e.

  Definition build_fun_value (te: tenv) (ge: genv) (params: smaplist btyp) (tret: btyp) (e: EXPR) : res value :=
    if MapList.nodup Ident.eq_dec params then
      let* tret' := btyp_to_typ te tret in
      let* params' := MapList.map_err (btyp_to_typ te) params in
      ret (Val (TFun (List.map (fun x => snd x) params') tret') (build_funval te ge params' tret' e))
    else fail.

  Definition eval_def_fun (te: tenv) (ge: genv) (x: ident) (f: Syntax.function EXPR btyp) : res genv :=
    let* fv := build_fun_value te ge (fn_params f) (fn_return f) (fn_body f) in
    genv_update ge x fv.

  Definition fields_btyp_to_typ (te: tenv) (fields: smaplist btyp) : res (smaplist typ) :=
    MapList.map_err (btyp_to_typ te) fields.

  Definition eval_def_const (te: tenv) (ge: genv) (x: ident) (l: literal) (ty: btyp) : res genv :=
    let* ty' := btyp_to_typ te ty in
    let* vv := eval_literal te l in
    let* v'  := cast_value vv ty' in
    genv_update ge x (Val ty' v').

  Definition eval_decl_const (te: tenv) (impl ge: genv) (x:ident) (bt:btyp) : res genv :=
    let* ty :=  Typing.btyp_to_typ te bt  in
    let* v  := genv_get impl x in
    if typ_eq_dec ty (typeof_value v) then
      genv_update ge x v
    else fail.

  Definition eval_decl_fun (te:tenv) (impl ge : genv) (x:Syntax.ident) (params : list (Syntax.param_attr * btyp)) (tret:btyp) : res genv :=
    let* tparam := mmap (Typing.btyp_to_typ te) (List.map snd params) in
    let* tret   := Typing.btyp_to_typ te tret in
    let* v := genv_get impl x in
    if (typ_eq_dec (TFun tparam tret) (typeof_value v)) then
      genv_update ge x v
    else fail.

  Definition eval_globdef (te: tenv) (impl ge: genv) (def: globdef EXPR btyp literal) : res genv :=
    match def with
    | DefConst x l ty => eval_def_const te ge x l ty
    | DefFun x f => eval_def_fun te ge x f
    | DeclConst y bt => eval_decl_const te impl ge y bt
    | DeclFun y params tret => eval_decl_fun te impl ge y params tret
    end.

  Definition eval_prog (impl: genv) (prog: program EXPR btyp literal) : res (tenv * genv) :=
    let* te := tenv_of_type_defs (prog_types prog) in
    let* ge' :=
      list_fold_left_err
        (fun acc d => eval_globdef te impl acc d)
        (prog_defs prog)
        (ret STree.empty)
    in
    ret (te, ge').

  End EVAL_EXPR.

End DENOT.
