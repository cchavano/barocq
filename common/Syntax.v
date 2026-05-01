From Stdlib Require Import PeanoNat Lia.
From compcert Require Import Integers Ctypes.
From BarocqComp Require Import Utils Ident Types Maps2 ExtOrdered.

(** * Syntax shared by some of the intermediate representations. *)

Definition ident := Ident.ident.

(** ** Constant literals *)

Inductive literal :=
  | LTrue : literal
  | LFalse  : literal
  | LInt32 : int -> signedness -> literal
  | LInt64 : int64 -> signedness -> literal
  | LArray : list literal -> btyp -> layout -> literal
  | LRecord : smaplist literal -> list ident -> ident -> literal.

Definition btypof_literal (l: literal) : btyp :=
  match l with
  | LTrue
  | LFalse => BBool
  | LInt32 _ s => BInt32 s
  | LInt64 _ s => BInt64 s
  | LArray _ ta ly => BArray ta ly
  | LRecord rc ub rid => BRecord rid ub
  end.

(** ** Operators *)

Inductive unary_op : Type :=
  | UopNotbool : unary_op
  | UopNotint : unary_op
  | UopNeg : unary_op
  | UopPlus : unary_op.

Inductive binary_op : Type :=
  | BopAndbool : binary_op
  | BopOrbool : binary_op
  | BopXorbool : binary_op
  | BopAdd : binary_op
  | BopSub : binary_op
  | BopMul : binary_op
  | BopDiv : binary_op
  | BopMod : binary_op
  | BopAndint : binary_op
  | BopOrint : binary_op
  | BopXorint : binary_op
  | BopShl : binary_op
  | BopShr : binary_op
  | BopEq : binary_op
  | BopNeq : binary_op
  | BopLt : binary_op
  | BopGt : binary_op
  | BopLe : binary_op
  | BopGe : binary_op.

(** cast operators are implicit and resolved using typing information *)
Inductive cast_operator :=
  | Cid (* Identitty *)
  | I32_of_bool
  | U32_of_bool
  | I64_of_bool
  | U64_of_bool
  | Benum_of_i32_I32_of_bool (enum: list ident) (* *)
  | I32_to_bool
  | U32_to_bool
  | U32_of_i32
  | I32_of_u32
  | I64_of_i32
  | U64_of_i32
  | U64_of_u32
  | I64_of_u32
  | Benum_of_i32 (enum: list ident)
  | Benum_of_i32_I32_of_u32 (enum : list ident)
  | I64_to_bool
  | U64_to_bool
  | I32_of_i64
  | U32_of_i64
  | I32_of_u64
  | U32_of_u64
  | U64_of_i64
  | I64_of_u64
  | Benum_of_i32_I32_of_i64 (enum: list ident)
  | Benum_of_i32_I32_of_u64 (enum: list ident)
  | I32_to_bool_Benum_to_i32 (enum: list ident)
  | Benum_to_i32
  | U32_of_i32_Benum_to_i32
  | I64_of_i32_Benum_to_i32
  | U64_of_i32_Benum_to_i32.

(** ** Atoms *)

(** Atoms are pure computations in C *)
(** For AArrayGet and ARecordProj, we store the layout of the result. *)

Inductive atom :=
  | ATrue : atom
  | AFalse : atom
  | AInt32 : int -> signedness -> atom
  | AInt64 : int64 -> signedness -> atom
  | AConstr : ident -> int -> btyp -> atom
  | AVar : ident -> btyp -> atom
  | ACast : atom -> btyp -> atom
  | AUnaryOp : unary_op -> atom -> btyp -> atom
  | ABinaryOp : binary_op -> atom -> atom -> btyp -> atom
  | AArrayGet : atom -> atom -> layout -> btyp -> atom
  | ARecordProj : atom -> ident -> layout -> btyp -> atom
  | APureCall : ident -> btyp -> list atom -> btyp -> atom.

Definition btypof_atom (a: atom) : btyp :=
  match a with
  | ATrue | AFalse => BBool
  | AInt32 i s => BInt32 s
  | AInt64 i s => BInt64 s
  | AConstr _ _ ty
  | AVar _ ty
  | ACast _ ty
  | AUnaryOp _ _ ty
  | ABinaryOp _ _ _ ty
  | AArrayGet _ _ _ ty
  | ARecordProj _ _ _ ty
  | APureCall _ _ _ ty => ty
  end.

Section ATOMIND.

Fixpoint atom_depth (a: atom) : nat :=
  match a with
  | ATrue | AFalse | AInt32 _ _ | AInt64 _ _ | AConstr _ _ _ | AVar _ _ => 0
  | ACast a _ | AUnaryOp _ a _ | ARecordProj a _ _ _ => 1 + (atom_depth a)
  | ABinaryOp _ a1 a2 _ | AArrayGet a1 a2 _ _ => 1 + (max (atom_depth a1) (atom_depth a2))
  | APureCall _ _ args _ =>
      1 + (List.fold_right (fun a acc => max (atom_depth a) acc)) 0 args
  end.

Variable P : atom -> Prop.

Variable PATrue : P ATrue.

Variable PFalse : P AFalse.

Variable PAInt32 : forall i s, P (AInt32 i s).

Variable PAInt64 : forall i s, P (AInt64 i s).

Variable PAConstr : forall i n t, P (AConstr i n t).

Variable PAVar : forall i t, P (AVar i t).

Variable PACast : forall a t, P a -> P (ACast a t).

Variable PAUnaryOp : forall op a t, P a -> P (AUnaryOp op a t).

Variable PABinaryOp : forall op a1 a2 t, P a1 -> P a2 -> P (ABinaryOp op a1 a2 t).

Variable PAArrayGet : forall a1 a2 ly t, P a1 -> P a2 -> P (AArrayGet a1 a2 ly t).

Variable PARecordProj : forall a f ly t, P a -> P (ARecordProj a f ly t).

Variable PAPureCall : forall i tf args tr, (forall x, List.In x args -> P x) -> P (APureCall i tf args tr).

Lemma atom_depth_ind : forall a, P a.
Proof.
  intro. remember (atom_depth a) as n.
  revert a Heqn.
  induction n using Wf_nat.lt_wf_ind.
  destruct n.
  - destruct a; (auto || discriminate).
  - destruct a; try (tauto || discriminate);
    simpl; intros.
    + apply PACast. specialize (H n).
      apply H. lia. inversion Heqn. reflexivity.
    + apply PAUnaryOp. specialize (H n).
      apply H. lia. inversion Heqn. reflexivity.
    + inversion Heqn. clear Heqn.
      assert (Hinf1: (atom_depth a1) < S n). lia.
      assert (Hinf2: (atom_depth a2) < S n). lia.
      apply PABinaryOp.
      * apply (H (atom_depth a1) Hinf1 a1). reflexivity.
      * apply (H (atom_depth a2) Hinf2 a2). reflexivity.
    + inversion Heqn. clear Heqn.
      assert (Hinf1: (atom_depth a1) < S n). lia.
      assert (Hinf2: (atom_depth a2) < S n). lia.
      apply PAArrayGet.
      * apply (H (atom_depth a1) Hinf1 a1). reflexivity.
      * apply (H (atom_depth a2) Hinf2 a2). reflexivity.
    + apply PARecordProj. specialize (H n).
      apply H. lia. inversion Heqn. reflexivity.
    + apply PAPureCall. inversion Heqn. clear Heqn.
      intros. apply H with (m := (atom_depth x)).
      rewrite H1. clear - H0.
      {
        induction l.
        - destruct H0.
        - simpl in *. destruct H0.
          + rewrite H. lia.
          + apply IHl in H. lia.
      }
      reflexivity.
Qed.

End ATOMIND.

(** ** Computations with atomic operands *)

Inductive comp : Type := 
  | CpAtom : atom -> comp
  | CpArraySet : atom -> atom -> atom -> btyp -> comp
  | CpRecordUpdate : atom -> ident -> atom -> btyp -> comp
  | CpCall : ident -> btyp -> list atom -> btyp -> comp.

Definition btypof_comp (c: comp) : btyp :=
  match c with
  | CpAtom a => btypof_atom a
  | CpArraySet _ _ _ ty
  | CpRecordUpdate _ _ _ ty
  | CpCall _ _ _ ty => ty
  end.

Section PROGRAMS.

  Variable BODY : Type.
  Variable TYP : Type.
  Variable LIT : Type.

  Record function : Type := mk_function {
    fn_return : TYP;
    fn_params : list (ident * TYP);
    fn_body : BODY
  }.

  Inductive param_attr :=
    | AttrReadonly
    | AttrWrite
    | AttrNone.

  Inductive globdef : Type :=
    | DefConst : ident -> LIT -> TYP -> globdef
    | DefFun : ident -> function -> globdef
    | DeclConst : ident -> TYP -> globdef
    | DeclFun : ident -> list (param_attr * TYP) -> TYP -> globdef.

  Definition globdef_id (def: globdef) : ident :=
    match def with
    | DefConst x _ _
    | DefFun x _
    | DeclConst x _
    | DeclFun x _ _ => x
    end.

  Inductive struct_or_union : Type :=
    | SU_struct
    | SU_union.

  Inductive type_def (T: Type) : Type :=
    | TdEnum : list ident -> type_def T
    | TdRecord : smaplist T -> type_def T.

  Definition get_enum_typedefs {T} (types: smaplist (type_def T)) : smaplist (list ident) :=
  MapList.fold_right
    (fun tid td acc =>
      match td with
      | TdEnum _ elems => cons (tid, elems) acc
      | _ => acc
      end)
    nil
    types.

  Definition get_record_typedefs  {T} (types: smaplist (type_def T)) : smaplist (smaplist T) :=
    MapList.fold_right
      (fun tid td acc =>
        match td with
        | TdRecord _ fields => cons (tid, fields) acc
        | _ => acc
        end)
      nil
      types.

  Record program : Type := mk_program {
    prog_defs : list globdef;
    prog_types : smaplist (type_def (TYP * layout));
    prog_tabs : smaplist struct_or_union;
  }.

End PROGRAMS.

Arguments mk_function {BODY TYP}.
Arguments fn_return {BODY TYP}.
Arguments fn_params {BODY TYP}.
Arguments fn_body {BODY TYP}.

Arguments DefConst {BODY TYP LIT}.
Arguments DefFun {BODY TYP LIT}.
Arguments DeclConst {BODY TYP LIT}.
Arguments DeclFun {BODY TYP LIT}.

Arguments globdef_id {BODY TYP LIT}.

Arguments TdEnum {T}.
Arguments TdRecord {T}.

Arguments mk_program {BODY TYP LIT}.
Arguments prog_defs {BODY TYP LIT}.
Arguments prog_types {BODY TYP LIT}.
Arguments prog_tabs {BODY TYP LIT}.

From Stdlib Require Import OrderedType.
From Stdlib Require Import Datatypes.
From Stdlib Require Import ZArith.

Definition comparison_dec (x y : comparison): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition function_dec {B T: Type}
  (b_dec : forall (b1 b2:B), {b1 = b2} + { b1 <> b2})
  (t_dec : forall (t1 t2:T), {t1 = t2} + { t1 <> t2})
  (f1 f2: function B T) :  {f1 = f2} + {f1 <> f2}.
Proof.
  decide equality.
  apply list_eq_dec.
  decide equality.
  apply eq_dec.
Defined.


Module IntOrderded.

  Definition compare_int (i1 i2:int) := Z.compare (Int.unsigned i1) (Int.unsigned i2).
  Definition compare_int64 (i1 i2:int64) := Z.compare (Int64.unsigned i1) (Int64.unsigned i2).

  Lemma compare_int_eq :forall i1 i2,
      compare_int i1 i2 = Eq <-> i1 = i2.
  Proof.
    unfold compare_int.
    intros.
    split ; intro.
    rewrite Z.compare_eq_iff in H.
    unfold Int.unsigned in *.
    destruct i1,i2.
    simpl in H.
    subst.
    f_equal.
    destruct intrange,intrange0.
    f_equal.
    apply Eqdep_dec.UIP_dec.
    apply comparison_dec.
    apply Eqdep_dec.UIP_dec.
    apply comparison_dec.
    subst.
    apply Z.compare_refl.
  Qed.

  Lemma compare_int64_eq :forall i1 i2,
      compare_int64 i1 i2 = Eq <-> i1 = i2.
  Proof.
    unfold compare_int64.
    intros.
    split ; intro.
    rewrite Z.compare_eq_iff in H.
    unfold Int64.unsigned in *.
    destruct i1,i2.
    simpl in H.
    subst.
    f_equal.
    destruct intrange,intrange0.
    f_equal.
    apply Eqdep_dec.UIP_dec.
    apply comparison_dec.
    apply Eqdep_dec.UIP_dec.
    apply comparison_dec.
    subst.
    apply Z.compare_refl.
  Qed.

  Lemma compare_int_trans : forall i i0 i1,
    forall c : comparison, compare_int i i0 = c -> compare_int i0 i1 = c -> compare_int i i1 = c.
  Proof.
    unfold compare_int.
    intros i i0 i1 c.
    destruct c.
    - rewrite ! Z.compare_eq_iff.
      congruence.
    - rewrite ! Z.compare_lt_iff.
      lia.
    - rewrite ! Z.compare_gt_iff.
      lia.
  Qed.

  Lemma compare_int64_trans : forall i i0 i1,
    forall c : comparison, compare_int64 i i0 = c -> compare_int64 i0 i1 = c -> compare_int64 i i1 = c.
  Proof.
    unfold compare_int64.
    intros i i0 i1 c.
    destruct c.
    - rewrite ! Z.compare_eq_iff.
      congruence.
    - rewrite ! Z.compare_lt_iff.
      lia.
    - rewrite ! Z.compare_gt_iff.
      lia.
  Qed.

  Lemma compare_int_antisym : forall i i0,
      compare_int i i0 = CompOpp (compare_int i0 i).
  Proof.
    unfold compare_int.
    intros.
    apply Z.compare_antisym.
  Qed.

  Lemma compare_int64_antisym : forall i i0,
      compare_int64 i i0 = CompOpp (compare_int64 i0 i).
  Proof.
    unfold compare_int64.
    intros.
    apply Z.compare_antisym.
  Qed.


End IntOrderded.


Module AtomOrdered <: OrderedType.
  Import IntOrderded.

  Definition unary_op_compare (o1 o2:unary_op) : comparison :=
    match o1 , o2 with
    | UopNotbool , UopNotbool => Eq
    | UopNotbool , _ => Lt
    | _ , UopNotbool  => Gt
    | UopNotint , UopNotint => Eq
    | UopNotint , _ => Lt
    | _ , UopNotint  => Gt
    | UopNeg , UopNeg => Eq
    | UopNeg , _ => Lt
    | _ , UopNeg  => Gt
    | UopPlus , UopPlus => Eq
    end.

  Definition binary_op_positive (o:binary_op) : positive :=
    (match o with
    | BopAndbool => 1
    | BopOrbool => 2
    | BopXorbool => 3
    | BopAdd => 4
    | BopSub => 5
    | BopMul => 6
    | BopDiv => 7
    | BopMod => 8
    | BopAndint => 9
    | BopOrint => 10
    | BopXorint => 11
    | BopShl => 12
    | BopShr => 13
    | BopEq => 14
    | BopNeq => 15
    | BopLt => 16
    | BopGt => 17
    | BopLe => 18
    | BopGe => 19
    end)%positive.

  Lemma unary_op_compare_eq : forall o1 o2,
      unary_op_compare o1 o2 = Eq <-> o1 = o2.
  Proof.
    destruct o1,o2; simpl ; intuition congruence.
  Qed.

  Definition unary_op_dec (o1 o2:unary_op) : {o1 = o2} + {o1 <> o2}.
  Proof.
    decide equality.
  Qed.

  Lemma unary_op_compare_trans : forall x y z c,
      unary_op_compare x y = c -> unary_op_compare y z = c -> unary_op_compare x z = c.
  Proof.
    destruct x,y,z; simpl; intuition congruence.
  Qed.

  Definition binary_op_compare (o1 o2:binary_op) : comparison :=
    Pos.compare (binary_op_positive o1) (binary_op_positive o2).

  Lemma binary_op_compare_eq : forall o1 o2,
      binary_op_compare o1 o2 = Eq <-> o1 = o2.
  Proof.
    unfold binary_op_compare.
    split ; intros.
    rewrite Pos.compare_eq_iff in H.
    destruct o1,o2 ; simpl in *; intuition congruence.
    subst.
    apply Pos.compare_refl.
  Qed.

  Definition binary_op_dec (o1 o2:binary_op) : {o1 = o2} + {o1 <> o2}.
  Proof.
    decide equality.
  Qed.

  Lemma binary_op_compare_trans : forall x y z c,
      binary_op_compare x y = c -> binary_op_compare y z = c -> binary_op_compare x z = c.
  Proof.
    unfold binary_op_compare.
    intros x y z c.
    destruct c.
    -  rewrite! Pos.compare_eq_iff.
       congruence.
    -  rewrite! Pos.compare_lt_iff.
       lia.
    -  rewrite! Pos.compare_gt_iff.
       lia.
  Qed.

  Lemma unary_op_compare_antisym : forall x y,
      unary_op_compare x y = CompOpp (unary_op_compare y x).
  Proof.
    destruct x,y; reflexivity.
  Qed.

  Lemma binary_op_compare_antisym : forall x y,
      binary_op_compare x y = CompOpp (binary_op_compare y x).
  Proof.
    destruct x,y; reflexivity.
  Qed.

  Fixpoint atom_compare (t1 t2: atom) : comparison :=
    match t1 , t2 with
    | ATrue, ATrue => Eq
    | ATrue,   _       => Lt
    | _         , ATrue => Gt
    | AFalse, AFalse => Eq
    | AFalse,   _       => Lt
    | _         , AFalse   => Gt
    | AInt32 i1 s1 , AInt32 i2 s2 => pair_compare compare_int signedness_compare (i1,s1) (i2,s2)
    | AInt32 _ _    , _      => Lt
    | _             , AInt32 _ _ => Gt
    | AInt64 i1 s1 , AInt64 i2 s2 => pair_compare compare_int64 signedness_compare (i1,s1)  (i2,s2)
    | AInt64 _ _    , _      => Lt
    | _             , AInt64 _ _ => Gt
    | AConstr c1 n1 bt1 , AConstr c2 n2 bt2 =>
        pair_compare (pair_compare Ident.compare compare_int)
          BtypOrdered.btyp_compare ((c1, n1), bt1) ((c2, n2), bt2)
    | AConstr _ _ _   ,  _          => Lt
    | _             , AConstr _ _ _ => Gt
    | AVar i1 bt1, AVar i2 bt2  => pair_compare Ident.compare BtypOrdered.btyp_compare (i1,bt1) (i2,bt2)
    | AVar _  _  , _            => Lt
    | _          , AVar _   _   => Gt
    | ACast a1 bt1 , ACast a2 bt2 => pair_compare atom_compare BtypOrdered.btyp_compare (a1,bt1) (a2,bt2)
    | ACast _  _   , _            => Lt
    | _            , ACast _ _    => Gt
    | AUnaryOp o1 a1 t1 , AUnaryOp o2 a2 t2 =>
        pair_compare (pair_compare unary_op_compare atom_compare) BtypOrdered.btyp_compare ((o1,a1),t1) ((o2,a2),t2)
    | AUnaryOp _ _ _, _ => Lt
    | _, AUnaryOp _ _ _ => Gt
    | ABinaryOp o1 a1 b1 t1, ABinaryOp o2 a2 b2 t2 =>
        pair_compare (pair_compare binary_op_compare atom_compare)
          (pair_compare atom_compare BtypOrdered.btyp_compare)  ((o1,a1),(b1,t1)) ((o2,a2),(b2,t2))
    | ABinaryOp _ _ _ _ , _ => Lt
    | _ , ABinaryOp _ _ _ _ => Gt
    | AArrayGet a1 i1 ly1 ta1, AArrayGet a2 i2 ly2 ta2 =>
        pair_compare (pair_compare atom_compare atom_compare)
          (pair_compare layout_compare BtypOrdered.btyp_compare ) ((a1, i1), (ly1, ta1)) ((a2, i2), (ly2, ta2))
    | AArrayGet _ _ _ _, _ => Lt
    | _, AArrayGet _ _ _ _ => Gt
    | ARecordProj a1 f1 ly1 tr1, ARecordProj a2 f2 ly2 tr2 =>
        pair_compare (pair_compare atom_compare Ident.compare)
          (pair_compare layout_compare BtypOrdered.btyp_compare) ((a1, f1), (ly1, tr1)) ((a2, f2), (ly2, tr2))
    | ARecordProj _ _ _ _, _ => Lt
    | _, ARecordProj _ _ _ _ => Gt
    | APureCall f1 bf1 args1 br1, APureCall f2 bf2 args2 br2 =>
        pair_compare (pair_compare Ident.compare BtypOrdered.btyp_compare)
          (pair_compare (list_compare atom_compare) (BtypOrdered.btyp_compare))
            ((f1, bf1), (args1, br1)) ((f2, bf2), (args2, br2))
    end.

  Definition t := atom.

  Definition eq : t -> t -> Prop := @eq t.

  Definition lt : t -> t -> Prop := fun x y => atom_compare x y = Lt.

  Lemma eq_refl : forall (x:t), x = x.
  Proof. reflexivity. Qed.

  Lemma eq_sym : forall (x y:t), x = y -> y = x.
  Proof. congruence. Qed.

  Lemma eq_trans : forall (x y z:t), x = y -> y = z -> x = z.
  Proof. congruence. Qed.

  Lemma atom_compare_eq : forall x y,
      atom_compare x y = Eq <-> x = y.
  Proof.
    induction x using atom_depth_ind.
    - destruct y; simpl; try intuition congruence.
    - destruct y; simpl; try intuition congruence.
    - destruct y; simpl; try intuition congruence.
      rewrite pair_compare_eq. intuition congruence.
      apply compare_int_eq.
      apply signedness_compare_eq.
    - destruct y; simpl; try intuition congruence.
      rewrite pair_compare_eq. intuition congruence.
      apply compare_int64_eq.
      apply signedness_compare_eq.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq. intuition congruence.
      apply pair_compare_eq.
      rewrite Ident.compare_eq.
      reflexivity.
      apply compare_int_eq.
      apply BtypOrdered.btyp_compare_eq.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq. intuition congruence.
      rewrite Ident.compare_eq.
      intuition congruence.
      rewrite BtypOrdered.btyp_compare_eq. tauto.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq. intuition congruence.
      rewrite IHx. tauto.
      apply BtypOrdered.btyp_compare_eq.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq. intuition congruence.
      rewrite pair_compare_eq. intuition congruence.
      apply unary_op_compare_eq.
      apply IHx.
      apply BtypOrdered.btyp_compare_eq.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq.
      intuition congruence.
      apply pair_compare_eq.
      apply binary_op_compare_eq.
      apply IHx1.
      apply pair_compare_eq.
      apply IHx2.
      apply BtypOrdered.btyp_compare_eq.
    - destruct y; simpl; try intuition congruence.
      rewrite pair_compare_eq. intuition congruence.
      rewrite pair_compare_eq. reflexivity.
      apply IHx1. apply IHx2.
      apply pair_compare_eq.
      apply layout_compare_eq.
      apply BtypOrdered.btyp_compare_eq.
    - destruct y; simpl; try intuition congruence.
      rewrite pair_compare_eq. intuition congruence.
      rewrite pair_compare_eq. reflexivity.
      apply IHx. apply Ident.compare_eq.
      apply pair_compare_eq.
      apply layout_compare_eq.
      apply BtypOrdered.btyp_compare_eq.
    - destruct y; simpl; try intuition congruence.
      rewrite pair_compare_eq. intuition congruence.
      rewrite pair_compare_eq. reflexivity.
      apply Ident.compare_eq.
      apply BtypOrdered.btyp_compare_eq.
      rewrite pair_compare_eq. reflexivity.
      apply list_compare_eq. intros.
      apply (H x H0).
      apply BtypOrdered.btyp_compare_eq.
  Qed.

  Lemma atom_compare_refl : forall x,
      atom_compare x x = Eq.
  Proof.
    intros.
    rewrite atom_compare_eq.
    reflexivity.
  Qed.

  Lemma atom_compare_trans : forall x y z c,
      atom_compare x y = c -> atom_compare y z = c -> atom_compare x z = c.
  Proof.
    induction x using atom_depth_ind.
    - simpl.
      destruct y,z; simpl; try intuition congruence.
    - destruct y,z; simpl; try intuition congruence.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      apply compare_int_eq.
      apply compare_int_trans.
      apply signedness_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      apply compare_int64_eq.
      apply compare_int64_trans.
      apply signedness_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      destruct a, b1.
      apply pair_compare_eq.
      apply Ident.compare_eq.
      apply compare_int_eq.
      apply pair_compare_trans.
      apply Ident.compare_eq.
      apply Ident.compare_trans.
      apply compare_int_trans.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      apply Ident.compare_eq.
      apply Ident.compare_trans.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      apply atom_compare_eq.
      apply IHx.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      destruct a ,b1.
      rewrite pair_compare_eq.
      tauto.
      apply unary_op_compare_eq.
      apply atom_compare_eq.
      intro.
      apply pair_compare_trans.
      apply unary_op_compare_eq.
      apply unary_op_compare_trans.
      apply IHx.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      intros a b5.
      destruct a,b5.
      rewrite pair_compare_eq.
      tauto.
      apply binary_op_compare_eq.
      apply atom_compare_eq.
      intro.
      apply pair_compare_trans.
      apply binary_op_compare_eq.
      apply binary_op_compare_trans.
      apply IHx1.
      apply pair_compare_trans.
      intros a b5.
      apply atom_compare_eq.
      intro.
      apply IHx2.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y, z; simpl; try intuition congruence.
      apply pair_compare_trans.
      destruct a, b1.
      apply pair_compare_eq.
      apply atom_compare_eq.
      apply atom_compare_eq.
      apply pair_compare_trans.
      apply atom_compare_eq.
      apply IHx1.
      apply IHx2.
      apply pair_compare_trans.
      apply layout_compare_eq.
      apply layout_compare_trans.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y, z; simpl; try intuition congruence.
      apply pair_compare_trans.
      destruct a, b1.
      apply pair_compare_eq.
      apply atom_compare_eq.
      apply Ident.compare_eq.
      apply pair_compare_trans.
      apply atom_compare_eq.
      apply IHx.
      apply Ident.compare_trans.
      apply pair_compare_trans.
      apply layout_compare_eq.
      apply layout_compare_trans.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y, z; simpl; try intuition congruence.
      apply pair_compare_trans.
      destruct a. destruct b4.
      apply pair_compare_eq.
      apply Ident.compare_eq.
      apply BtypOrdered.btyp_compare_eq.
      apply pair_compare_trans.
      apply Ident.compare_eq.
      apply Ident.compare_trans.
      apply BtypOrdered.btyp_compare_trans.
      apply pair_compare_trans.
      intros a b3. apply list_compare_eq.
      intros. apply atom_compare_eq.
      intro c.
      apply ExtOrdered.list_compare_trans.
      apply atom_compare_eq.
      intros. apply (H _ H0 _ _ _ H3 H4).
      apply BtypOrdered.btyp_compare_trans.
  Qed.

  Lemma atom_antisym  : forall (x y:t), atom_compare x y = CompOpp (atom_compare y x).
  Proof.
    induction x using atom_depth_ind.
    - destruct y; simpl; try congruence.
    - destruct y ; simpl; try congruence.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply compare_int_antisym.
      apply signedness_compare_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply compare_int64_antisym.
      apply signedness_compare_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      apply pair_compare_antisym.
      apply Ident.compare_antisym.
      apply compare_int_antisym.
      apply BtypOrdered.btyp_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      apply Ident.compare_antisym.
      apply BtypOrdered.btyp_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      apply IHx.
      apply BtypOrdered.btyp_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply pair_compare_antisym.
      simpl.
      apply unary_op_compare_antisym.
      apply IHx.
      apply BtypOrdered.btyp_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply pair_compare_antisym.
      simpl.
      apply binary_op_compare_antisym.
      apply IHx1.
      apply pair_compare_antisym.
      simpl.
      apply IHx2.
      apply BtypOrdered.btyp_antisym.
    - destruct y; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply pair_compare_antisym.
      apply IHx1.
      apply IHx2.
      apply pair_compare_antisym.
      apply layout_compare_antisym.
      apply BtypOrdered.btyp_antisym.
    - destruct y; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply pair_compare_antisym.
      simpl.
      apply IHx.
      simpl.
      apply Ident.compare_antisym.
      apply pair_compare_antisym.
      apply layout_compare_antisym.
      apply BtypOrdered.btyp_antisym.
    - destruct y; simpl; try congruence; simpl.
      apply pair_compare_antisym.
      apply pair_compare_antisym.
      apply Ident.compare_antisym.
      apply BtypOrdered.btyp_antisym.
      apply pair_compare_antisym.
      apply ExtOrdered.list_compare_antisym.
      apply atom_compare_eq.
      simpl.
      intros. eapply H; eauto.
      apply BtypOrdered.btyp_antisym.
  Qed.



  Definition lt_trans  (x y z:t): lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    apply atom_compare_trans.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> eq x y -> False.
  Proof.
    unfold lt. intros.
    unfold eq in H0. subst.
    rewrite atom_compare_refl in H. discriminate.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    destruct (atom_compare x y) eqn:TC.
    - apply EQ. rewrite atom_compare_eq in TC. apply TC.
    - apply LT;auto.
    - apply GT.
      rewrite atom_antisym in TC.
      unfold lt.
      destruct (atom_compare y x); try discriminate.
      reflexivity.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {x <> y}.
  Proof.
    destruct (atom_compare x y) eqn:EQB.
    - left. apply atom_compare_eq in EQB. auto.
    - right. intro.
      subst. rewrite atom_compare_refl in EQB. discriminate.
    - right. intro.
      subst. rewrite atom_compare_refl in EQB. discriminate.
  Qed.

  (** vars *)

  Fixpoint vars_of_atom (a:atom) : list ident :=
    match a with
    | ATrue | AFalse | AInt32 _ _ | AInt64 _ _ | AConstr _ _ _  =>  nil
    | AVar i _ => i :: nil
    | ACast a _ => vars_of_atom a
    | AUnaryOp _  a _ => vars_of_atom a
    | ABinaryOp _ a1 a2 _ => vars_of_atom a1 ++ vars_of_atom a2
    | AArrayGet a1 a2 _ _ => vars_of_atom a1 ++ vars_of_atom a2
    | ARecordProj a1 _ _ _ => vars_of_atom a1
    | APureCall id _ l _   => id :: List.fold_right (fun e acc => vars_of_atom e ++ acc) nil l
    end.

End AtomOrdered.
