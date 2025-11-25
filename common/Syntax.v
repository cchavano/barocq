From Coq Require Import Lia.
From compcert Require Import Integers Ctypes.
From BarocqComp Require Import Utils Ident Types Maps2 ExtOrdered.

Definition ident := Ident.ident.

(** * Constant literals *)

Inductive literal :=
  | LTrue : literal
  | LFalse  : literal
  | LInt32 : int -> signedness -> literal
  | LInt64 : int64 -> signedness -> literal
  | LArray : list literal -> btyp -> layout -> literal
  | LRecord : smaplist literal -> list ident -> ident -> literal.

(** * Operators *)

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

(** * Atoms *)

(** Atoms are pure computations in C *)

(* Inductive atom : Type :=
  | ATrue : atom
  | AFalse : atom
  | AInt32 : int -> signedness -> atom
  | AInt64 : int64 -> signedness -> atom
  | AConstr : ident -> atom
  | AVar : ident -> atom
  | ACast : atom -> btyp -> atom
  | AUnaryOp : unary_op -> atom -> atom
  | ABinaryOp : binary_op -> atom -> atom -> atom. *)

Inductive atom : Type :=
  | ATrue : atom
  | AFalse : atom
  | AInt32 : int -> signedness -> atom
  | AInt64 : int64 -> signedness -> atom
  | AConstr : ident -> atom
  | AVar : ident -> atom
  | ACast : atom -> btyp -> atom
  | AUnaryOp : unary_op -> atom -> atom
  | ABinaryOp : binary_op -> atom -> atom -> atom
  | AArrayGet : atom -> atom -> atom
  | ARecordProj : atom -> ident -> atom.

(** Deep accesses with atomics array indexes. *)

(* Inductive access : Type :=
  | AcRecordField : ident -> access
  | AcArrayIndex : atom -> access. *)

(** * Computations with atomic operands *)

Inductive comp : Type := 
  | CpAtom : atom -> comp
  (* | CpArrayGet : atom -> atom -> comp *)
  | CpArraySet : atom -> atom -> atom -> comp
  (* | CpRecordProj : atom -> ident -> comp *)
  | CpRecordUpdate : atom -> ident -> atom -> comp
  (* | CpDeepAccess : atom -> list access -> comp *)
  | CpCall : ident -> list atom -> comp.

(** * Typed syntax *)

Module Typed.

  Inductive atom :=
    | ATrue : atom
    | AFalse : atom
    | AInt32 : int -> signedness -> atom
    | AInt64 : int64 -> signedness -> atom
    | AConstr : ident -> btyp -> atom
    | AVar : ident -> btyp -> atom
    | ACast : atom -> btyp -> atom
    | AUnaryOp : unary_op -> atom -> btyp -> atom
    | ABinaryOp : binary_op -> atom -> atom -> btyp -> atom
    | AArrayGet : atom -> atom -> layout -> btyp -> atom
    | ARecordProj : atom -> ident -> layout -> btyp -> atom.

  Inductive access : Type :=
    | AcRecordField : ident -> btyp -> layout -> access
    | AcArrayIndex : atom -> btyp -> layout -> access.

  Inductive comp : Type := 
    | CpAtom : atom -> btyp -> comp
    (* | CpArrayGet : atom -> atom -> btyp -> layout -> comp *)
    | CpArraySet : atom -> atom -> atom -> btyp -> comp
    (* | CpRecordProj : atom -> ident -> btyp -> layout -> comp *)
    | CpRecordUpdate : atom -> ident -> atom -> btyp -> comp
    (* | CpDeepAccess : atom -> list access -> btyp -> comp *)
    | CpCall : ident -> btyp -> list atom -> btyp -> comp.

End Typed.

(** * Syntax shared by some of the intermediate representations. *)

(** ** Functions *)

Record function (B T: Type) : Type := mk_function {
  fn_return : T;
  fn_params : list (ident * T);
  fn_body : B
}.

(** ** Global definitions *)

Inductive param_attr :=
  | AttrReadonly
  | AttrWrite
  | AttrNone.

Inductive globdef (L F T: Type) : Type :=
  | DefConst : ident -> L -> T -> globdef L F T
  | DefFun : ident -> F -> globdef L F T
  | DeclConst : ident -> T -> globdef L F T
  | DeclFun : ident -> list (param_attr * T) -> T -> globdef L F T.

(** ** Programs *)

Inductive struct_or_union : Type :=
  | SU_struct
  | SU_union.

Inductive type_def (T: Type) : Type :=
  | TdEnum : list ident -> type_def T
  | TdRecord : smaplist T -> type_def T.

Arguments TdEnum {T}.
Arguments TdRecord {T}.

Record program (G T: Type) : Type := mk_program {
  prog_defs : list G;
  prog_types : smaplist (type_def T);
  prog_tabs : smaplist struct_or_union;
}.

Definition get_enum_typedefs {T} (types: smaplist (type_def T)) : smaplist (list ident) :=
  MapList.fold_right
    (fun tid td acc =>
      match td with
      | TdEnum elems => cons (tid, elems) acc
      | _ => acc
      end)
    nil
    types.

Definition get_record_typedefs {T} (types: smaplist (type_def T)) : smaplist (smaplist T) :=
  MapList.fold_right
    (fun tid td acc =>
      match td with
      | TdRecord fields => cons (tid, fields) acc
      | _ => acc
      end)
    nil
    types.

Arguments DefConst {L} {F} {T}.
Arguments DefFun {L} {F} {T}.
Arguments DeclConst {L} {F} {T}.
Arguments DeclFun {L} {F} {T}.

Arguments mk_function {B} {T}.
Arguments fn_return {B} {T}.
Arguments fn_params {B} {T}.
Arguments fn_body {B} {T}.

Arguments mk_program {G T}.
Arguments prog_defs {G T}.
Arguments prog_types {G T}.
Arguments prog_tabs {G T}.

Require Import OrderedType.
Require Import Datatypes.
Require Import ZArith.

Definition comparison_dec (x y : comparison): {x = y} + {x <> y}.
Proof.
  decide equality.
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
  Import Typed.
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

  Fixpoint atom_compare (t1 t2:Typed.atom) : comparison :=
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
    | AConstr i1 bt1 , AConstr i2 bt2 => pair_compare String.compare BtypOrdered.btyp_compare (i1,bt1) (i2,bt2)
    | AConstr _ _   ,  _          => Lt
    | _             , AConstr _ _ => Gt
    | AVar i1 bt1, AVar i2 bt2  => pair_compare String.compare BtypOrdered.btyp_compare (i1,bt1) (i2,bt2)
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
    end.

  Definition t := Typed.atom.

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
    induction x.
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
      rewrite string_compare_eq_iff.
      intuition congruence.
      rewrite BtypOrdered.btyp_compare_eq. tauto.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq. intuition congruence.
      rewrite string_compare_eq_iff.
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
      apply IHx. apply string_compare_eq_iff.
      apply pair_compare_eq.
      apply layout_compare_eq.
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
    induction x.
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
      apply string_compare_eq_iff.
      apply string_compare_trans.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      apply string_compare_eq_iff.
      apply string_compare_trans.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      apply atom_compare_eq.
      apply IHx.
      apply BtypOrdered.btyp_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply pair_compare_trans.
      destruct a ,b2.
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
      destruct a, b2.
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
      destruct a, b2.
      apply pair_compare_eq.
      apply atom_compare_eq.
      apply string_compare_eq_iff.
      apply pair_compare_trans.
      apply atom_compare_eq.
      apply IHx.
      apply string_compare_trans.
      apply pair_compare_trans.
      apply layout_compare_eq.
      apply layout_compare_trans.
      apply BtypOrdered.btyp_compare_trans.
  Qed.

  Lemma atom_antisym  : forall (x y:t), atom_compare x y = CompOpp (atom_compare y x).
  Proof.
    induction x.
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
      apply String.compare_antisym.
      apply BtypOrdered.btyp_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      apply String.compare_antisym.
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
      apply String.compare_antisym.
      apply pair_compare_antisym.
      apply layout_compare_antisym.
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

End AtomOrdered.
