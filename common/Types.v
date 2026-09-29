From Stdlib Require Import ZArith List MSetPositive Bool.
From compcert Require Import Coqlib Integers Maps.
From BarocqComp Require Import Res Barray Brecord Benum Ident Maps2 Utils.
From Stdlib Require Import Datatypes List MSetPositive Lia.
From BarocqComp Require Import ExtOrdered.
From BarocqComp Require Import Option.
Local Open Scope option_monad_scope.

(** * Syntax of types *)

(** ** Plain types *)

Inductive signedness : Type :=  
  | Signed
  | Unsigned.

Lemma signedness_eq_dec: forall (s1 s2: signedness), {s1 = s2} + {s1 <> s2}.
Proof.
  intros. destruct s1; destruct s2.
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.

Inductive typ : Type :=
  | TUnit : typ
  | TBool : typ
  | TInt32 : signedness -> typ
  | TInt64 : signedness -> typ
  | TArray : typ -> typ
  | TEnum : ident -> list ident -> typ
  | TRecord : option ident -> list (ident * typ) -> typ
  | TFun : list typ -> typ -> typ
  | TAbs : ident -> typ.

Definition typ_is_prim (ty: typ) : bool :=
  match ty with
  | TBool | TInt32 _ | TInt64 _ | TEnum _ _ => true
  | _ => false
  end.

(* [no_TFun t] holds it there are to function types *)
Fixpoint no_TFun (t:typ) :=
  match t with
  | TFun _ _ => false
  | TArray t => no_TFun t
  | TRecord _ l => List.forallb (fun x => no_TFun (snd x)) l
  | _  => true
  end.

(* [fo_typ t] holds if there are no higher-order types.
   i.e function do not take functions as arguments *)
Definition fo_typ (t:typ) :=
  match t with
  | TFun l r => List.forallb no_TFun l && no_TFun r
  | TArray t => no_TFun t
  | TRecord _ l => List.forallb (fun x => no_TFun (snd x)) l
  |   _         => true
  end.

  Lemma no_TFun_fo_typ (ty:typ):  no_TFun ty = true -> fo_typ ty = true.
  Proof.
    destruct ty; simpl; auto; try discriminate.
  Qed.


Fixpoint typ_eq_dec (t1 t2: typ) : { t1 = t2 } + { t1 <> t2 }.
Proof.
  decide equality.
  - apply signedness_eq_dec.
  - apply signedness_eq_dec.
  - apply list_eq_dec. apply Ident.eq_dec. 
  - apply Ident.eq_dec.
  - apply list_eq_dec. decide equality. apply Ident.eq_dec.
  - apply option_eq_dec.
    apply Ident.eq_dec.
  - apply list_eq_dec. apply typ_eq_dec.
  - apply Ident.eq_dec.
Defined.

Fixpoint typ_depth (t:typ) : nat :=
  match t with
  | TUnit
  | TBool
  | TInt32 _  | TInt64 _ => O
  | TArray ty => S (typ_depth ty)
  | TEnum _ _ => O
  | TRecord _ l => S (List.fold_right (fun e acc => max (typ_depth (snd e)) acc) 0%nat l)
  | TFun l r    => S (List.fold_right (fun e acc => max (typ_depth e) acc) (typ_depth r) l)
  | TAbs _ => O
  end.

Section TYPIND.
  Variable P : typ -> Prop.

  Variable PTUnit : P TUnit.

  Variable PTBool : P TBool.

  Variable PTInt32 : forall s, P (TInt32 s).

  Variable PTInt64 : forall s, P (TInt64 s).

  Variable PTEnun : forall i l, P (TEnum i l).

  Variable PTAbs : forall i , P (TAbs i).

  Variable PTArray : forall t, P t -> P (TArray t).

  Variable PTRecord : forall i l, (forall x, In x l -> P (snd x)) -> P (TRecord i l).

  Variable PTFun : forall l r, (forall x, In x l -> P x) -> P r -> P (TFun l r).

  Lemma typ_depth_ind : forall t, P t.
  Proof.
    intro.
    remember (typ_depth t) as n.
    revert t Heqn.
    induction n using Wf_nat.lt_wf_ind.
    destruct n.
    - destruct t; try discriminate; auto.
    - destruct t; try discriminate; auto;
      simpl;intros.
      +  apply PTArray.
         apply H with (m:=n). lia. congruence.
      + apply PTRecord.
        intros.
        apply H with (m:=typ_depth (snd x));auto.
        rewrite Heqn.
        clear - H0.
        { induction l.
          - simpl in H0. tauto.
          - simpl.
            simpl in H0.
            destruct H0; subst.
            +  lia.
            + apply IHl in H.
              lia.
        }
      +  apply PTFun.
         intros.
        apply H with (m:=typ_depth x);auto.
        rewrite Heqn.
        clear - H0.
        { induction l.
          - simpl in H0. tauto.
          - simpl.
            simpl in H0.
            destruct H0; subst.
            +  lia.
            + apply IHl in H.
              lia.
        }
        apply H with (m:= typ_depth t);auto.
        rewrite Heqn.
        clear.
        induction l.
        simpl. lia.
        simpl. lia.
  Qed.

End TYPIND.

Definition signedness_compare (s1 s2:signedness) :=
  match s1 , s2 with
  | Signed , Signed => Eq
  | Signed , _      => Lt
  |  _     , Signed => Gt
  | Unsigned , Unsigned => Eq
  end.

Definition signedness_eqb (s1 s2: signedness) : bool:=
  match s1 , s2 with
  | Unsigned , Unsigned => true
  | Signed , Signed => true
  | _ , _ => false
  end.

Lemma signedness_compare_eq : forall s1 s2,
    signedness_compare s1 s2 = Eq <-> s1 = s2.
Proof.
  destruct s1,s2; simpl; intuition try congruence.
Qed.

Lemma signedness_compare_trans : forall s1 s2 s3,
  forall c, signedness_compare s1 s2 = c -> signedness_compare s2 s3 = c -> signedness_compare s1 s3 = c.
Proof. destruct s1,s2,s3; simpl; congruence. Qed.

Lemma signedness_compare_antisym : forall s1 s2,
  signedness_compare s1 s2 = CompOpp (signedness_compare s2 s1).
Proof.
  destruct s1, s2; reflexivity.
Qed.

Fixpoint typ_compare (t1 t2:typ) :=
  match t1 , t2 with
  | TUnit , TUnit => Eq
  | TUnit , _     => Lt
  | _     , TUnit => Gt
  | TBool , TBool => Eq
  | TBool ,  _    => Lt
  |   _   , TBool => Gt
  | TInt32 s , TInt32 s' =>  signedness_compare s s'
  | TInt32 _ , _         => Lt
  | _        , TInt32 _  => Gt
  | TInt64 s , TInt64 s' => signedness_compare s s'
  | TInt64 _ , _         => Lt
  | _        , TInt64 _  => Gt
  | TArray t1 , TArray t2 => typ_compare t1 t2
  | TArray _  ,   _       => Lt
  | _         , TArray _  => Gt
  | TEnum id1 l1 , TEnum id2 l2 => pair_compare String.compare (list_compare String.compare) (id1,l1) (id2,l2)
  | TEnum _ _ , _   => Lt
  | _ , TEnum _ _   => Gt
  | TRecord i1 l1 , TRecord i2 l2 =>
      pair_compare (option_compare String.compare) (list_compare (pair_compare String.compare typ_compare)) (i1,l1) (i2,l2)
  | TRecord _ _ , _ => Lt
  | _ , TRecord _ _ => Gt
  | TFun l1 t1 , TFun l2 t2 => pair_compare (list_compare typ_compare) typ_compare (l1,t1) (l2,t2)
  | TFun _ _   , _   => Lt
  | _ , TFun  _ _    => Gt
  | TAbs id1 , TAbs id2 => String.compare id1 id2
  end.

Fixpoint typ_eqb (t1 t2:typ) :=
  match t1 , t2 with
  | TUnit , TUnit => true
  | TBool , TBool => true
  | TInt32 s1 , TInt32 s2 => signedness_eqb s1 s2
  | TInt64 s1 , TInt64 s2 => signedness_eqb s1 s2
  | TArray t1 , TArray t2 => typ_eqb t1 t2
  | TEnum i1 l1 ,  TEnum i2 l2 => pair_eqb String.eqb (forall2b String.eqb) (i1,l1) (i2,l2)
  | TRecord i1 l1 , TRecord i2 l2 => pair_eqb (option_eqb String.eqb)
                                       (forall2b (pair_eqb String.eqb typ_eqb)) (i1,l1) (i2,l2)
  | TFun a1 r1 , TFun a2 r2 => pair_eqb typ_eqb (forall2b typ_eqb) (r1,a1) (r2,a2)
  | TAbs i1 , TAbs i2 => String.eqb i1 i2
  | _ , _ => false
  end.

Lemma signedness_eqb_true : forall s s',
    signedness_eqb s s' = true <-> s =  s'.
Proof.
  destruct s, s'; simpl; intuition congruence.
Qed.

Lemma typ_eqb_true : forall (t1 t2:typ), typ_eqb t1 t2 = true <-> t1 = t2.
Proof.
  induction t1 using  typ_depth_ind;
    destruct t2; unfold typ_eqb ; try intuition congruence.
  - rewrite signedness_eqb_true; intuition congruence.
  - rewrite signedness_eqb_true; intuition congruence.
  - rewrite pair_eqb_eq.
    intuition congruence.
    apply String.eqb_eq.
    intros.
    apply forall2b_eqb_eq.
    intros.
    apply String.eqb_eq.
  - rewrite String.eqb_eq.
    intuition  congruence.
  - fold typ_eqb.
    rewrite IHt1. intuition congruence.
  - fold typ_eqb.
    rewrite pair_eqb_eq.
    intuition congruence.
    intros. simpl.  apply option_eqb_eq.
    intros. apply String.eqb_eq.
    intros.
    apply forall2b_eqb_eq.
    intros.
    apply pair_eqb_eq; intros.
    apply String.eqb_eq.
    apply H; auto.
  - fold typ_eqb.
    rewrite pair_eqb_eq.
    intuition congruence.
    simpl. apply IHt1.
    simpl. apply forall2b_eqb_eq.
    intros; auto.
Qed.

Lemma typ_compare_eq :
  forall (t1:typ) (t2:typ), typ_compare t1 t2 = Eq <-> t1 = t2.
Proof.
  induction t1 using typ_depth_ind.
  - destruct t2 ; simpl; intuition congruence.
  - destruct t2 ; simpl; intuition congruence.
  - destruct t2 ; simpl; try intuition congruence.
    rewrite signedness_compare_eq. intuition congruence.
  - destruct t2 ; simpl; try intuition congruence.
    rewrite signedness_compare_eq. intuition congruence.
  - destruct t2 ; simpl; try intuition congruence.
    rewrite pair_compare_eq. intuition congruence.
    apply string_compare_eq.
    apply list_compare_eq.
    intros. apply string_compare_eq.
  - destruct t2 ; simpl ; try intuition congruence.
    rewrite string_compare_eq.
    intuition congruence.
  - destruct t2 ; simpl ; try intuition congruence.
    rewrite IHt1. intuition congruence.
  - destruct t2 ; simpl ; try intuition congruence.
    rewrite pair_compare_eq.
    intuition congruence.
    apply option_compare_eq.
    apply string_compare_eq.
    apply list_compare_eq.
    intros.
    destruct x,y.
    apply pair_compare_eq.
    apply string_compare_eq.
    change t with (snd (s,t)).
    apply H; auto.
  - destruct t2 ; simpl ; try intuition congruence.
    rewrite pair_compare_eq.
    intuition congruence.
    apply list_compare_eq.
    intros.
    apply H; auto.
    apply IHt1;auto.
Qed.


(** ** Concrete types *)

Inductive layout : Type :=
  | LyPrim : layout
  | LyBoxed : layout
  | LyUnboxed : option Z -> layout.


Definition layout_eqb (l1 l2:layout) :=
  match l1, l2 with
  | LyPrim , LyPrim
  | LyBoxed , LyBoxed => true
  | LyUnboxed z1 , LyUnboxed z2 => ExtOrdered.option_eqb Z.eqb z1 z2
  | _ , _ => false
  end.


Definition layout_eq_dec (b1 b2: layout) : { b1 = b2 } + { b1 <> b2 }.
Proof.
  destruct b1; destruct b2;
  try ((left; reflexivity) || (right; discriminate)).
  decide equality. decide equality. apply Z.eq_dec.
Defined.

Definition layout_compare (ly1 ly2: layout) : comparison :=
  match ly1, ly2 with
  | LyPrim, LyPrim
  | LyBoxed, LyBoxed => Eq
  | LyPrim, _ => Lt
  | _, LyPrim => Gt
  | LyBoxed, _ => Lt
  | _, LyBoxed => Gt
  | LyUnboxed None, LyUnboxed None => Eq
  | LyUnboxed None, LyUnboxed (Some _) => Lt
  | LyUnboxed (Some _), LyUnboxed None => Gt
  | LyUnboxed (Some z1), LyUnboxed (Some z2) => Z.compare z1 z2
  end.

Lemma layout_compare_eq :
  forall (ly1 ly2: layout),
  layout_compare ly1 ly2 = Eq <-> ly1 = ly2.
Proof.
  destruct ly1; destruct ly2; simpl;
  try (split; (discriminate || reflexivity)).
  - destruct o; split; discriminate.
  - destruct o; split; discriminate.
  - destruct o; destruct o0; try (split; discriminate).
    intuition. apply Z.compare_eq in H. congruence.
    inversion H. apply Z.compare_refl.
    split; reflexivity.
Qed.

Lemma layout_compare_antisym  : forall (x y: layout), layout_compare x y = CompOpp (layout_compare y x).
Proof.
  destruct x; destruct y; simpl;
  try reflexivity.
  - destruct o; reflexivity.
  - destruct o; reflexivity.
  - destruct o; reflexivity.
  - destruct o; reflexivity.
  - destruct o; destruct o0; try reflexivity.
    apply Z.compare_antisym.
Qed.

From Stdlib Require Import Lia.

Lemma layout_compare_trans:
  forall (ly1 ly2 ly3: layout) (c: comparison),
  layout_compare ly1 ly2 = c -> layout_compare ly2 ly3 = c -> layout_compare ly1 ly3 = c.
Proof.
  destruct ly1; destruct ly2; destruct ly3; try congruence; intros;
  simpl in H; simpl in H0.
  - subst. discriminate.
  - destruct o; simpl; congruence.
  - destruct o; simpl; congruence.
  - destruct o; simpl; congruence. 
  - destruct o; destruct o0; simpl; congruence.
  - congruence.
  - destruct o; congruence.
  - destruct o; congruence.
  - destruct o; congruence.
  - destruct o; destruct o0; simpl; congruence.
  - destruct o; congruence.
  - destruct o; destruct o0; simpl; congruence.
  - destruct o; simpl; congruence.
  - destruct o; destruct o0; congruence.
  - destruct o; destruct o0; simpl; congruence.
  - destruct o; destruct o0; simpl; congruence.
  - destruct o; destruct o0; destruct o1; simpl; try congruence.
    destruct c. apply Z.compare_eq in H. apply Z.compare_eq in H0. subst. apply Z.compare_refl.
    apply (Zcompare_Lt_trans _ _ _ H H0).
    apply (Zcompare_Gt_trans _ _ _ H H0).
Qed.

Inductive btyp : Type :=
  | BBool : btyp
  | BInt32 : signedness -> btyp
  | BInt64 : signedness -> btyp
  | BArray : btyp -> layout -> btyp
  | BEnum  : ident -> btyp
  | BRecord : ident -> list ident -> btyp (* we register the list of unboxed fields *)
  | BActR   : list (ident * btyp) -> btyp (* Activation record, for typing loop body *)
  | BFun : list btyp -> btyp -> btyp
  | BAbs : ident -> btyp.

Definition btyp_is_prim (ty: btyp) : bool :=
  match ty with
  | BBool | BInt32 _ | BInt64 _ | BEnum _ => true
  | _ => false
  end.

Definition btyp_is_int (ty: btyp) : bool :=
  match ty with
  | BInt32 _ | BInt64 _  => true
  | _ => false
  end.


Definition field_descr : Type := btyp * layout.

Fixpoint btyp_eq_dec (t1 t2: btyp) : { t1 = t2 } + { t1 <> t2 }.
Proof.
  decide equality.
  - apply signedness_eq_dec.
  - apply signedness_eq_dec.
  - apply layout_eq_dec.
  - apply Ident.eq_dec.
  - apply list_eq_dec. apply Ident.eq_dec.
  - apply Ident.eq_dec.
  - apply list_eq_dec.
    apply pair_eq_dec. exact Ident.eq_dec.
    exact btyp_eq_dec.
  - apply list_eq_dec. apply btyp_eq_dec.
  - apply Ident.eq_dec.
Defined.

Definition btyp_eqb (t1 t2: btyp) : bool :=
  if btyp_eq_dec t1 t2 then true else false.

Lemma btyp_eqb_eq:
  forall (t1 t2: btyp), btyp_eqb t1 t2 = true <-> t1 = t2.
Proof.
  intros. unfold btyp_eqb; split;
  destruct (btyp_eq_dec t1 t2); intros;
  (tauto || discriminate).
Qed.

Fixpoint btyp_depth (t:btyp) : nat :=
  match t with
  | BBool
  | BInt32 _
  | BInt64 _ => O
  | BArray t' _ => S (btyp_depth t')
  | BEnum _ => O
  | BRecord _ _ => O
  | BActR  l    => S (List.fold_right (fun e acc => max (btyp_depth (snd e)) acc) O l)
  | BFun l t' => S (List.fold_right (fun e acc => max (btyp_depth e) acc) (btyp_depth t') l)
  | BAbs _ => O
  end.

Section BTYPIND.
  Variable P : btyp -> Prop.

  Variable PBBool : P BBool.

  Variable PBInt32 : forall s, P (BInt32 s).

  Variable PBInt64 : forall s, P (BInt64 s).

  Variable PBEnun : forall i, P (BEnum i).

  Variable PBAbs : forall i , P (BAbs i).

  Variable PBArray : forall t ly, P t -> P (BArray t ly).

  Variable PBRecord : forall i ub, P (BRecord i ub).

  Variable PBActR : forall l, (forall x, In x l -> P (snd x)) -> P (BActR l).

  Variable PBFun : forall l r, (forall x, In x l -> P x) -> P r -> P (BFun l r).

  Lemma btyp_depth_ind : forall t, P t.
  Proof.
    intro.
    remember (btyp_depth t) as n.
    revert t Heqn.
    induction n using Wf_nat.lt_wf_ind.
    destruct n.
    - destruct t; try discriminate; auto.
    - destruct t; try discriminate; auto;
      simpl;intros.
      +  apply PBArray.
         apply H with (m:=n). lia. congruence.
      +  apply PBActR.
         intros.
         apply H with (m:= btyp_depth (snd x)); auto.
         rewrite Heqn.
         clear - H0.
         {
           induction l.
          - simpl in H0. tauto.
          - simpl.
            simpl in H0.
            destruct H0; subst.
            +  lia.
            + apply IHl in H.
              lia.
        }
      +  apply PBFun.
         intros.
        apply H with (m:=btyp_depth x);auto.
        rewrite Heqn.
        clear - H0.
        { induction l.
          - simpl in H0. tauto.
          - simpl.
            simpl in H0.
            destruct H0; subst.
            +  lia.
            + apply IHl in H.
              lia.
        }
        apply H with (m:= btyp_depth t);auto.
        rewrite Heqn.
        clear.
        induction l.
        simpl. lia.
        simpl. lia.
  Qed.

End BTYPIND.



Definition mk_fun_btyp {A: Type} (params: list (A * btyp)) (tret: btyp) : btyp :=
  BFun (List.map snd params) tret.

(** * Type of a record field *)

Definition typof_field (k: ident) (fields: smaplist typ) : option typ :=
  find_err Ident.eq_dec k fields.

Definition btypof_field (k: ident) (fields: smaplist btyp) : option btyp :=
  find_err Ident.eq_dec k fields.

Definition is_index_btyp (ty: btyp) : bool :=
  match ty with
  | BInt32 Unsigned | BInt64 Unsigned => true
  | _ => false
  end.

Definition is_index_typ (ty: typ) : bool :=
  match ty with
  | TInt32 Unsigned | TInt64 Unsigned => true
  | _ => false
  end.

(** extraction of types *)
Definition typof_array (ty:typ) :=
  match ty with
  | TArray te => Some te
  | _         => fail
  end.

Definition typof_record (ty:typ) :=
  match ty with
  | TRecord _ te => Some te
  | _         => fail
  end.


(** * Conversion of a typ to a Coq Type *)

Section EVALTYP.

  Polymorphic Variable eval_typ : typ -> Type.

  Polymorphic Definition eval_recordtyp (fields: smaplist typ) : Type :=
    grecord eval_typ fields.

  Polymorphic Fixpoint eval_funtyp (tparams: list typ) (tret: Type) : Type :=
    match tparams with
    | nil => unit -> (option tret)
    | tx:: tparams' => eval_typ tx -> match tparams' with
                                      | nil => option tret
                                      |  _  => eval_funtyp tparams' tret
                                      end
    end.

  (* Should have its own library, eventually - also look at WhileLib.v *)

  Polymorphic Fixpoint eval_tuple (tparams: list typ) : Type :=
    match tparams with
    | nil => unit
    | tx::tparams' => match tparams' with
                      | nil => eval_typ tx
                      |  _  => eval_typ tx * eval_tuple tparams'
                      end
    end.


End EVALTYP.

Polymorphic Fixpoint eval_typ (am: PMap.t Type) (t: typ) {struct t}: Type :=
  match t with
  | TUnit => unit
  | TBool => bool
  | TInt32 _ => int
  | TInt64 _ => int64
  | TArray ta => array (eval_typ am ta)
  | TRecord _ fields => eval_recordtyp (eval_typ am) fields
  | TEnum _ elems => enum elems
  | TFun tparams tret => eval_funtyp (eval_typ am) tparams (eval_typ am tret)
  | TAbs ta => SMap.get ta am
  end.

(* From Stdlib Require Import List String.

Import ListNotations.

Open Scope string_scope.

Compute (eval_typ (PMap.init (unit: Type)) (TRecord "point" [("x", TInt32 Signed); ("y", TInt64 Signed)])). *)

(** ** Type cast w.r.t. type equality *)

Definition typ_cast (am: SMap.t Type) {t1 t2: typ}  (Heq: t1 = t2) (x: eval_typ am t1) : eval_typ am t2 :=
  cast (f_equal (eval_typ am) Heq) x.

Remark typ_cast_id:
  forall t am (x: eval_typ am t),
  typ_cast am eq_refl x = x.
Proof.
  reflexivity.
Qed.

(** Ordered Type *)
From Stdlib Require Import OrderedType.

Module TypeOrderedCmp <: OrderedCompare.
  (* Using directly a comparison function. *)
  Definition t := typ.

  Definition depth := typ_depth.

  Definition compare := typ_compare.

  Lemma compare_antisym  : forall x y, compare x y = CompOpp (compare y x).
  Proof.
    induction x using typ_depth_ind.
    - destruct y; simpl; try congruence.
    - destruct y; simpl; try congruence.
    - destruct y ; simpl; try congruence.
      destruct s,s0; reflexivity.
    - destruct y ; simpl; try congruence.
      destruct s,s0; reflexivity.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      apply String.compare_antisym.
      intros. simpl.
      apply ExtOrdered.list_compare_antisym.
      apply string_compare_eq.
      intros.
      apply String.compare_antisym.
    - destruct y ; simpl; try congruence.
      apply String.compare_antisym.
    - destruct y ; simpl; try congruence.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      intros.
      simpl.
      apply option_compare_antisym.
      destruct i,o; simpl;auto.
      apply String.compare_antisym.
      apply ExtOrdered.list_compare_antisym.
      intros.
      destruct x,y.
      apply pair_compare_eq.
      apply string_compare_eq.
      apply typ_compare_eq.
      intros.
      apply pair_compare_antisym.
      apply String.compare_antisym.
      apply H;auto.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply ExtOrdered.list_compare_antisym.
      apply typ_compare_eq.
      intros.
      apply H;auto.
      simpl.
      apply IHx.
  Qed.


  Lemma compare_trans : forall x y z c,
      (compare x y = c -> compare y z = c -> compare x z = c).
  Proof.
    induction x using typ_depth_ind.
    - destruct y; simpl; try congruence;
        destruct z; simpl; try intuition congruence.
    - destruct y; simpl; try  congruence;
        destruct z; simpl; try intuition congruence.
    - destruct y ; simpl; try congruence;
        destruct z; simpl; try intuition congruence.
      apply signedness_compare_trans.
    - destruct y ; simpl; try congruence;
        destruct z; simpl; try intuition congruence.
      apply signedness_compare_trans.
    -
      destruct y ; simpl; try congruence;
        destruct z; simpl; try intuition congruence.
      intro c.
      { apply pair_compare_trans.
        apply string_compare_eq.
        apply string_compare_trans.
        intro.
        apply ExtOrdered.list_compare_trans.
        apply string_compare_eq.
        intros x y z c1 _ _ _.
        apply string_compare_trans.
      }
    - destruct y ; simpl; try congruence;
        destruct z; simpl; try intuition congruence.
      intro  c.
      apply string_compare_trans.
    - destruct y ; simpl; try congruence;
        destruct z; simpl; try intuition congruence.
      apply IHx.
    - destruct y ; simpl; try congruence;
        destruct z; simpl; try intuition congruence.
      intro.
      apply pair_compare_trans.
      intros x y.
      apply option_compare_eq.
      apply string_compare_eq.
      intro.
      apply option_compare_trans.
      apply string_compare_trans.
      intro.
      apply ExtOrdered.list_compare_trans.
      intros x y.
      destruct x,y; apply pair_compare_eq.
      apply string_compare_eq.
      apply typ_compare_eq.
      intros x y z c1 I1 I2 I3.
      apply pair_compare_trans.
      apply string_compare_eq.
      apply string_compare_trans.
      apply H; auto.
    - destruct y ; simpl; try congruence;
        destruct z; try congruence.
      apply pair_compare_trans.
      intros.
      apply list_compare_eq in H0;auto.
      intros.
      apply typ_compare_eq.
      intro.
      apply ExtOrdered.list_compare_trans.
      apply typ_compare_eq.
      intros x0 y0 z0 c' I1 I2 I3;auto.
      apply H; auto.
      apply IHx.
  Qed.

  Lemma compare_eq :forall t1 t2, compare t1 t2 = Eq <-> t1 = t2.
  Proof. apply typ_compare_eq. Qed.



End  TypeOrderedCmp.


Module TypOrdered <: OrderedType.
  Include ExtOrdered.MakeEq(TypeOrderedCmp).

  Definition depth := typ_depth.



End TypOrdered.

  Fixpoint btyp_compare (x y:btyp) : comparison :=
     match x , y with
     | BBool , BBool => Eq
     | BBool ,  _    => Lt
     |  _    , BBool => Gt
     | BInt32 s1 , BInt32 s2 => signedness_compare s1 s2
     | BInt32 _  ,   _       => Lt
     |  _        , BInt32 _  => Gt
     | BInt64 s1 , BInt64 s2 => signedness_compare s1 s2
     | BInt64 _  ,   _       => Lt
     |  _        , BInt64 _  => Gt
     | BArray bt1 ly1 , BArray bt2 ly2 => pair_compare btyp_compare layout_compare (bt1, ly1) (bt2, ly2)
     | BArray  _ _  , _          => Lt
     | _          , BArray _ _   => Gt
     | BEnum i1 , BEnum i2     => String.compare i1 i2
     | BEnum _  , _            => Lt
     | _        , BEnum  _     => Gt
     | BRecord i1 ub1 , BRecord i2 ub2 => pair_compare String.compare (list_compare Ident.compare) (i1, ub1) (i2, ub2)
     | BRecord _ _ , _          => Lt
     | _          , BRecord _ _ => Gt
     | BActR l1   , BActR l2    => list_compare (pair_compare Ident.compare btyp_compare) l1 l2
     | BActR _    , _           => Lt
     | _          , BActR _     => Gt
     | BFun l1 t1 , BFun l2 t2 => pair_compare (list_compare btyp_compare) btyp_compare (l1,t1) (l2,t2)
     | BFun _  _  , _          => Lt
     | _          , BFun _ _   => Gt

     | BAbs i , BAbs  j => String.compare i j
     end.

Module BtypOrderedCmp <: OrderedCompare.

  Definition t := btyp.


  Definition compare := btyp_compare.


  Lemma compare_eq : forall x y,
      compare x y = Eq <-> x = y.
  Proof.
    induction x using btyp_depth_ind.
    - destruct y; simpl; intuition congruence.
    - destruct y; simpl; try intuition  congruence.
      rewrite signedness_compare_eq.
      intuition congruence.
    - destruct y; simpl; try intuition  congruence.
      rewrite signedness_compare_eq.
      intuition congruence.
    - destruct y; simpl; try intuition  congruence.
      rewrite string_compare_eq.
      intuition congruence.
    - destruct y; simpl; try intuition  congruence.
      rewrite string_compare_eq.
      intuition congruence.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq.
      intuition congruence.
      exact (IHx y).
      apply layout_compare_eq.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq.
      intuition congruence.
      rewrite string_compare_eq. tauto.
      rewrite list_compare_eq. tauto.
      intros. apply string_compare_eq.
    - destruct y; simpl; try intuition congruence.
      rewrite list_compare_eq. intuition congruence.
      intros.  destruct x as [x1 x2].
      destruct y as [y1 y2].
      rewrite pair_compare_eq. intuition congruence.
      rewrite string_compare_eq. tauto.
      apply H with (y:= y2) in H0.
      apply H0.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq.
      intuition congruence.
      apply list_compare_eq;auto.
      apply IHx.
  Qed.

  Lemma compare_trans : forall x y z c,
      btyp_compare x y = c -> btyp_compare y z = c -> btyp_compare x z = c.
  Proof.
    induction x using btyp_depth_ind.
    - simpl.
      destruct y,z; simpl; try intuition congruence.
    - destruct y,z; simpl; try intuition congruence.
      apply signedness_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply signedness_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply string_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      apply string_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      intros. erewrite pair_compare_trans with (a2 := y) (b2 := l) (c := c); eauto.
      apply compare_eq.
      apply layout_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      intros. erewrite pair_compare_trans with (a2 := i0) (b2 := l) (c := c); eauto.
      apply string_compare_eq.
      apply string_compare_trans.
      intros. erewrite ExtOrdered.list_compare_trans; eauto.
      apply string_compare_eq.
      intros. apply (string_compare_trans _ _ _ _ H6 H7).
      congruence.
    - destruct y,z; simpl;try intuition congruence.
      intro.
      apply ExtOrdered.list_compare_trans.
      intros. destruct x, y; rewrite pair_compare_eq.
      tauto. apply string_compare_eq.
      apply compare_eq.
      intros until 3.
      apply pair_compare_trans.
      apply string_compare_eq.
      apply string_compare_trans.
      intro. apply H; auto.
    - destruct y,z; simpl; try intuition congruence.
      intro.
      apply pair_compare_trans.
      intros a b.
      rewrite list_compare_eq; auto.
      intros.
      apply compare_eq.
      intro.
      apply ExtOrdered.list_compare_trans.
      intros.
      apply compare_eq.
      intros x0 y0 z0 c1 I1 I2 I3.
      apply H; auto.
      apply IHx.
  Qed.

  Lemma compare_antisym  : forall (x y:t), compare x y = CompOpp (compare y x).
  Proof.
    induction x using btyp_depth_ind.
    - destruct y; simpl; try congruence.
    - destruct y ; simpl; try congruence.
      destruct s,s0; reflexivity.
    - destruct y ; simpl; try congruence.
      destruct s,s0; reflexivity.
    - destruct y ; simpl; try congruence.
      apply String.compare_antisym.
    - destruct y ; simpl; try congruence.
      apply String.compare_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl. apply IHx.
      apply layout_compare_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl. apply String.compare_antisym.
      apply list_compare_antisym.
      apply string_compare_eq.
      intros. apply String.compare_antisym.
    - destruct y ; simpl; try congruence.
      apply ExtOrdered.list_compare_antisym.
      { intros x y; apply pair_compare_eq.
      apply string_compare_eq.
      apply compare_eq.
      }
      intros.
      apply pair_compare_antisym.
      apply String.compare_antisym.
      apply H; auto.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply ExtOrdered.list_compare_antisym.
      intros.
      apply compare_eq.
      intros.
      apply H;auto.
      simpl.
      apply IHx.
  Qed.

End BtypOrderedCmp.


Module BtypOrdered := ExtOrdered.Make(BtypOrderedCmp).
