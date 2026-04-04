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
  | TBool : typ
  | TInt32 : signedness -> typ
  | TInt64 : signedness -> typ
  | TArray : typ -> typ
  | TEnum : ident -> list ident -> typ
  | TRecord : ident -> list (ident * typ) -> typ
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
  - apply Ident.eq_dec.
  - apply list_eq_dec. apply typ_eq_dec.
  - apply Ident.eq_dec.
Defined.

Fixpoint typ_depth (t:typ) : nat :=
  match t with
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
      pair_compare String.compare (list_compare (pair_compare String.compare typ_compare)) (i1,l1) (i2,l2)
  | TRecord _ _ , _ => Lt
  | _ , TRecord _ _ => Gt
  | TFun l1 t1 , TFun l2 t2 => pair_compare (list_compare typ_compare) typ_compare (l1,t1) (l2,t2)
  | TFun _ _   , _   => Lt
  | _ , TFun  _ _    => Gt
  | TAbs id1 , TAbs id2 => String.compare id1 id2
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
  - destruct (String.eqb i i0) eqn:EQ ; try discriminate.
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
      destruct (String.eqb i1 i2) eqn:EQ1 ; try discriminate.
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


(** ** Concrete types *)

Inductive layout : Type :=
  | LyPrim : layout
  | LyBoxed : layout
  | LyUnboxed : option Z -> layout.

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
  | BEnum : ident -> btyp
  | BRecord : ident -> list ident -> btyp (* we register the list of unboxed fields *)
  | BFun : list btyp -> btyp -> btyp
  | BAbs : ident -> btyp.

Definition btyp_is_prim (ty: btyp) : bool :=
  match ty with
  | BBool | BInt32 _ | BInt64 _ | BEnum _ => true
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

End EVALTYP.

Polymorphic Fixpoint eval_typ (am: PMap.t Type) (t: typ) {struct t}: Type :=
  match t with
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

Module TypOrdered <: OrderedType.
  Definition t := typ.


  Definition depth := typ_depth.
  Definition eq : t -> t -> Prop := @eq t.
  Definition lt : t -> t -> Prop := fun x y => typ_compare x y = Lt.

  Lemma eq_refl : forall (x:t), x = x.
  Proof. reflexivity. Qed.

  Lemma eq_sym : forall (x y:t), x = y -> y = x.
  Proof. congruence. Qed.

  Lemma eq_trans : forall (x y z:t), x = y -> y = z -> x = z.
  Proof. congruence. Qed.

  Lemma typ_compare_eq : forall (x y:typ),
      typ_compare x y = Eq <-> x = y.
  Proof.
    induction x using typ_depth_ind; destruct y; simpl; try intuition congruence.
    - intros. rewrite signedness_compare_eq.
      intuition congruence.
    - intros. rewrite signedness_compare_eq.
      intuition congruence.
    - intros.
      rewrite pair_compare_eq.
      intuition congruence.
      rewrite string_compare_eq_iff.
      tauto.
      apply list_compare_eq.
      intros.
      apply string_compare_eq_iff.
    -  intros. rewrite string_compare_eq_iff.
       intuition congruence.
    - rewrite IHx. intuition congruence.
    -
      intros.
      rewrite pair_compare_eq.
      intuition congruence.
      rewrite string_compare_eq_iff.
      tauto.
      rewrite list_compare_eq.
      tauto.
      intros.
      destruct x,y.
      rewrite pair_compare_eq.
      intuition congruence.
      rewrite string_compare_eq_iff.
      tauto.
      apply H with (y:= t1) in H0.
      simpl in H0. tauto.
    - rewrite pair_compare_eq.
      intuition congruence.
      rewrite list_compare_eq.
      tauto.
      auto.
      auto.
  Qed.


  Lemma typ_compare_refl  : forall (x:t), typ_compare x x = Eq.
  Proof.
    intros.
    rewrite typ_compare_eq.
    reflexivity.
  Qed.


    
  Lemma typ_eq_trans  : forall (x y z:t), forall c, typ_compare x y = c -> typ_compare y z = c  -> typ_compare x z = c.
  Proof.
    induction x using typ_depth_ind.
    - destruct y; simpl; try congruence;
        destruct z; try congruence.
    - destruct y ; simpl; try congruence;
        destruct z; try congruence.
      apply signedness_compare_trans.
    - destruct y ; simpl; try congruence;
        destruct z; try congruence.
      apply signedness_compare_trans.
    - destruct y ; simpl; try congruence;
        destruct z; try congruence.
      apply pair_compare_trans.
      intros. rewrite string_compare_eq_iff in H.
      auto.
      apply string_compare_trans.
      intro.
      apply ExtOrdered.list_compare_trans.
      apply string_compare_eq_iff.
      intros x y z c0 I1 I2 I3.
      apply string_compare_trans.
    - destruct y ; simpl; try congruence;
        destruct z; try congruence.
      apply string_compare_trans.
    - destruct y ; simpl; try congruence;
        destruct z; try congruence.
      intro.
      apply IHx.
    - destruct y ; simpl; try congruence;
        destruct z; try congruence.
      apply pair_compare_trans.
      intros a v. rewrite string_compare_eq_iff.
      congruence.
      apply string_compare_trans.
      intro.
      apply ExtOrdered.list_compare_trans.
      intros.
      destruct x,y;
      rewrite pair_compare_eq.
      tauto.
      apply string_compare_eq_iff.
      apply typ_compare_eq.
      intros x y z c' I1 I2 I3.
      destruct x, y, z.
      apply pair_compare_trans.
      intros. rewrite string_compare_eq_iff in *. auto.
      apply string_compare_trans.
      change t0 with (snd (s,t0)).
      apply H.
      auto.
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

  Lemma typ_antisym  : forall (x y:t), typ_compare x y = CompOpp (typ_compare y x).
  Proof.
    induction x using typ_depth_ind.
    - destruct y; simpl; try congruence.
    - destruct y ; simpl; try congruence.
      destruct s,s0; reflexivity.
    - destruct y ; simpl; try congruence.
      destruct s,s0; reflexivity.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      apply String.compare_antisym.
      intros.
      apply ExtOrdered.list_compare_antisym.
      apply string_compare_eq_iff.
      intros.
      apply String.compare_antisym.
    - destruct y ; simpl; try congruence.
      apply String.compare_antisym.
    - destruct y ; simpl; try congruence.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      intros.
      apply String.compare_antisym.
      intros.
      apply ExtOrdered.list_compare_antisym.
      intros.
      destruct x,y.
      apply pair_compare_eq.
      apply string_compare_eq_iff.
      apply typ_compare_eq.
      intros.
      apply pair_compare_antisym.
      apply String.compare_antisym.
      apply H;auto.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply ExtOrdered.list_compare_antisym.
      intros.
      apply typ_compare_eq.
      intros.
      apply H;auto.
      simpl.
      apply IHx.
  Qed.

  Definition lt_trans  (x y z:t): lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    apply typ_eq_trans.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> eq x y -> False.
  Proof.
    unfold lt. intros.
    unfold eq in H0. subst.
    rewrite typ_compare_refl in H. discriminate.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    destruct (typ_compare x y) eqn:TC.
    - apply EQ. rewrite typ_compare_eq in TC. apply TC.
    - apply LT;auto.
    - apply GT.
      rewrite typ_antisym in TC.
      unfold lt.
      destruct (typ_compare y x); try discriminate.
      reflexivity.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {x <> y}.
  Proof.
    destruct (typ_compare x y) eqn:EQB.
    - left. apply typ_compare_eq in EQB. auto.
    - right. intro.
      subst. rewrite typ_compare_refl in EQB. discriminate.
    - right. intro.
      subst. rewrite typ_compare_refl in EQB. discriminate.
  Qed.

End TypOrdered.

Module BtypOrdered <: OrderedType.

  Definition t := btyp.

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
     | BFun l1 t1 , BFun l2 t2 => pair_compare (list_compare btyp_compare) btyp_compare (l1,t1) (l2,t2)
     | BFun _  _  , _          => Lt
     | _          , BFun _ _   => Gt

     | BAbs i , BAbs  j => String.compare i j
     end.

  Definition eq : t -> t -> Prop := @eq t.
  Definition lt : t -> t -> Prop := fun x y => btyp_compare x y = Lt.

  Lemma eq_refl : forall (x:t), x = x.
  Proof. reflexivity. Qed.

  Lemma eq_sym : forall (x y:t), x = y -> y = x.
  Proof. congruence. Qed.

  Lemma eq_trans : forall (x y z:t), x = y -> y = z -> x = z.
  Proof. congruence. Qed.

  Lemma btyp_compare_eq : forall x y,
      btyp_compare x y = Eq <-> x = y.
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
      rewrite string_compare_eq_iff.
      intuition congruence.
    - destruct y; simpl; try intuition  congruence.
      rewrite string_compare_eq_iff.
      intuition congruence.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq.
      intuition congruence.
      exact (IHx y).
      apply layout_compare_eq.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq.
      intuition congruence.
      rewrite string_compare_eq_iff. tauto.
      rewrite list_compare_eq. tauto.
      intros. apply string_compare_eq_iff.
    - destruct y; simpl; try intuition  congruence.
      rewrite pair_compare_eq.
      intuition congruence.
      apply list_compare_eq;auto.
      apply IHx.
  Qed.

  Lemma btyp_compare_refl : forall x,
      btyp_compare x x = Eq.
  Proof.
    intros.
    rewrite btyp_compare_eq.
    reflexivity.
  Qed.

  Lemma btyp_compare_trans : forall x y z c,
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
      apply btyp_compare_eq.
      apply layout_compare_trans.
    - destruct y,z; simpl; try intuition congruence.
      intros. erewrite pair_compare_trans with (a2 := i0) (b2 := l) (c := c); eauto.
      apply string_compare_eq_iff.
      apply string_compare_trans.
      intros. erewrite ExtOrdered.list_compare_trans; eauto.
      apply string_compare_eq_iff.
      intros. apply (string_compare_trans _ _ _ _ H6 H7).
      congruence.
    - destruct y,z; simpl; try intuition congruence.
      intro.
      apply pair_compare_trans.
      intros a b.
      rewrite list_compare_eq; auto.
      intros.
      apply btyp_compare_eq.
      intro.
      apply ExtOrdered.list_compare_trans.
      intros.
      apply btyp_compare_eq.
      intros x0 y0 z0 c1 I1 I2 I3.
      apply H; auto.
      apply IHx.
  Qed.

  Lemma btyp_antisym  : forall (x y:t), btyp_compare x y = CompOpp (btyp_compare y x).
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
      apply string_compare_eq_iff.
      intros. apply String.compare_antisym.
    - destruct y ; simpl; try congruence.
      apply pair_compare_antisym.
      simpl.
      apply ExtOrdered.list_compare_antisym.
      intros.
      apply btyp_compare_eq.
      intros.
      apply H;auto.
      simpl.
      apply IHx.
  Qed.



  Definition lt_trans  (x y z:t): lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    apply btyp_compare_trans.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> eq x y -> False.
  Proof.
    unfold lt. intros.
    unfold eq in H0. subst.
    rewrite btyp_compare_refl in H. discriminate.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    destruct (btyp_compare x y) eqn:TC.
    - apply EQ. rewrite btyp_compare_eq in TC. apply TC.
    - apply LT;auto.
    - apply GT.
      rewrite btyp_antisym in TC.
      unfold lt.
      destruct (btyp_compare y x); try discriminate.
      reflexivity.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {x <> y}.
  Proof.
    destruct (btyp_compare x y) eqn:EQB.
    - left. apply btyp_compare_eq in EQB. auto.
    - right. intro.
      subst. rewrite btyp_compare_refl in EQB. discriminate.
    - right. intro.
      subst. rewrite btyp_compare_refl in EQB. discriminate.
  Qed.


End BtypOrdered.

