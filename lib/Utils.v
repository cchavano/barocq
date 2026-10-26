From Stdlib Require Import PArith ZArith String DecimalString List Bool MSetPositive.
From compcert Require Import Coqlib Ctypesdefs Maps Integers.
From BarocqComp  Require Import Unsigned63 ZifyUint63.
From BarocqComp Require Import StateMonads Res Option Ident ZlistPlus.
From BarocqComp Require Export Utils0.
Local Open Scope error_monad_scope.
Local Open Scope option_monad_scope.
Import MonCounter.
Import MonCounterErr.
Import ListNotations.


(** * Identifiers *)

Open Scope state_monad_scope.

Definition fresh_var (pre: string) : cmon ident :=
  do n <- MonCounter.incr;
  MonCounter.sret (Ident.concat pre (Ident.of_str_pos n)).

Close Scope state_monad_scope.

Open Scope state_err_monad_scope.

Definition fresh_var_err (pre: string) : crmon ident :=
  do n <- MonCounterErr.incr;
  MonCounterErr.sret (Ident.concat pre (Ident.of_str_pos n)).

Close Scope state_err_monad_scope.

Definition cast_enum {A: Type} (l:list A) (z: Z) : option A :=
  list_nth_z l z.

Lemma cast_enum_Some : forall {A: Type} (l:list A) (z: Z),
    0 <= z < Zlength l ->
    exists v, cast_enum l z = Some v.
Proof.
  intros.
  unfold cast_enum.
  destruct (list_nth_z l z) eqn:GET.
  eexists ; split; eauto.
  rewrite <- list_nth_z_Some in H. congruence.
Qed.

(** * Lists *)

Lemma nth_error_map_same :
  forall (A B: Type) (f: A -> B) (l: list A) (n: nat),
  nth_error (map f l) n =
    let* x := (nth_error  l n) in
    (Some (f x)).
Proof.
  induction l; destruct n.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. apply (IHl n).
Qed.

Definition list_nth_err {A: Type} (l:list A) (n:nat) : res A :=
  Res.of_opt (List.nth_error l n).

Fixpoint list_fold_left_err_compat {A B: Type} (f: A -> B -> option A) (l: list B) (a0: option A) : option A :=
  match l with
  | nil => a0
  | x :: l' =>
      let* a0 := a0 in
      list_fold_left_err_compat f l' (f a0 x)
  end.

Fixpoint list_fold_left_err {A B: Type} (f: A -> B -> res A) (l: list B) (a0: A) : res A :=
  match l with
  | nil => eret a0
  | x :: l' =>
      do acc <- f a0 x;
      list_fold_left_err f l' acc
  end.

Lemma list_fold_left_err_ext:
  forall {A B: Type} (f g: A -> B -> res A),
  (forall a b, f a b = g a b) ->
  forall (l: list B) (a0: A), list_fold_left_err f l a0 = list_fold_left_err g l a0.
Proof.
  induction l; intros.
  - simpl. reflexivity.
  - simpl.
    rewrite H.
    destruct (g a0 a); try reflexivity. simpl.
    apply IHl.
Qed.

Fixpoint list_fold_right_err {A B: Type} (f: B -> A -> res A) (a0: A) (l: list B) : res A :=
  match l with
  | nil => OK a0
  | x :: l' =>
      do r <- list_fold_right_err f a0 l';
      f x r
  end.

Lemma list_fold_right_err_ext:
  forall {A B: Type} (f g: B -> A -> res A),
  (forall b a, f b a = g b a) ->
  forall (l: list B) (a0: A), list_fold_right_err f a0 l = list_fold_right_err g a0 l.
Proof.
  induction l; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHl.
    destruct (list_fold_right_err g a0 l); simpl; try reflexivity.
    apply H.
Qed.

Lemma list_fold_right_err_ext_OK:
  forall {A B: Type} (f g: B -> A -> res A),
  (forall b a r, f b a = OK r -> g b a = OK r) ->
  forall (l: list B) (a0: A) (r: A),
    list_fold_right_err f a0 l = OK r ->
    list_fold_right_err g a0 l = OK r.
Proof.
  induction l; intros.
  - simpl in H0. simpl. exact H0.
  - simpl. simpl in H0.
    Res.monadInv H0.
    rewrite IHl with (r := x); simpl. apply H.
    exact EQ0. exact EQ. 
Qed.

Definition list_is_empty {A: Type} (l: list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.

Definition list_mem {A: Type} (EqDec: forall (x y: A), {x = y} + {x <> y}) (a: A) (l: list A) : bool :=
  List.existsb (fun x => if EqDec x a then true else false) l.

Lemma list_map_transl_err_same:
  forall (A B C: Type) (l: list A) (l': list B) (transl: A -> res B) (f: A -> C) (g: B -> C)
  (transl_correct: forall a b, transl a = OK b -> g b = f a),
    Res.mmap transl l = OK l' ->
    map g l' = map f l.
Proof.
  induction l; intros.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. Res.monadInv H. simpl.
    f_equal. apply transl_correct. exact EQ.
    eapply IHl; eauto.
Qed.

Module UInt63Cmp.
  Definition t := int.

  Definition compare := Unsigned63.compare.

  Lemma compare_eq : forall i j, compare i j = Eq <-> i = j.
  Proof.
    intros.
    rewrite compare_def_spec.
    unfold compare_def.
    destruct (i <?j)%uint63 eqn:LT.
    split. congruence.
    lia.
    destruct (i =?j)%uint63 eqn:EQ.
    split. lia.
    reflexivity.
    split ; (congruence || lia).
  Qed.

  Lemma compare_antisym : forall i j, compare i j  = CompOpp (compare j i).
  Proof.
    intros.
    rewrite! compare_def_spec in *.
    unfold compare_def in *.
    destruct (i <?j)%uint63 eqn:LT1;
    destruct (j <?i)%uint63 eqn:LT2; try lia.
    destruct (j =?i)%uint63 eqn:EQ ; try lia.
    reflexivity.
    destruct (i =?j)%uint63 eqn:EQ; try lia.
    reflexivity.
    destruct (i =?j)%uint63 eqn:EQ1; try lia.
    destruct (j =?i)%uint63 eqn:EQ2; try lia.
    reflexivity.
  Qed.

  Lemma compare_trans : forall i j k c, (i ?= j)%uint63 = c -> (j ?= k)%uint63 = c -> (i ?= k)%uint63 = c.
  Proof.
    intros.
    rewrite! compare_def_spec in *.
    unfold compare_def in *.
    destruct (i <?j)%uint63 eqn:LT1.
  - destruct (j <? k)%uint63 eqn:LT2.
    + subst.
      replace (i <? k)%uint63 with true by lia.
    auto.
    + subst.
      destruct (j =? k)%uint63 ; discriminate.
  - destruct (i =? j)%uint63 eqn:EQ1;
    subst.
    assert (i = j) by lia.
    subst.
    auto.
    destruct (j <? k)%uint63 eqn:LT; try discriminate.
    destruct (j =? k)%uint63 eqn:EQ2; try discriminate.
    destruct (i <? k)%uint63 eqn:LT2; try congruence.
    lia.
    destruct (i =? k)%uint63 eqn:EQ3; try congruence.
    lia.
Qed.

End UInt63Cmp.

Module UnsignedInt63 <: OrderedType.OrderedType.
  Definition t := int.

  Definition eq := @eq t.

  Definition lt: t -> t -> Prop := fun x y => Unsigned63.compare x y = Lt.

  Definition eq_refl : forall x, eq x x.
  Proof.
    reflexivity.
  Qed.

  Lemma eq_sym   : forall x y, eq x y -> eq y x.
  Proof.
    unfold eq.
    congruence.
  Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. congruence.
  Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt. intros x y z.
    apply UInt63Cmp.compare_trans.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> not (eq x y).
  Proof.
    unfold lt,eq. repeat intro.
    subst.
    assert (( y ?= y)%uint63 = Eq).
    { rewrite UInt63Cmp.compare_eq.
      reflexivity.
    } congruence.
  Qed.

  Definition compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros.
    unfold lt,eq.
    destruct (x ?= y)%uint63 eqn:CMP.
    - apply OrderedType.EQ.  rewrite UInt63Cmp.compare_eq in CMP. auto.
    - apply OrderedType.LT ;assumption.
    - apply OrderedType.GT. rewrite UInt63Cmp.compare_antisym.
      unfold UInt63Cmp.compare.
      rewrite CMP. reflexivity.
  Qed.

  Definition eq_dec : forall (x y:t),{x = y} + {~ (x = y)} := eqs.

  Definition eqb (x y:t) :=
    match UInt63Cmp.compare x y with
    | Eq => true
    | _  => false
    end.

  Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
  Proof.
    unfold eq,eqb. intros.
    destruct (UInt63Cmp.compare x y) eqn:EQ.
    - rewrite UInt63Cmp.compare_eq in EQ. intuition congruence.
    - split ; intro; subst. discriminate.
      assert (UInt63Cmp.compare y y = Eq).
      {
        rewrite UInt63Cmp.compare_eq.  reflexivity.
      }
      congruence.
    - split ; intro; subst. discriminate.
      assert (UInt63Cmp.compare y y = Eq).
      {
        rewrite UInt63Cmp.compare_eq.  reflexivity.
      }
      congruence.
  Qed.

End UnsignedInt63.


(** * Sets *)

Notation pset := PositiveSet.t.

Definition smem (s: pset) (p: positive) : bool := PositiveSet.mem p s.

Definition sadd (s: pset) (p: positive) : pset := PositiveSet.add p s.

Definition sremove (s: pset) (p: positive) : pset := PositiveSet.remove p s.

Definition sunion (s1 s2: pset) : pset := PositiveSet.union s1 s2.

Notation sempty := PositiveSet.empty.

Definition ident_set : Type := pset.

(** * Others *)

(* Lemma inj_eq_iff :
  forall (A B: Type)
  (EQA: forall (a1 a2: A), {a1 = a2} + {a1 <> a2})
  (EQB: forall (b1 b2: B), {b1 = b2} + {b1 <> b2})
  (f: A -> B)
  (INJ: forall (a1 a2: A), f(a1) = f(a2) -> a1 = a2),
  forall (a1 a2: A),
  (if EQB (f a1) (f a2) then true else false) =
  (if EQA a1 a2 then true else false).
Proof.
  intros. destruct (EQB (f a1) (f a2)); destruct (EQA a1 a2).
  - reflexivity.
  - specialize (INJ a1 a2 e). tauto.
  - destruct n. congruence.
  - reflexivity.
Qed.

Lemma bij_impl_inj:
  forall (A B: Type)
  (f: A -> B)
  (BIJ: forall (b: B), exists! (a: A), f(a) = b),
  forall (a1 a2: A), f(a1) = f(a2) -> a1 = a2.
Proof.
  intros. specialize (BIJ (f a1)). destruct BIJ as [a UNIQUE].
  unfold unique in UNIQUE. destruct UNIQUE as [EQ1 INJ].
  assert (EQ2: f a = f a2). congruence. symmetry in H.
  apply (INJ a2) in H. specialize (INJ a1). destruct INJ.
  reflexivity. congruence.
Qed.

Lemma bij_defs_impl :
  forall (A B: Type)
  (EQA: forall (a1 a2: A), {a1 = a2} + {a1 <> a2})
  (EQB: forall (b1 b2: B), {b1 = b2} + {b1 <> b2})
  (f: A -> B)
  (g: B -> A)
  (BIJ: forall (a: A) (b: B), f(a) = b <-> g(b) = a),
  forall b, exists! a, f(a) = b.
Proof.
  intros. exists (g b). unfold unique. split.
  - specialize (BIJ (g b) b). tauto.
  - intro. specialize (BIJ x' b). tauto.
Qed.

Lemma bij_eq_iff :
  forall (A B: Type)
  (EQA: forall (a1 a2: A), {a1 = a2} + {a1 <> a2})
  (EQB: forall (b1 b2: B), {b1 = b2} + {b1 <> b2})
  (f: A -> B)
  (g: B -> A)
  (BIJ: forall (a: A) (b: B), f(a) = b <-> g(b) = a),
  forall (a1 a2: A),
  (if EQB (f a1) (f a2) then true else false) =
  (if EQA a1 a2 then true else false).
Proof.
  intros. destruct (EQB (f a1) (f a2)); destruct (EQA a1 a2).
  - reflexivity.
  - destruct n. pose proof BIJ as BIJ'. specialize (BIJ a1 (f a2)).
    destruct BIJ as [INJ SURJ]. assert (Hgf: g (f a2) = a2).
    { specialize (BIJ' a2 (f a2)). tauto. } specialize (INJ e). congruence.
  - destruct n. congruence.
  - reflexivity.
Qed. *)

Lemma bij_eq_iff :
  forall (A B: Type)
  (EQA: forall (a1 a2: A), {a1 = a2} + {a1 <> a2})
  (EQB: forall (b1 b2: B), {b1 = b2} + {b1 <> b2})
  (f: A -> B)
  (g: B -> A)
  (BIJ: forall (a: A) (b: B), f (g b) = b /\ g (f a) = a),
  forall (a1 a2: A),
  (if EQB (f a1) (f a2) then true else false) =
  (if EQA a1 a2 then true else false).
Proof.
  intros. destruct (EQB (f a1) (f a2)); destruct (EQA a1 a2).
  - reflexivity.
  - pose proof BIJ as BIJ'. specialize (BIJ a1 (f a1)).
    specialize (BIJ' a2 (f a2)). destruct BIJ; destruct BIJ'.
    congruence.
  - destruct n. congruence.
  - reflexivity.
Qed.

Fixpoint forall_err {A: Type} (P : A -> res bool) (l:list A) : res bool :=
  match l with
  | nil => OK true
  | e::l => do b <- P e;
            do b1 <- forall_err P l;
            OK (b && b1)
  end.

Fixpoint forall_check {A: Type} (P : A -> res unit) (l:list A) : res unit :=
  match l with
  | nil => OK tt
  | e::l => do _ <- P e;
            forall_check P l
  end.

Section MERGE.
  Context {A : Type}.
  Variable merge : A -> A -> res A.

  Fixpoint merge_list_rec (acc : A) (l:list (res A)) : res A :=
    match l with
     | nil => OK acc
     | e::l => do e <- e;
               do m <- merge e acc;
               merge_list_rec m l
     end.

  Definition merge_list (l: list (res A)) : res A :=
    match l with
    | nil => Error (msg "")
    | acc :: l => do acc <- acc;
                  merge_list_rec acc l
    end.

End MERGE.

Section FORALL3.
  Context {A B C: Type}.

  Variable P : A -> B -> C -> Prop.

  Inductive Forall3 : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 nil nil nil
  | Forall3_cons : forall x y z lx ly lz,
      P x y z ->
      Forall3 lx ly lz ->
      Forall3 (cons x lx) (cons y ly) (cons z lz).

End FORALL3.

(* decide equality of pairs *)

Definition pair_eq_dec {A B: Type}
  (eqA : forall (a1 a2:A),{a1=a2}+{a1<> a2})
  (eqB : forall (a1 a2:B),{a1=a2}+{a1<> a2}) :
  forall (x:A * B) (y:A * B), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Import Datatypes.

Definition compare_eqb (c1 c2: comparison) : bool :=
  match c1 , c2 with
  | Eq , Eq => true
  | Lt , Lt => true
  | Gt , Gt => true
  | _ , _   => false
  end.

Definition compare_le (c:comparison) :=
  match c with
  | Eq | Lt => true
  | _   => false
  end.

Definition compare_eq (c:comparison) :=
  match c with
  | Eq  => true
  | _   => false
  end.

Definition compare_lt (c:comparison) :=
  match c with
  | Lt  => true
  | _   => false
  end.

(** Iterator *)
Fixpoint iternd {A: Type} (F: A -> res A) (leb : A -> A -> bool)
               (join : A -> A -> res A)  (d:A)  (n:nat) : res A * (list A) :=
  match n with
  | O => (Res.Error (MSG "Not enough fuel" :: nil) , (d::nil))
  | S n => match F d with
           | Res.Error m => (Res.Error (MSG "itern: function returns an error "::m),d::nil)
           | OK d1   =>
               match join d d1 with
               | Res.Error e => (Res.Error (MSG "itern: join fails "::e), d::d1::nil)
               | OK d1d  =>
                   if leb d1d d
                   then (OK d,d::nil)
                   else let (r,l) := iternd F leb join d1d n in
                        (r, d::l)
               end
           end
  end.



Fixpoint itern {A: Type} (F : A -> res A) (leb : A -> A -> bool)
               (join : A -> A -> res A)  (d:A)  (n:nat) : res A:=
  match n with
  | O => Res.Error (MSG "Not enough fuel" ::nil)
  | S n =>
      match F d with
      | Res.Error m => Res.Error (MSG "itern: function returns an error "::m)
      | OK d1   =>
          match join d d1 with
          | Res.Error e => Res.Error (MSG "itern: join fails "::e)
          | OK d1d  =>
              if leb d1d d
              then OK d
              else itern F leb join d1d n
          end
      end
  end.

Section ITER.
  Variable A : Type.
  Variable F : A -> res A.
  Variable join : A -> A -> res A.
  Variable leb  : A -> A -> bool.

  Variable join_ub_l : forall a1 a2 r,
      join a1 a2 = OK r ->
      leb a1 r = true.

  Variable join_ub_r : forall a1 a2 r,
      join a1 a2 = OK r ->
      leb a2 r = true.

  Variable leb_trans : forall a1 a2 a3,
      leb a1 a2 = true ->
      leb a2 a3 = true ->
      leb a1 a3 = true.

  Variable leb_refl : forall a1,
      leb a1 a1 = true.


  Lemma itern_iternd : forall n d0,
      itern F leb join d0 n = fst (iternd F leb join d0 n).
  Proof.
    induction n; simpl; auto.
    intros.
    destruct (F d0); try congruence.
    destruct (join d0 a); try reflexivity.
    destruct (leb a0 d0); try congruence.
    reflexivity.
    rewrite IHn. destruct (iternd F leb join a0 n).
    reflexivity.
    reflexivity.
  Qed.

  Lemma itern_le : forall n d0 d1 ,
      itern F leb join d0 n = OK d1 ->
      leb d0 d1 = true.
  Proof.
    induction n.
    - simpl. discriminate.
    - simpl. intros.
      destruct (F d0) eqn:Fd; try discriminate.
      destruct (join d0 a) eqn:J; try discriminate.
      destruct (leb a0 d0) eqn:LE.
      * inv H.
        apply leb_refl.
      * eapply IHn in H.
        apply join_ub_l in J.
        eapply leb_trans;eauto.
  Qed.

  Definition lebr (x : res A) (y:A) : bool :=
    match x with
    | Res.Error _ => false
    | Res.OK x    => leb x y
    end.


  Lemma itern_fix : forall n d0 d1 ,
      itern F leb join d0 n = OK d1 ->
      lebr (F d1) d1 = true /\  leb d0 d1 = true.
  Proof.
    induction n.
    - simpl. discriminate.
    - simpl. intros.
      destruct (F d0) eqn:Fd; try discriminate.
      destruct (join d0 a) eqn:J; try discriminate.
      destruct (leb a0 d0) eqn:LE.
      * inv H.
        repeat split; auto.
        rewrite Fd. simpl.
        apply join_ub_r in J.
        eapply leb_trans;eauto.
      * apply IHn in H.
        destruct H as (LE1 & LE2).
        split; auto.
        apply join_ub_l in J.
        eapply leb_trans;eauto.
  Qed.

End ITER.
