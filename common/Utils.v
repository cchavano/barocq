From Stdlib Require Import PArith ZArith String DecimalString List Bool MSetPositive.
From compcert Require Import Coqlib Ctypesdefs Maps Integers.
From BarocqComp Require Import StateMonads Res Option Ident ZlistPlus.
Local Open Scope error_monad_scope.
Local Open Scope option_monad_scope.
Import MonCounter.
Import MonCounterErr.
Import ListNotations.

Lemma elim_if : forall {A: Type} (c:bool) (e1 e1' e2 e2':A),
  e1 = e1' -> e2 = e2' ->
  (if c then e1 else e2) = (if c then e1' else e2').
Proof.
  destruct c; auto.
Qed.

Polymorphic Definition cast {A B: Type} (EQ : A = B) (v: A) : B.
  rewrite EQ in v. exact v.
Defined.

Lemma cast_ok_imp_eq:
  forall (A B: Type) (EQ: A = B) (v: A) (v': B),
  @cast A B EQ v = v' ->
  A = B.
Proof.
  tauto.
Qed.

(** Given a goal of the form [Forall P l], instead of doing [repeat Forall_cons] (slow),
    do [apply Forall_app_sound]  (fast) *)

(* [Forall_app [l1;...;ln] G] generates the formula P l1 -> ... -> P ln -> G *)
Fixpoint Forall_app {A: Type} (P : A -> Prop) (l:list A) (G:Prop) {struct l} :=
  match l with
  | nil => G
  | e::l' => P e -> (Forall_app P l' G)
  end.

Lemma Forall_app_Forall : forall {A: Type} (P : A -> Prop) l G,
    (Forall P l -> G) ->  Forall_app P l G.
Proof.
  induction l; simpl;auto.
Qed.

Lemma Forall_app_sound : forall {A: Type} (P: A -> Prop) l,
    Forall_app P l (Forall P l).
Proof.
  intros.
  apply Forall_app_Forall.
  auto.
Qed.

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

Definition cast_enum {A: Type} (l:list A) (i:int) : option A :=
  list_nth_z l (Int.signed i).

Lemma cast_enum_Some : forall {A: Type} (l:list A) (i:int),
    0 <= Int.signed i < Zlength l ->
    exists v, cast_enum l i = Some v.
Proof.
  intros.
  unfold cast_enum.
  destruct (list_nth_z l (Int.signed i)) eqn:GET.
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
  
Section S.
  (** is-it already defined elsewhere? *)
  Context {A B: Type}.
  Variable f : A -> B -> bool.

  Fixpoint forall2b  (l1: list A) (l2: list B) {struct l1} : bool :=
    match l1 , l2 with
  | nil , nil => true
  | e1::l1, e2::l2 => if f e1 e2 then forall2b l1 l2 else false
  | _ , _ => false
  end.

End S.

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

(* Tactics *)

Ltac destruct_conj H :=
  match type of H with
  | _ && _ = _ =>
      apply andb_prop in H;
      destruct_conj H
  | _ /\ _ =>
      let c1 := fresh "C" in
      let c2 := fresh "C" in
      destruct H as [c1 c2];
      destruct_conj c1;
      destruct_conj c2
  | _ => idtac
  end.
      
Ltac inv H := Coqlib.inv H.

Ltac rew H :=
  match type of H with
  | ?A = _ => destruct A ; try discriminate ; inv H
  end.
