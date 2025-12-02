From Coq Require Import PArith ZArith String DecimalString List Bool MSetPositive.
From compcert Require Import Ctypesdefs Maps Integers.
From BarocqComp Require Import Error Monads Ident.
Import MonCounter.
Import MonCounterErr.
Import ListNotations.

Polymorphic Definition cast {A B: Type} (EQ : A = B) (v: A) : B.
  rewrite EQ in v. exact v.
Defined.

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

Definition transl_user_ident (i: ident) : ident :=
  Ident.prefix_with "u_" i.

Open Scope state_monad_scope.

Definition fresh_var (prefix: string) : cmon ident :=
  let* ctr := MonCounter.get in
  let var := Ident.prefix_with prefix (Ident.of_str_nat ctr) in
  MonCounter.incr var.

Close Scope state_monad_scope.

Open Scope state_err_monad_scope.

Definition fresh_var_err (prefix: string) : crmon ident :=
  let* ctr := MonCounterErr.get in
  let var := Ident.prefix_with prefix (Ident.of_str_nat ctr) in
  MonCounterErr.incr var.

Close Scope state_err_monad_scope.

(** * Lists *)

Definition list_nth_err {A: Type} (l: list A) (n: nat) : res A :=
  err_of_opt (nth_error l n).

Lemma list_nth_err_map_same : 
  forall (A B: Type) (f: A -> B) (l: list A) (n: nat),
  list_nth_err (map f l) n =
  let* x := list_nth_err l n in
  eret (f x).
Proof.
  unfold list_nth_err. induction l; destruct n.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. apply (IHl n).
Qed.

Fixpoint list_fold_left_err {A B: Type} (f: A -> B -> res A) (l: list B) (a0: res A) : res A :=
  match l with
  | nil => a0
  | x :: l' =>
      let* a0 := a0 in
      list_fold_left_err f l' (f a0 x)
  end.

Fixpoint list_fold_right_err {A B: Type} (f: B -> A -> res A) (a0: res A) (l: list B) : res A :=
  match l with
  | nil => a0
  | x :: l' =>
      let* r := list_fold_right_err f a0 l' in
      f x r
  end.

Definition list_is_empty {A: Type} (l: list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.

Definition list_mem {A: Type} (EqDec: forall (x y: A), {x = y} + {x <> y}) (a: A) (l: list A) : bool :=
  List.existsb (fun x => if EqDec x a then true else false) l.

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
  | e::l => let* b := P e in
            let* b1 := forall_err P l in
            OK (b && b1)
  end.

Fixpoint forall_check {A: Type} (P : A -> res unit) (l:list A) : res unit :=
  match l with
  | nil => OK tt
  | e::l => let* _ := P e in
            forall_check P l
  end.



Section MERGE.
  Context {A : Type}.
  Variable merge : A -> A -> res A.

  Fixpoint merge_list_rec (acc : A) (l:list (res A)) : res A :=
  match l with
  | nil => OK acc
  | e::l => let* e := e in
            let* m := merge e acc in
            merge_list_rec m l
  end.

  Definition merge_list (l: list (res A)) : res A :=
    match l with
    | nil => Error (msg "")
    | acc :: l => let* acc := acc in
                  merge_list_rec acc l
    end.

End MERGE.
