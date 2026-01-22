(** * A collection of useful monads *)

From Coq Require Import PArith String.
From Coq Require Import RelationClasses.
From compcert Require Import AST Maps Errors Coqlib.

Module Type MONAD.

  Parameter M : Type -> Type.
  Parameter ret : forall (A: Type) (a: A), M A.
  Parameter bind : forall (A B: Type) (f: M A) (g: A -> M B), M B.
  Parameter bind2 : forall (A B C: Type) (f: M (A * B)) (g: A -> B -> M C), M C.

End MONAD.

Module MonError <: MONAD.

  Export Errors.

  Definition M : Type -> Type := res.

  Definition ret {A: Type} (a: A) : M A := OK a.

  Definition bind {A B: Type} (f: M A) (g: A -> M B) : M B := Errors.bind f g.

  Definition bind_catch {A B: Type} (f: M A) (g: A -> M B) (m: string) : M B :=
    match f with
    | OK a => g a
    | Error _ => Error (msg m)
    end. 

  Definition bind2 {A B C: Type} (f: M (A * B)) (g: A -> B -> M C) : M C := Errors.bind2 f g.

  Definition fail {A: Type} : M A := Error nil.

  Definition failwith {A: Type} (m: string) : M A := Error (msg m).

  Definition err_of_opt {A: Type} (o: option A) : M A :=
    match o with
    | Some v => OK v
    | None => fail
    end.

  Definition isOK {A: Type} (v: M A) : Prop :=
    exists x, v = OK x.

  Lemma isOK_Error : forall {A: Type} (v : M A),
      isOK v -> forall e, v = Error e -> False.
  Proof.
    unfold isOK.
    intros. destruct H. congruence.
  Qed.

  
  Remark ok_imp_some:
    forall (A: Type) (o: option A) (v: A),
    err_of_opt o = OK v ->
    o = Some v.
  Proof.
    unfold err_of_opt; intros.
    destruct o; try discriminate.
    inv H. reflexivity.
  Qed.

  Inductive res_rel {A B : Type} (R : A -> B -> Prop) : res A -> res B -> Prop :=
    res_rel_error : forall m, res_rel R (Error m) (Error m)
  | res_rel_ok : forall (x : A) (y : B), R x y -> res_rel R (OK x) (OK y).

  Lemma res_rel_trans : forall {A : Type} (R: A -> A -> Prop),
      Transitive R -> Transitive (res_rel R).
  Proof.
    repeat intro.
    inv H0;inv H1; try constructor.
    eapply H; eauto.
  Qed.

  Lemma res_rel_sym : forall {A : Type} (R: A -> A -> Prop),
      Symmetric R -> Symmetric (res_rel R).
  Proof.
    repeat intro.
    inv H0; try constructor.
    apply H; eauto.
  Qed.

  Lemma res_rel_refl : forall {A : Type} (R: A -> A -> Prop),
      Reflexive R -> Reflexive (res_rel R).
  Proof.
    repeat intro.
    destruct x. constructor; auto.
    constructor.
  Qed.

  Notation eret := ret.

  Notation efail := fail.

  Notation "'let*' X := A 'in' B" := (bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200)
    : error_monad_scope.

  Notation "'let*' ( X , Y ) := A 'in' B" := (bind2 A (fun X Y => B))
    (at level 200, X name, Y name, A at level 100, B at level 200)
    : error_monad_scope.

  Notation "let/catch X := A '/>' M 'in' B" := (bind_catch A (fun X => B) M)
    (at level 200, X name, A at level 100, M at level 100, B at level 200)
    : error_monad_scope.

End MonError.

Module Type STATE_TYPE.

  Parameter t : Type.

End STATE_TYPE.

Module MonState (S: STATE_TYPE) <: MONAD.

  Definition M (A: Type) : Type := S.t -> A * S.t.

  Definition ret {A: Type} (a: A) : M A :=
    fun (s: S.t) => (a, s).

  Definition bind {A B: Type} (f: M A) (g: A -> M B) : M B :=
    fun (s: S.t) =>
      let (a, s') := f s in
      g a s'.

  Definition bind2 {A B C: Type} (f: M (A * B)) (g: A -> B -> M C) : M C :=
    fun (s: S.t) =>
      let '((a, b), s') := f s in
      g a b s'.

  Definition get : M S.t :=
    fun (s: S.t) => (s, s).

  Declare Scope state_monad_scope.

  Notation "'let*' X := A 'in' B" := (bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200)
    : state_monad_scope.

  Notation "'let*' ( X , Y ) := A 'in' B" := (bind2 A (fun X Y => B))
    (at level 200, X name, Y name, A at level 100, B at level 200)
    : state_monad_scope.
        
End MonState.

Module MonStateErr (S: STATE_TYPE) <: MONAD.

  Import MonError.

  Definition M (A: Type) : Type := S.t -> res (A * S.t).

  Definition ret {A: Type} (a: A) : M A :=
    fun (s: S.t) => OK (a, s).

  Definition bind {A B: Type} (f: M A) (g: A -> M B) : M B :=
    fun (s: S.t) =>
      match f s with
      | OK (a, s') => g a s'
      | Error msg => Error msg
      end.

  Definition bind2 {A B C: Type} (f: M (A * B)) (g: A -> B -> M C) : M C :=
    fun (s: S.t) =>
      match f s with
      | OK ((a, b), s') => g a b s'
      | Error msg => Error msg
      end.

  Definition get : M S.t :=
    fun (s: S.t) => OK (s, s).

  Definition lift_err {A: Type} (f: MonError.M A) : M A :=
    fun (s: S.t) =>
      match f with
      | OK a => OK (a, s)
      | Error msg => Error msg
      end.

  Definition fail {A: Type} : M A :=
    fun (s: S.t) => Error nil.

  Definition failwith {A: Type} (m: string) : M A :=
    fun (s: S.t) => Error (msg m).

  Declare Scope state_err_monad_scope.

  Notation "'let*' X := A 'in' B" := (bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200)
    : state_err_monad_scope.

  Notation "'let*' ( X , Y ) := A 'in' B" := (bind2 A (fun X Y => B))
    (at level 200, X name, Y name, A at level 100, B at level 200)
    : state_err_monad_scope.

End MonStateErr.

Module StateCounter <: STATE_TYPE.
  Definition t : Type := positive.
End StateCounter.

Module MonCounter.

  Include MonState(StateCounter).

  Definition incr : M positive :=
    fun (s: StateCounter.t) =>
      (s, s + 1)%positive.

  Notation cmon := M.

End MonCounter.

Module MonCounterErr.

  Include MonStateErr(StateCounter).

  Definition incr : M positive :=
    fun (s: StateCounter.t) =>
      OK (s, s + 1)%positive.

  Notation crmon := M.

End MonCounterErr.

