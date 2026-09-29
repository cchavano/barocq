(** * A collection of useful state monads *)

From Stdlib Require Import PArith String.
From Stdlib Require Import RelationClasses.
From compcert Require Import AST Maps Coqlib.
From BarocqComp Require Import Res.

Module Type SMONAD.

Parameter M : Type -> Type.
Parameter sret : forall (A: Type) (a: A), M A.
Parameter bind : forall (A B: Type) (f: M A) (g: A -> M B), M B.
Parameter bind2 : forall (A B C: Type) (f: M (A * B)) (g: A -> B -> M C), M C.

End SMONAD.

Module Type STATE_TYPE.

  Parameter t : Type.

End STATE_TYPE.

Module MonState (S: STATE_TYPE) <: SMONAD.

  Definition M (A: Type) : Type := S.t -> A * S.t.

  Definition sret {A: Type} (a: A) : M A :=
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

  Notation "'do' X <- A ; B" := (bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200)
    : state_monad_scope.

  Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
    (at level 200, X name, Y name, A at level 100, B at level 200)
    : state_monad_scope.

  Notation "'do' ( X , Y , Z ) <- A ; B" := (bind A (fun '(X, Y, Z) => B))
    (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
    : state_monad_scope.



  Section FOLDR.
    Open Scope state_monad_scope.
    Context {A B: Type}.
    Variables (F : B -> A -> M A).

    Fixpoint fold_right (l:list B) (m : M A) : M A :=
      match l with
      | nil => m
      | e::l => do r <- fold_right l m ;
                F e r
      end.
    End FOLDR.


End MonState.

Module MonStateErr (S: STATE_TYPE) <: SMONAD.

  Definition M (A: Type) : Type := S.t -> res (A * S.t).

  Definition sret {A: Type} (a: A) : M A :=
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

  Definition lift_err {A: Type} (f: res A) : M A :=
    fun (s: S.t) =>
      match f with
      | OK a => OK (a, s)
      | Error msg => Error msg
      end.

  Definition lift_option {A: Type} (f: option A) : M A :=
    fun (s: S.t) =>
      match f with
      | Some a => OK (a, s)
      | None => Error nil
      end.

  Definition sfail {A: Type} : M A :=
    fun (s: S.t) => Error nil.

  Definition sfailwith {A: Type} (m: string) : M A :=
    fun (s: S.t) => Error (msg m).

  Declare Scope state_err_monad_scope.

  Notation "'do' X <- A ; B" := (bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200)
    : state_err_monad_scope.

  Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
    (at level 200, X name, Y name, A at level 100, B at level 200)
    : state_err_monad_scope.

End MonStateErr.

Module MonStateErr2 (S: STATE_TYPE) <: SMONAD.

  Definition M (A: Type) : Type := S.t -> (res A * S.t).

  Definition sret {A: Type} (a: A) : M A :=
    fun (s: S.t) => (OK a, s).

  Definition bind {A B: Type} (f: M A) (g: A -> M B) : M B :=
    fun (s: S.t) =>
      match f s with
      | (OK a, s') => g a s'
      | (Error msg, s') => (Error msg, s')
      end.

  Definition bind2 {A B C: Type} (f: M (A * B)) (g: A -> B -> M C) : M C :=
    fun (s: S.t) =>
      match f s with
      | (OK (a, b), s') => g a b s'
      | (Error msg, s') => (Error msg, s')
      end.

  Definition get : M S.t :=
    fun (s: S.t) => (OK s, s).

  Definition lift_err {A: Type} (f: res A) : M A :=
    fun (s: S.t) =>
      match f with
      | OK a => (OK a, s)
      | Error msg => (Error msg, s)
      end.

  Definition lift_option {A: Type} (f: option A) : M A :=
    fun (s: S.t) =>
      match f with
      | Some a => (OK a, s)
      | None => (Error nil, s)
      end.

  Definition sfail {A: Type} : M A :=
    fun (s: S.t) => (Error nil, s).

  Definition sfailwith {A: Type} (m: string) : M A :=
    fun (s: S.t) => (Error (msg m), s).

  Declare Scope state_err2_monad_scope.

  Notation "'do' X <- A ; B" := (bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200)
    : state_err2_monad_scope.

  Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
    (at level 200, X name, Y name, A at level 100, B at level 200)
    : state_err2_monad_scope.

  Notation "'do/l' X <- A ; B" := (bind (lift_err A) (fun X => B))
    (at level 200, X name, A at level 100, B at level 200)
    : state_err2_monad_scope.

  Notation "'do/l' ( X , Y ) <- A ; B" := (bind2 (lift_err A) (fun X Y => B))
    (at level 200, X name, Y name, A at level 100, B at level 200)
    : state_err2_monad_scope.

End MonStateErr2.

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

