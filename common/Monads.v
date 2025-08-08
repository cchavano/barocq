(** * A collection of useful monads *)

From Coq Require Import String.
From compcert Require Import AST Errors.

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

  Notation eret := ret.

  Notation efail := fail.

  Notation "'let*' X := A 'in' B" := (MonError.bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200)
    : error_monad_scope.

  Notation "'let*' ( X , Y ) := A 'in' B" := (MonError.bind2 A (fun X Y => B))
    (at level 200, X name, Y name, A at level 100, B at level 200)
    : error_monad_scope.

  Notation "let/catch X := A '/>' M 'in' B" := (MonError.bind_catch A (fun X => B) M)
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
  Definition t : Type := nat.
End StateCounter.

Module MonCounter.

  Include MonState(StateCounter).

  Definition incr {A: Type} (a: A) : M A :=
    fun (s: StateCounter.t) =>
      (a, s + 1).

  Notation cmon := MonCounter.M.

End MonCounter.

Module MonCounterErr.

  Include MonStateErr(StateCounter).

  Definition incr {A: Type} (a: A) : M A :=
    fun (s: StateCounter.t) =>
      OK (a, s + 1).

  Notation crmon := MonCounterErr.M.

End MonCounterErr.