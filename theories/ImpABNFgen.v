From Coq Require Import List.
From BarocqComp Require Import Error Syntax ImpBNF ImpABNF.
Import ListNotations.

Local Open Scope error_monad_scope.

Fixpoint tailcomp_depth (t: ImpBNF.tailcomp) : nat :=
  match t with
  | ImpBNF.TcBegin ls t1 =>
      1 + (fold_left (fun acc x => acc + (statement_depth x)) ls 0)
        + (tailcomp_depth t1)
  | ImpBNF.TcComp _ => 3
  | ImpBNF.TcIfThenElse _ t1 t2 =>
      let m := max 1 (tailcomp_depth t1) in
      let m := max m (tailcomp_depth t2) in
      1 + m
  end

with statement_depth (s: ImpBNF.statement) : nat :=
  match s with
  | ImpBNF.StSetTailcomp _ t => 1 + (tailcomp_depth t)
  end.

Fixpoint normalize_statement (fuel: nat) (s: ImpBNF.statement) : res ImpABNF.statement :=
  match fuel with
  | O => fail
  | S fuel' =>
      let '(ImpBNF.StSetTailcomp x t) := s in
      match t with
        | ImpBNF.TcBegin ls tc =>
            let* ls' := mmap (normalize_statement fuel') ls in
            let* sc := normalize_statement fuel' (ImpBNF.StSetTailcomp x tc) in
            ret (StBegin (ls' ++ [sc]))
        | ImpBNF.TcIfThenElse a t1 t2 => 
            let* s1 := normalize_statement fuel' (ImpBNF.StSetTailcomp x t1) in
            let* s2 := normalize_statement fuel' (ImpBNF.StSetTailcomp x t2) in
            ret (StIfThenElse a s1 s2)
        | ImpBNF.TcComp c => ret (StSet x c)
      end
  end.

Fixpoint normalize_tailcomp (t: ImpBNF.tailcomp) : res ImpABNF.tailcomp :=
  match t with
  | ImpBNF.TcBegin ls t1 =>
      let* ls' := mmap (fun s => normalize_statement (statement_depth s + 1) s) ls in
      let* t1' := normalize_tailcomp t1 in
      ret (TcBegin ls' t1')
  | ImpBNF.TcIfThenElse a t1 t2 =>
      let* t1' := normalize_tailcomp t1 in
      let* t2' := normalize_tailcomp t2 in
      ret (TcIfThenElse a t1' t2')
  | ImpBNF.TcComp c => ret (TcComp c)
  end.

Definition normalize_function (f: ImpBNF.function) : res ImpABNF.function :=
  let* body := normalize_tailcomp (fn_body f) in
  ret {|
    fn_return := fn_return f;
    fn_params := fn_params f;
    fn_body := body
  |}.

Definition normalize_globdef (def: ImpBNF.globdef) : res ImpABNF.globdef :=
  match def with
  | DefConst x l ty => ret (DefConst x l ty)
  | DefFun x f =>
      let* f' := normalize_function f in
      ret (DefFun x f')
  end.

Definition normalize_program (prog: ImpBNF.program) : res ImpABNF.program :=
  let* defs := mmap normalize_globdef (prog_defs prog) in
  let prog' := {|
    prog_defs := defs;
    prog_types := prog_types prog
  |} in
  ret prog'.