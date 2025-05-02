From Coq Require Import List.
From BarocqComp Require Import Error Syntax ImpBNF ImpABNF.
Import ListNotations.

Fixpoint tailcomp_depth (t: ImpBNF.tailcomp) : nat :=
  match t with
  | ImpBNF.TcBegin s t1 =>
      1 + (statement_depth s) + (tailcomp_depth t1)
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

Fixpoint norm_statement (fuel: nat) (s: ImpBNF.statement) : res ImpABNF.statement :=
  match fuel with
  | O => fail
  | S fuel' =>
      let '(ImpBNF.StSetTailcomp x t) := s in
      match t with
        | ImpBNF.TcBegin s tc =>
            let* s' := norm_statement fuel' s in
            let* sc := norm_statement fuel' (ImpBNF.StSetTailcomp x tc) in
            ret (StSequence s' sc)
        | ImpBNF.TcIfThenElse a t1 t2 => 
            let* s1 := norm_statement fuel' (ImpBNF.StSetTailcomp x t1) in
            let* s2 := norm_statement fuel' (ImpBNF.StSetTailcomp x t2) in
            ret (StIfThenElse a s1 s2)
        | ImpBNF.TcComp c => ret (StSet x c)
      end
  end.

Fixpoint norm_tailcomp (t: ImpBNF.tailcomp) : res ImpABNF.tailcomp :=
  match t with
  | ImpBNF.TcBegin s t1 =>
      let* s' := norm_statement (statement_depth s + 1) s in
      let* t1' := norm_tailcomp t1 in
      ret (TcBegin s' t1')
  | ImpBNF.TcIfThenElse a t1 t2 =>
      let* t1' := norm_tailcomp t1 in
      let* t2' := norm_tailcomp t2 in
      ret (TcIfThenElse a t1' t2')
  | ImpBNF.TcComp c => ret (TcComp c)
  end.

Definition norm_function (f: ImpBNF.function) : res ImpABNF.function :=
  let* body := norm_tailcomp (fn_body f) in
  ret {|
    fn_return := fn_return f;
    fn_params := fn_params f;
    fn_body := body
  |}.

Definition norm_globdef (def: ImpBNF.globdef) : res ImpABNF.globdef :=
  match def with
  | DefConst x l ty => ret (DefConst x l ty)
  | DefFun x f =>
      let* f' := norm_function f in
      ret (DefFun x f')
  end.

Definition norm_program (prog: ImpBNF.program) : res ImpABNF.program :=
  let* defs := mmap norm_globdef (prog_defs prog) in
  let prog' :={|
    prog_defs := defs;
    prog_types := prog_types prog;
  |} in
  ret prog'.