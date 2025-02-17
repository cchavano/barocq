From Coq Require Import List String.
From BarocqComp Require Import Common Monads Syntax ImpABNF Imp1.
Import MonCounter.

Fixpoint transl_statement (s: ImpABNF.statement) : Imp1.statement :=
  match s with
  | ImpABNF.StBegin ls =>
      fold_left
        (fun acc s => StSequence acc (transl_statement s)) ls StSkip
  | ImpABNF.StSet x c => StSet x c
  | ImpABNF.StIfThenElse a s1 s2 =>
      StIfThenElse a (transl_statement s1) (transl_statement s2)
  end.

Local Open Scope state_monad_scope.

Definition fresh_var : cmon ident := Common.fresh_var "i".

Fixpoint transl_tailcomp_rec (t: ImpABNF.tailcomp) : cmon Imp1.statement :=
  match t with
  | TcBegin ls t1 =>
      let s1 := fold_left (fun acc s => StSequence acc (transl_statement s)) ls StSkip in
      let* s2 := transl_tailcomp_rec t1 in
      ret (StSequence s1 s2)
  | TcComp c =>
      match c with
      | CpAtom a => ret (StReturn a)
      | _ =>
          let* x := fresh_var in
          ret (StSequence (StSet x c) (StReturn (AVar x)))
      end
  | TcIfThenElse a t1 t2 =>
      let* s1 := transl_tailcomp_rec t1 in
      let* s2 := transl_tailcomp_rec t2 in
      ret (StIfThenElse a s1 s2)
  end.

Definition transl_tailcomp (t: ImpABNF.tailcomp) : Imp1.statement :=
  fst (transl_tailcomp_rec t 0).

Definition transl_function (f: ImpABNF.function) : Imp1.function :=
  {|
    fn_return := fn_return f;
    fn_params := fn_params f;
    fn_body := transl_tailcomp (fn_body f)
  |}.

Definition transl_globdef (def: ImpABNF.globdef) : Imp1.globdef :=
  match def with
  | DefConst x l ty => DefConst x l ty
  | DefFun x f => DefFun x (transl_function f)
  end.

Definition transl_program (prog: ImpABNF.program) : Imp1.program :=
  {|
    prog_defs := map (fun d => transl_globdef d) (prog_defs prog);
    prog_types := prog_types prog
  |}.