From Coq Require Import Bool List String.
From BarocqComp Require Import Error Utils Monads Syntax ImpABNF Imp1.
Import MonCounter.

Fixpoint transl_statement (s: ImpABNF.statement) : Imp1.statement :=
  match s with
  | ImpABNF.StSequence s1 s2 =>
      let s1' := transl_statement s1 in
      let s2' := transl_statement s2 in
      StSequence s1' s2'
  | ImpABNF.StSet x c => StSet x c
  | ImpABNF.StIfThenElse a s1 s2 =>
      let s1' := transl_statement s1 in
      let s2' := transl_statement s2 in
      StIfThenElse a s1' s2'
  end.

Local Open Scope state_monad_scope.

Definition fresh_var : cmon ident := Utils.fresh_var "i".

Fixpoint transl_tailcomp_rec (t: ImpABNF.tailcomp) : cmon Imp1.statement :=
  match t with
  | TcBegin s t1 =>
      let s' := transl_statement s in
      let* s1 := transl_tailcomp_rec t1 in
      ret (StSequence s' s1)
  | TcComp c =>
      match c with
      | CpAtom a => ret (StReturn a)
      | _ =>
          let* x := fresh_var in
          let s := StSequence (StSet x c) (StReturn (AVar x)) in
          ret s
      end
  | TcIfThenElse a t1 t2 =>
      let* t1' := transl_tailcomp_rec t1 in
      let* t2' := transl_tailcomp_rec t2 in
      ret (StIfThenElse a t1' t2')
  end.

Definition transl_tailcomp (t: ImpABNF.tailcomp) : Imp1.statement :=
  let '(s, _) := transl_tailcomp_rec t 0 in
  s.

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
  | DeclConst x ty => DeclConst x ty
  | DeclFun f tparams tret => DeclFun f tparams tret
  end.

Definition transl_program (prog: ImpABNF.program) : Imp1.program :=
  {|
    prog_defs := map (fun d => transl_globdef d) (prog_defs prog);
    prog_types := prog_types prog
  |}.

Close Scope state_monad_scope.

Parameter gen_aliasing_program : bool -> Imp1Typed.program -> res Imp1.Aliasing_AST.program.

Parameter check_program_aliasing : Aliasing_AST.program -> res Imp1Typed.program.