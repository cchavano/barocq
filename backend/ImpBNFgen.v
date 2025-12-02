From Coq Require Import String List.
From BarocqComp Require Import Syntax BarocqBNF ImpBNF Maps2.
Import ListNotations.

Open Scope string_scope.

Fixpoint transl_expr (e: BarocqBNF.expr) : ImpBNF.tailcomp :=
  match e with
  | EAtom a => TcComp (CpAtom a)
  (* | EArrayGet a1 a2 => TcComp (CpArrayGet a1 a2) *)
  | EArraySet a1 a2 a3 => TcComp (CpArraySet a1 a2 a3)
  (* | ERecordProj a x => TcComp (CpRecordProj a x) *)
  | ERecordUpdate a1 x a2 => TcComp (CpRecordUpdate a1 x a2)
  (* | EDeepAccess a acs => TcComp (CpDeepAccess a acs) *)
  | EApp a args =>
      let fid :=
        match a with
        | AVar x => x
        | _ => "" (* ill-formed program *)
        end
      in
      TcComp (CpCall fid args)
  | ELetIn x e1 e2 =>
      TcBegin (StSetTailcomp x (transl_expr e1)) (transl_expr e2)
  | EIfThenElse a e1 e2 =>
      TcIfThenElse a (transl_expr e1) (transl_expr e2)
  | EMatch a cases =>
      let cases' := MapList.map transl_expr cases in
      TcSwitch a cases'
  | EAttr s e =>  TcAttr s (transl_expr e)
  end.

Definition transl_function (f: BarocqBNF.function) : ImpBNF.function :=
  {|
    fn_return := fn_return f;
    fn_params := fn_params f;
    fn_body := transl_expr (fn_body f)
  |}.

Definition transl_globdef (def: BarocqBNF.globdef) : ImpBNF.globdef :=
  match def with
  | DefConst x l ty => DefConst x l ty
  | DefFun x f => DefFun x (transl_function f)
  | DeclConst x ty => DeclConst x ty
  | DeclFun f tparams tret => DeclFun f tparams tret
  end.

Definition transl_program (prog: BarocqBNF.program) : ImpBNF.program :=
  {|
    prog_defs := List.map transl_globdef (prog_defs prog);
    prog_types := prog_types prog;
    prog_tabs := prog_tabs prog;
  |}.
