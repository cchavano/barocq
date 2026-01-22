From Coq Require Import List String.
From BarocqComp Require Import Error Utils Syntax ImpBNF Imp1 Maps2.
Import ListNotations.

Open Scope string_scope.

Fixpoint tailcomp_depth (t: ImpBNF.tailcomp) : nat :=
  match t with
  | ImpBNF.TcBegin s t1 _ =>
      1 + Nat.max (statement_depth s) (tailcomp_depth t1)
  | ImpBNF.TcComp _ _ => 1
  | ImpBNF.TcIfThenElse _ t1 t2 _ =>
      let m := Nat.max 1 (tailcomp_depth t1) in
      let m := Nat.max m (tailcomp_depth t2) in
      1 + m
  | ImpBNF.TcSwitch _ cases _ =>
      let cases_depths := List.map (fun c => tailcomp_depth (snd c)) cases in
      let m := List.fold_left (fun m d => Nat.max m d) cases_depths 0 in
      1 + m
  | ImpBNF.TcAttr s e => 1 + tailcomp_depth e
  end

with statement_depth (s: ImpBNF.statement) : nat :=
  match s with
  | ImpBNF.StSetTailcomp _ t => 1 + (tailcomp_depth t)
  end.

Fixpoint norm_statement (fuel: nat) (s: ImpBNF.statement) : res Imp1.statement :=
  match fuel with
  | O => fail
  | S fuel' =>
      let '(ImpBNF.StSetTailcomp x t) := s in
      match t with
      | ImpBNF.TcBegin s tc _ =>
          let* s' := norm_statement fuel' s in
          let* sc := norm_statement fuel' (ImpBNF.StSetTailcomp x tc) in
          ret (StSequence s' sc)
      | ImpBNF.TcIfThenElse a t1 t2 _ =>
          let* s1 := norm_statement fuel' (ImpBNF.StSetTailcomp x t1) in
          let* s2 := norm_statement fuel' (ImpBNF.StSetTailcomp x t2) in
          ret (StIfThenElse a s1 s2)
      | ImpBNF.TcSwitch a cases _ =>
          let* cases' :=
            Utils.list_fold_right_err
              (fun '(ci, ti) acc =>
                 let* si := norm_statement fuel' (ImpBNF.StSetTailcomp x ti) in
                 ret ((ci, si) :: acc))
              (ret nil)
              cases
          in
          ret (StSwitch a cases')
      | ImpBNF.TcComp c _ => ret (StSet x c)
      | ImpBNF.TcAttr a c =>
          let* s1 := norm_statement fuel' (StSetTailcomp x c) in
          ret (StAttr a s1)
      end
  end.

Fixpoint norm_tailcomp (t: ImpBNF.tailcomp) : res Imp1.statement :=
  match t with
  | ImpBNF.TcBegin s t1 _ =>
      let* s' := norm_statement (statement_depth s + 1) s in
      let* t1' := norm_tailcomp t1 in
      ret (StSequence s' t1')
  | ImpBNF.TcIfThenElse a t1 t2 _ =>
      let* t1' := norm_tailcomp t1 in
      let* t2' := norm_tailcomp t2 in
      ret (StIfThenElse a t1' t2')
  | ImpBNF.TcSwitch a cases _ =>
      let* cases' := MapList.map_err norm_tailcomp cases in
      ret (StSwitch a cases')
  | ImpBNF.TcComp c _ =>
      match c with
      | CpAtom a ty => ret (StReturn a)
      | _ => ret (StSequence (StSet "res" c) (StReturn (AVar "res" (typof_comp c))))
      end
  | ImpBNF.TcAttr a c =>
      let* t1 := norm_tailcomp c in
      ret (StAttr a t1)
  end.

Definition norm_function (f: ImpBNF.function) : res Imp1.function :=
  let* body := norm_tailcomp (fn_body f) in
  ret {|
    fn_return := fn_return f;
    fn_params := fn_params f;
    fn_body := body
  |}.

Definition norm_globdef (def: ImpBNF.globdef) : res Imp1.globdef :=
  match def with
  | DefConst x l ty => ret (DefConst x l ty)
  | DefFun x f =>
      let* f' := norm_function f in
      ret (DefFun x f')
  | DeclConst x ty => ret (DeclConst x ty)
  | DeclFun f tparams tret => ret (DeclFun f tparams tret)
  end.

Definition norm_program (prog: ImpBNF.program) : res Imp1.program :=
  let* defs := mmap norm_globdef (prog_defs prog) in
  let prog' := {|
    prog_defs := defs;
    prog_types := prog_types prog;
    prog_tabs := prog_tabs prog
  |} in
  ret prog'.