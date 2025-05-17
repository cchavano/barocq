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

Module AliasingCheck.

  Import Syntax.Typed.
  Import Imp1.Aliasing_AST.

  Parameter path : Type.

  Parameter make_path : list ident -> path.

  Parameter is_valid_path : ABSDOM -> ident -> path -> bool.

  Parameter is_valid_atom : ABSDOM -> atom -> bool.

  Parameter is_valid_return : ABSDOM -> bool.

  Parameter is_valid_deep_access : ABSDOM -> atom -> list access -> bool.

  Parameter gen_aliasing_program : bool -> Imp1Typed.program -> res Imp1.Aliasing_AST.program.

  Definition failcheck {A: Type} : MonError.M A := failwith "Imp1gen.AliasingCheck.check_statement".

  Fixpoint check_statement (s: Imp1.Aliasing_AST.statement) : res Imp1Typed.statement :=
    match s with
    | StSet x c IN _ =>
        let valid_comp :=
          match c with
            | CpAtom a _ => is_valid_atom IN a
            | CpArrayGet a i _ =>
                is_valid_atom IN a
                && is_valid_atom IN i 
            | CpArraySet _ i v _ =>
                is_valid_atom IN i
                && is_valid_atom IN v
            | CpStructProj (AVar y _) f _ =>
                is_valid_path IN y (make_path (cons f nil))
            | CpStructProj _ _ _ => false
            | CpStructUpdate _ _ v _ => is_valid_atom IN v
            | CpCall _ args _ =>
                List.forallb (is_valid_atom IN) args
            | CpDeepAccess a acs _ =>
                is_valid_deep_access IN a acs
          end
        in
        if valid_comp then eret (Imp1Typed.StSet x c)
        else failcheck
  | StIfThenElse a s1 s2 =>
      let* s1' := check_statement s1 in
      let* s2' := check_statement s2 in
      eret (Imp1Typed.StIfThenElse a s1' s2')
  | StSequence s1 s2 =>
      let* s1' := check_statement s1 in
      let* s2' := check_statement s2 in
      eret (Imp1Typed.StSequence s1' s2')
  | StReturn a _ OUT =>
      if is_valid_return OUT then eret (Imp1Typed.StReturn a)
      else failcheck
  end.

  Definition check_function (f: Imp1.Aliasing_AST.function) : res Imp1Typed.function :=
    let* body := check_statement (fn_body f) in
    eret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}.

  Definition check_globdef (def: Imp1.Aliasing_AST.globdef) : res Imp1Typed.globdef :=
    match def with
    | DefConst x l ty => eret (DefConst x l ty)
    | DefFun x f =>
        let* f' := check_function f in
        eret (DefFun x f')
    | DeclConst x ty => eret (DeclConst x ty)
    | DeclFun f tparams tret => eret (DeclFun f tparams tret)
    end.

  Definition check_program (prog: Imp1.Aliasing_AST.program) : res Imp1Typed.program :=
    let* defs := mmap check_globdef (prog_defs prog) in
    eret {|
      prog_defs := defs;
      prog_types := prog_types prog
    |}.

End AliasingCheck.