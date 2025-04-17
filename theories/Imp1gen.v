From Coq Require Import Bool List String.
From BarocqComp Require Import Error Common Monads Syntax ImpABNF Imp1.
Import MonCounter.

Definition transl_param (x: ident) : ident :=
  prefix_ident "a" x.

Fixpoint transl_atom (params: pset) (a: atom) : atom :=
  match a with
  | AVar x =>
      if smem params x then AVar (transl_param x)
      else (AVar x)
  | AUnaryOp op a1 =>
      AUnaryOp op (transl_atom params a1)
  | ABinaryOp op a1 a2 =>
      ABinaryOp op (transl_atom params a1) (transl_atom params a2)
  | _ => a
  end.

Definition transl_access (params: pset) (ac: access) : access :=
  match ac with
  | AcArrayIndex i => AcArrayIndex (transl_atom params i)
  | _ => ac
  end.

Definition transl_comp (params: pset) (c: comp) : comp :=
  match c with
  | CpAtom a =>
      CpAtom (transl_atom params a)
  | CpArrayGet a1 a2 =>
      let a1' := transl_atom params a1 in
      let a2' := transl_atom params a2 in
      CpArrayGet a1' a2'
  | CpArraySet a1 a2 a3 =>
      let a1' := transl_atom params a1 in
      let a2' := transl_atom params a2 in
      let a3' := transl_atom params a3 in
      CpArraySet a1' a2' a3'
  | CpStructProj a f =>
      let a' := transl_atom params a in
      CpStructProj a' f
  | CpStructUpdate a1 f a2 =>
      let a1' := transl_atom params a1 in
      let a2' := transl_atom params a2 in
      CpStructUpdate a1' f a2'
  | CpDeepAccess a acs =>
      let a' := transl_atom params a in
      let acs' := List.map (transl_access params) acs in
      CpDeepAccess a' acs'
  | CpCall a args =>
      let a' := transl_atom params a in
      let args' := List.map (transl_atom params) args in
      CpCall a' args'
  end.

Fixpoint transl_statement (params: pset) (s: ImpABNF.statement) : Imp1.statement * pset :=
  match s with
  | ImpABNF.StSequence s1 s2 =>
      let (s1', params1) := transl_statement params s1 in
      let (s2', params2) := transl_statement params1 s2 in
      (StSequence s1' s2', params2)
  | ImpABNF.StSet x c =>
      let c' := transl_comp params c in
      (StSet x c', sremove params x)
  | ImpABNF.StIfThenElse a s1 s2 =>
      let a' := transl_atom params a in
      let (s1', params1) := transl_statement params s1 in
      let (s2', params2) := transl_statement params s2 in
      (* params1 and params2 should be the same after compilation *)
      (StIfThenElse a' s1' s2', params1)
  end.

Local Open Scope state_monad_scope.

Definition fresh_var : cmon ident := Common.fresh_var "i".

Fixpoint transl_tailcomp_rec (params: pset) (t: ImpABNF.tailcomp) : cmon (Imp1.statement * pset) :=
  match t with
  | TcBegin s t1 =>
      let (s', params') := transl_statement params s in
      let* (s1, params1) := transl_tailcomp_rec params' t1 in
      ret (StSequence s' s1, params1)
  | TcComp c =>
      match c with
      | CpAtom a =>
          ret (StReturn (transl_atom params a), params)
      | _ =>
          let* x := fresh_var in
          let c' := transl_comp params c in
          let s := StSequence (StSet x c') (StReturn (AVar x)) in
          ret (s, params)
      end
  | TcIfThenElse a t1 t2 =>
      let a' := transl_atom params a in
      let* (t1', params1) := transl_tailcomp_rec params t1 in
      let* (t2', params2) := transl_tailcomp_rec params t2 in
      (* Sets params1 and params2 should be equal after a compilation phase. *)
      ret (StIfThenElse a' t1' t2', params1)
  end.

Definition transl_tailcomp (params: pset) (t: ImpABNF.tailcomp) : Imp1.statement :=
  let '((s, _), _) := transl_tailcomp_rec params t 0 in
  s.

Definition transl_function (f: ImpABNF.function) : Imp1.function :=
  let param_set := List.fold_left (fun acc p => sadd acc (fst p)) (fn_params f) sempty in
  {|
    fn_return := fn_return f;
    fn_params := List.map (fun '(x, tx) => (transl_param x, tx)) (fn_params f);
    fn_body := transl_tailcomp param_set (fn_body f)
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

Close Scope state_monad_scope.

Module AliasingCheck.

  Import Syntax.Typed.
  Import Imp1.Aliasing_AST.

  Parameter path : Type.

  Parameter make_path : list ident -> path.

  Parameter is_valid_path : ABSDOM -> ident -> path -> bool.

  Parameter is_valid_atom : ABSDOM -> atom -> bool.

  Parameter is_valid_return : ABSDOM -> bool.

  Parameter gen_aliasing_program : bool -> Imp1Typed.program -> res Imp1.Aliasing_AST.program.

  Definition failcheck {A: Type} : MonError.M A := failwith "Imp1gen.AliasingCheck.check_statement".

  Fixpoint check_statement (s: Imp1.Aliasing_AST.statement) : res Imp1Typed.statement :=
    match s with
    | StSet x c IN _ =>
        let* c' :=
          match c with
          | CpAtom a _ =>
              if is_valid_atom IN a then eret c
              else failcheck
          | CpArrayGet a i _ =>
              if is_valid_atom IN a &&
                 is_valid_atom IN i 
              then eret c
              else failcheck
          | CpArraySet _ i v _ =>
              if is_valid_atom IN i &&
                 is_valid_atom IN v
              then eret c
              else failcheck
          | CpStructProj (AVar y _) f _ =>
              if is_valid_path IN y (make_path (cons f nil)) then eret c
              else failcheck
          | CpStructProj _ _ _ => fail
          | CpStructUpdate _ _ v _ =>
              if is_valid_atom IN v then eret c
              else failcheck
          | CpCall _ args _ =>
              let all_valid := List.forallb (is_valid_atom IN) args in
              if all_valid then eret c else failcheck
          | CpDeepAccess _ _ _ => eret c (* TODO *)
          end
        in
        eret (Imp1Typed.StSet x c')
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
    end.

  Definition check_program (prog: Imp1.Aliasing_AST.program) : res Imp1Typed.program :=
    let* defs := mmap check_globdef (prog_defs prog) in
    eret {|
      prog_defs := defs;
      prog_types := prog_types prog
    |}.

End AliasingCheck.