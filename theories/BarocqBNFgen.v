From Coq Require Import PArith String List.
From compcert Require Import Clightdefs Integers.
From BarocqComp Require Import Monads Error Common Syntax Types Barocq BarocqBNF.
Import ListNotations.
Import MonCounter.

Open Scope error_monad_scope.

Fixpoint atom_of_expr (e: Barocq.expr) : res atom :=
  match e with
  | Barocq.ETrue => eret ATrue
  | Barocq.EFalse => eret AFalse
  | Barocq.EInt32 i => eret (AInt32 i)
  | Barocq.EInt64 i => eret (AInt64 i)
  | Barocq.EVar x => eret (AVar (transl_user_ident x))
  | Barocq.EUnaryOp op e1 =>
      let* a1 := atom_of_expr e1 in
      eret (AUnaryOp op a1)
  | Barocq.EBinaryOp op e1 e2 =>
      let* a1 := atom_of_expr e1 in
      let* a2 := atom_of_expr e2 in
      eret (ABinaryOp op a1 a2)
  | _ => fail
  end.

Close Scope error_monad_scope.

Open Scope state_monad_scope.

Section NORMEXPR.

  Definition fresh_var : cmon ident := Common.fresh_var "b".
  
  Fixpoint normalize_app (normalize_expr: Barocq.expr -> cmon BarocqBNF.expr) (f: ident) 
    (args: list Barocq.expr) (vars: list atom) : cmon BarocqBNF.expr :=
    match args with
    | nil => ret (EApp (AVar f) (rev' vars))
    | e :: args' => 
        let* xe := fresh_var in
        let* be := normalize_expr e in
        let* ber := normalize_app normalize_expr f args' ((AVar xe) :: vars) in
        ret (ELetIn xe be ber)
    end.

  Fixpoint normalize_expr_rec (e: Barocq.expr) : cmon BarocqBNF.expr :=
    match e with
    | Barocq.ETrue => ret (EAtom ATrue)
    | Barocq.EFalse => ret (EAtom AFalse)
    | Barocq.EInt32 i => ret (EAtom (AInt32 i))
    | Barocq.EInt64 i => ret (EAtom (AInt64 i))
    | Barocq.EVar x => ret (EAtom (AVar (transl_user_ident x)))
    | Barocq.EUnaryOp op e1 =>
        match atom_of_expr e with
        | OK a => ret (EAtom a)
        | Error _ =>
            let* x1 := fresh_var in
            let* be1 := normalize_expr_rec e1 in
            ret (ELetIn x1 be1 (EAtom (AUnaryOp op (AVar x1))))
        end
    | Barocq.EBinaryOp op e1 e2 =>
        match atom_of_expr e with
        | OK a => ret (EAtom a)
        | Error _ =>
            let* x1 := fresh_var in
            let* be1 := normalize_expr_rec e1 in
            let* x2 := fresh_var in
            let* be2 := normalize_expr_rec e2 in
            ret
              (ELetIn x1 be1
                (ELetIn x2 be2
                  (EAtom (ABinaryOp op (AVar x1) (AVar x2)))))
        end
    | Barocq.EArrayGet e1 e2 =>
        let* x1 := fresh_var in
        let* be1 := normalize_expr_rec e1 in
        let* x2 := fresh_var in
        let* be2 := normalize_expr_rec e2 in
        ret
          (ELetIn x1 be1
            (ELetIn x2 be2
              (EArrayGet (AVar x1) (AVar x2))))
    | Barocq.EArraySet e1 e2 e3 =>
        let* x1 := fresh_var in
        let* be1 := normalize_expr_rec e1 in
        let* x2 := fresh_var in
        let* be2 := normalize_expr_rec e2 in
        let* x3:= fresh_var in
        let* be3 := normalize_expr_rec e3 in
        ret
          (ELetIn x1 be1
            (ELetIn x2 be2
              (ELetIn x3 be3
                (EArraySet (AVar x1) (AVar x2) (AVar x3)))))
    | Barocq.EStructProj e1 k =>
        let* x1 := fresh_var in
        let* be1 := normalize_expr_rec e1 in
        ret
          (ELetIn x1 be1
            (EStructProj (AVar x1) k))
    | Barocq.EStructUpdate e1 k e2 =>
        let* x1 := fresh_var in
        let* be1 := normalize_expr_rec e1 in
        let* x2 := fresh_var in
        let* be2 := normalize_expr_rec e2 in
        ret
          (ELetIn x1 be1
            (ELetIn x2 be2
              (EStructUpdate (AVar x1) k (AVar x2))))
    | Barocq.EApp e1 args =>
        let* x1 := fresh_var in
        let* be1 := normalize_expr_rec e1 in
        let* bapp := normalize_app normalize_expr_rec x1 args nil in
        ret (ELetIn x1 be1 bapp)
    | Barocq.EIfThenElse e1 e2 e3 =>
        let* x1 := fresh_var in
        let* be1 := normalize_expr_rec e1 in
        let* be2 := normalize_expr_rec e2 in
        let* be3 := normalize_expr_rec e3 in
        ret
          (ELetIn x1 be1
            (EIfThenElse (AVar x1) be2 be3))
    | Barocq.ELetIn x e1 e2 =>
        let* be1 := normalize_expr_rec e1 in
        let* be2 := normalize_expr_rec e2 in
        ret (ELetIn (transl_user_ident x) be1 be2)
    end.

End NORMEXPR.

Close Scope state_monad_scope.
      
Definition normalize_expr (e: Barocq.expr) : BarocqBNF.expr :=
  fst (normalize_expr_rec e 0).

Fixpoint atom_subst (vars: ptree atom) (a: atom) : atom :=
  match a with
  | AVar x =>
      match tget vars x with
      | Some a' => a'
      | None => a
      end
  | AUnaryOp op a1 =>
      AUnaryOp op (atom_subst vars a1)
  | ABinaryOp op a1 a2 =>
      ABinaryOp op (atom_subst vars a1) (atom_subst vars a2)
  | _ => a
  end.

Fixpoint simplify_expr_rec (vars: ptree atom) (e: BarocqBNF.expr) : BarocqBNF.expr :=
  match e with
  | EAtom a => EAtom (atom_subst vars a)
  | EArrayGet a1 a2 =>
      let a1' := atom_subst vars a1 in
      let a2' := atom_subst vars a2 in
      EArrayGet a1' a2'
  | EArraySet a1 a2 a3 =>
      let a1' := atom_subst vars a1 in
      let a2' := atom_subst vars a2 in
      let a3' := atom_subst vars a3 in
      EArraySet a1' a2' a3'
  | EStructProj a x =>
      let a' := atom_subst vars a in
      EStructProj a' x
  | EStructUpdate a1 x a2 =>
      let a1' := atom_subst vars a1 in
      let a2' := atom_subst vars a2 in
      EStructUpdate a1' x a2'
  | EApp a args =>
      let a' := atom_subst vars a in
      let args' := map (atom_subst vars) args in
      EApp a' args'
  | EIfThenElse a e1 e2 =>
      let a' := atom_subst vars a in
      let e1' := simplify_expr_rec vars e1 in
      let e2' := simplify_expr_rec vars e2 in
      EIfThenElse a' e1' e2'
  | ELetIn x e1 e2 =>
      let simpl_let (_: unit) :=
        let e1' := simplify_expr_rec vars e1 in
        let e2' := simplify_expr_rec vars e2 in
        ELetIn x e1' e2'
      in
      if prefix "b" (string_of_ident x) then
        match e1 with
        | EAtom a =>
            let vars' := tset vars x (atom_subst vars a) in
            simplify_expr_rec vars' e2
        | _ => simpl_let tt
        end
      else
        simpl_let tt
  end.

Definition simplify_expr (e: BarocqBNF.expr) : BarocqBNF.expr :=
  simplify_expr_rec tempty e.

Definition normalize_params (params: list (ident * ctyp)) : list (ident * ctyp) :=
  map (fun '(x, tx) => (transl_user_ident x, tx)) params.

Definition normalize_function (fsimpl: bool) (f: Barocq.function): BarocqBNF.function :=
  let body_norm := normalize_expr (fn_body f) in
  {|
    fn_return := fn_return f;
    fn_params := normalize_params (fn_params f);
    fn_body := if fsimpl then simplify_expr body_norm else body_norm
  |}.

Local Open Scope error_monad_scope.

Fixpoint normalize_program_rec (fsimpl: bool) (ts: types) (prog: Barocq.program) : res BarocqBNF.program :=
  match prog with
  | nil =>
      eret {|
        prog_defs := nil;
        prog_types := ts
      |}
  | d :: prog' =>
      match d with
      | Barocq.DefStruct a fields =>
          let* ts' := types_update ts a fields in
          normalize_program_rec fsimpl ts' prog'
      | Barocq.DefConst x l ty =>
          let* r := normalize_program_rec fsimpl ts prog' in
          eret {|
            prog_defs := (Syntax.DefConst (transl_user_ident x) l ty) :: (prog_defs r);
            prog_types := (prog_types r)
          |}
      | Barocq.DefFun x f =>
          let f' := normalize_function fsimpl f in
          let* r := normalize_program_rec fsimpl ts prog' in
          eret {|
            prog_defs := (Syntax.DefFun (transl_user_ident x) f') :: (prog_defs r);
            prog_types := prog_types r
          |}
      end
  end.

Definition normalize_program (fsimpl: bool) (prog: Barocq.program) : res BarocqBNF.program :=
  normalize_program_rec fsimpl tempty prog.