From Coq Require Import PArith String List.
From compcert Require Import Clightdefs Integers.
From BarocqComp Require Import Monads Error Common Syntax Types Barocq BarocqBNF.
Import ListNotations.
Import MonCounter.

Fixpoint split_deep_access_rec (e: BarocqTyped.expr) (acs: list BarocqTyped.access) : BarocqTyped.expr :=
  match acs with
  | nil => e
  | ac :: acs' =>
      match ac with
      | BarocqTyped.StructField f ty =>
          BarocqTyped.EStructProj (split_deep_access_rec e acs') f ty
      | BarocqTyped.ArrayIndex e1 ty =>
          BarocqTyped.EArrayGet (split_deep_access_rec e acs') e1 ty
      end
  end.

Fixpoint split_deep_access (e: Barocq.Typed.expr) : Barocq.Typed.expr :=
  match e with
  | BarocqTyped.EDeepAccess e1 acs ty =>
      match ty with
      | CBool | CInt32 _ | CInt64 _ => e
      | _ =>
        let e1' := split_deep_access e1 in
        split_deep_access_rec e1' (List.rev' acs)
      end
  | BarocqTyped.EUnaryOp op e1 ty =>
      BarocqTyped.EUnaryOp op (split_deep_access e1) ty
  | BarocqTyped.EBinaryOp op e1 e2 ty =>
      let e1' := split_deep_access e1 in
      let e2' := split_deep_access e2 in
      BarocqTyped.EBinaryOp op e1' e2' ty
  | BarocqTyped.EArrayGet e1 e2 ty =>
      let e1' := split_deep_access e1 in
      let e2' := split_deep_access e2 in
      BarocqTyped.EArrayGet e1' e2' ty
  | BarocqTyped.EArraySet e1 e2 e3 ty =>
      let e1' := split_deep_access e1 in
      let e2' := split_deep_access e2 in
      let e3' := split_deep_access e3 in
      BarocqTyped.EArraySet e1' e2' e3' ty
  | BarocqTyped.EStructProj e1 f ty =>
      let e1' := split_deep_access e1 in
      BarocqTyped.EStructProj e1' f ty
  | BarocqTyped.EStructUpdate e1 f e2 ty =>
      let e1' := split_deep_access e1 in
      let e2' := split_deep_access e2 in
      BarocqTyped.EStructUpdate e1' f e2' ty
  | BarocqTyped.EApp e1 args ty =>
      let e1' := split_deep_access e1 in
      let args' := List.map split_deep_access args in
      BarocqTyped.EApp e1' args' ty
  | BarocqTyped.EIfThenElse e1 e2 e3 ty =>
      let e1' := split_deep_access e1 in
      let e2' := split_deep_access e2 in
      let e3' := split_deep_access e3 in
      BarocqTyped.EIfThenElse e1' e2' e3' ty
  | BarocqTyped.ELetIn x e1 e2 ty =>
      let e1' := split_deep_access e1 in
      let e2' := split_deep_access e2 in
      BarocqTyped.ELetIn x e1' e2' ty
  | _ => e
  end.
  

Fixpoint atom_of_expr (e: Barocq.expr) : res atom :=
  match e with
  | Barocq.ETrue => eret ATrue
  | Barocq.EFalse => eret AFalse
  | Barocq.EInt32 i s => eret (AInt32 i s)
  | Barocq.EInt64 i s => eret (AInt64 i s)
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

Open Scope state_monad_scope.

Definition fresh_var : cmon ident := Common.fresh_var "b".

Section NORMEXPR.

  Variable normalize_expr : Barocq.expr -> cmon BarocqBNF.expr.
  
  Fixpoint normalize_app (f: ident) (args: list Barocq.expr) (vars: list atom) : cmon BarocqBNF.expr :=
    match args with
    | nil => ret (EApp (AVar f) (rev' vars))
    | e :: args' => 
        let* xe := fresh_var in
        let* be := normalize_expr e in
        let* ber := normalize_app f args' ((AVar xe) :: vars) in
        ret (ELetIn xe be ber)
    end.

  Fixpoint normalize_access_list (a: atom) (acs: list Barocq.access) (acs_norm: list Syntax.access)
    : cmon BarocqBNF.expr :=
    match acs with
    | nil => ret (EDeepAccess a (rev acs_norm))
    | ac :: acs' =>
        match ac with
        | Barocq.StructField f =>
            normalize_access_list a acs' (Syntax.StructField f :: acs_norm)
        | Barocq.ArrayIndex e =>
            match atom_of_expr e with
            | OK ae => normalize_access_list a acs' ((Syntax.ArrayIndex ae) :: acs_norm)
            | Error _ =>
              let* xe := fresh_var in
              let* be := normalize_expr e in
              let* ber := normalize_access_list a acs' ((Syntax.ArrayIndex (AVar xe)) :: acs_norm) in
              ret (ELetIn xe be ber)
            end
        end
    end.

End NORMEXPR.

Fixpoint normalize_expr_rec (e: Barocq.expr) : cmon BarocqBNF.expr :=
  match e with
  | Barocq.ETrue => ret (EAtom ATrue)
  | Barocq.EFalse => ret (EAtom AFalse)
  | Barocq.EInt32 i s => ret (EAtom (AInt32 i s))
  | Barocq.EInt64 i s => ret (EAtom (AInt64 i s))
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
  | Barocq.EDeepAccess e1 acs =>
      match atom_of_expr e1 with
      | OK a => normalize_access_list normalize_expr_rec a acs nil
      | Error _ =>
          let* x1 := fresh_var in
          let* be1 := normalize_expr_rec e1 in
          let* bacs := normalize_access_list normalize_expr_rec (AVar x1) acs nil in
          ret (ELetIn x1 be1 bacs)
      end
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

Close Scope state_monad_scope.
      
Definition normalize_expr (e: BarocqTyped.expr) : BarocqBNF.expr :=
  let e' := split_deep_access e in
  let eu := untype_expr e' in
  fst (normalize_expr_rec eu 0).

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
  | EDeepAccess a acs =>
      let a' := atom_subst vars a in
      let acs' :=
        map
          (fun ac =>
            match ac with
            | Syntax.StructField f => Syntax.StructField f
            | Syntax.ArrayIndex ai => Syntax.ArrayIndex (atom_subst vars ai)
            end)
        acs
      in
      EDeepAccess a' acs'
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

Definition normalize_function (fsimpl: bool) (f: BarocqTyped.function): BarocqBNF.function :=
  let body_norm := normalize_expr (fn_body f) in
  {|
    fn_return := fn_return f;
    fn_params := normalize_params (fn_params f);
    fn_body := if fsimpl then simplify_expr body_norm else body_norm
  |}.

Fixpoint normalize_program_rec (fsimpl: bool) (ts: types) (prog: BarocqTyped.program) : res BarocqBNF.program :=
  match prog with
  | nil =>
      eret {|
        prog_defs := nil;
        prog_types := ts
      |}
  | d :: prog' =>
      match d with
      | BarocqTyped.DefStruct a fields =>
          let* ts' := types_update ts a fields in
          normalize_program_rec fsimpl ts' prog'
      | BarocqTyped.DefConst x l ty =>
          let* r := normalize_program_rec fsimpl ts prog' in
          eret {|
            prog_defs := (Syntax.DefConst (transl_user_ident x) l ty) :: (prog_defs r);
            prog_types := (prog_types r)
          |}
      | BarocqTyped.DefFun x f =>
          let f' := normalize_function fsimpl f in
          let* r := normalize_program_rec fsimpl ts prog' in
          eret {|
            prog_defs := (Syntax.DefFun (transl_user_ident x) f') :: (prog_defs r);
            prog_types := prog_types r
          |}
      end
  end.

Definition normalize_program (fsimpl: bool) (prog: BarocqTyped.program) : res BarocqBNF.program :=
  normalize_program_rec fsimpl tempty prog.