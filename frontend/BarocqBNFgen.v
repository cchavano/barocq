From Coq Require Import PArith String List.
From compcert Require Import Clightdefs Integers.
From BarocqComp Require Import Ident Error Monads Maps2 Utils Syntax Types Benum Typing Barocq BarocqBNF.
Import ListNotations.
Import MonCounterErr.

(** Normalization *)

Section NORM.

  Variable pure_funs: SSet.t.

  Definition bnfexpr_of_atomlist (e: BarocqTyped.expr) (la: list atom) : res BarocqBNF.expr :=
    match e with
    | BarocqTyped.ECast _ ty =>
        let* a := list_nth_err la 0 in
        eret (EAtom (ACast a ty) ty)
    | BarocqTyped.EUnaryOp op _ ty =>
        let* a := list_nth_err la 0 in
        eret (EAtom (AUnaryOp op a ty) ty)
    | BarocqTyped.EBinaryOp op _ _ ty =>
        let* a1 := list_nth_err la 0 in
        let* a2 := list_nth_err la 1 in
        eret (EAtom (ABinaryOp op a1 a2 ty) ty)
    | BarocqTyped.EArrayGet _ _ ly ty =>
        let* a1 := list_nth_err la 0 in
        let* a2 := list_nth_err la 1 in
        eret (EAtom (AArrayGet a1 a2 ly ty) ty)
    | BarocqTyped.EArraySet _ _ _ ty =>
        let* a1 := list_nth_err la 0 in
        let* a2 := list_nth_err la 1 in
        let* a3 := list_nth_err la 2 in
        eret (EArraySet a1 a2 a3 ty)
    | BarocqTyped.ERecordProj _ x ly ty =>
        let* a := list_nth_err la 0 in
        eret (EAtom (ARecordProj a x ly ty) ty)
    | BarocqTyped.ERecordUpdate _ x _ ty =>
        let* a1 := list_nth_err la 0 in
        let* a2 := list_nth_err la 1 in
        eret (ERecordUpdate a1 x a2 ty)
    | BarocqTyped.EApp (BarocqTyped.EVar f tf) _ ty =>
        let* a := list_nth_err la 0 in
        let args := tail la in
        if SSet.mem f pure_funs then
          eret (EAtom (APureCall f tf args ty) ty)
        else
          eret (EApp a args ty)
    | _ => efail
    end.

  Open Scope state_err_monad_scope.

  Definition fresh_var : crmon ident := Utils.fresh_var_err "b".

  Fixpoint norm_expr_rec (e: BarocqTyped.expr) : crmon BarocqBNF.expr :=
    let fix norm_expr_aux (e: BarocqTyped.expr) : crmon ((smaplist BarocqBNF.expr) * atom) :=
      match e with
      | BarocqTyped.ETrue => ret (nil, ATrue)
      | BarocqTyped.EFalse => ret (nil, AFalse)
      | BarocqTyped.EInt32 i s => ret (nil, AInt32 i s)
      | BarocqTyped.EInt64 i s => ret (nil, AInt64 i s)
      | BarocqTyped.EConstr x n ty => ret (nil, AConstr x n ty)
      | BarocqTyped.EVar x ty => ret (nil, AVar x ty)
      | BarocqTyped.ECast e1 ty =>
          let* (li1, a1) := norm_expr_aux e1 in
          ret (li1, ACast a1 ty)
      | BarocqTyped.EUnaryOp op e1 ty =>
          let* (li, a1) := norm_expr_aux e1 in
          ret (li, AUnaryOp op a1 ty)
      | BarocqTyped.EBinaryOp op e1 e2 ty =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (li2, a2) := norm_expr_aux e2 in
          ret (li1 ++ li2, ABinaryOp op a1 a2 ty)
      | BarocqTyped.EArrayGet e1 e2 ly ty =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (li2, a2) := norm_expr_aux e2 in
          let* x := fresh_var in
          ret (li1 ++ li2, AArrayGet a1 a2 ly ty)
      | BarocqTyped.EArraySet e1 e2 e3 ty =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (li2, a2) := norm_expr_aux e2 in
          let* (li3, a3) := norm_expr_aux e3 in
          let* x := fresh_var in
          ret (li1 ++ li2 ++ li3 ++ [(x, EArraySet a1 a2 a3 ty)], AVar x ty)
      | BarocqTyped.ERecordProj e1 f ly ty =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* x := fresh_var in
          ret (li1, ARecordProj a1 f ly ty)
      | BarocqTyped.ERecordUpdate e1 f e2 ty =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (li2, a2) := norm_expr_aux e2 in
          let* x := fresh_var in
          ret (li1 ++ li2 ++ [(x, ERecordUpdate a1 f a2 ty)], AVar x ty)
      | BarocqTyped.EApp e1 args ty =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (l_args, a_args) :=
            List.fold_left
              (fun acc arg =>
                let* (acc_l, acc_args) := acc in
                let* (lia, a) := norm_expr_aux arg in
                ret (acc_l ++ lia, acc_args ++ [a]))
              args
              (ret ([], []))
          in
          let impure_call :=
            let* x := fresh_var in
            ret (li1 ++ l_args ++ [(x, EApp a1 a_args ty)], AVar x ty)
          in
          match a1 with
          | AVar f tf =>
              if SSet.mem f pure_funs then
                ret (li1 ++ l_args, APureCall f tf a_args ty)
              else impure_call
          | _ => impure_call
          end
      | _ =>
          let* x := fresh_var in
          let* be := norm_expr_rec e in
          ret ((x, be) :: nil, AVar x (BarocqTyped.typof_expr e))
      end
    in
    let fix mk_norm (le: smaplist BarocqBNF.expr) (e: BarocqBNF.expr) : BarocqBNF.expr :=
      let te := BarocqBNF.btypof_expr e in
      let fix mk_rec le :=
        match le with
        | nil => e
        | (x, be) :: le' =>
            ELetIn x be (mk_rec le') te
        end
      in mk_rec le
    in
    let fix norm_exprlist_rec (e: BarocqTyped.expr) (la: list atom) (le: list BarocqTyped.expr) : crmon ((smaplist BarocqBNF.expr) * BarocqBNF.expr) :=
      match le with
      | nil =>
          let* er := lift_err (bnfexpr_of_atomlist e (rev' la)) in
          ret (nil, er)
      | e1 :: le' =>
          let* (lx, a1) := norm_expr_aux e1 in
          let* (lr, er) := norm_exprlist_rec e (a1 :: la) le' in
          ret (lx ++ lr, er)
      end
    in
    let norm_exprlist (e: BarocqTyped.expr) (le: list BarocqTyped.expr) : crmon BarocqBNF.expr :=
      let* (lx, er) := norm_exprlist_rec e [] le in
      ret (mk_norm lx er)
    in
    let fix norm_match_cases (cases: list (pattern * BarocqTyped.expr)) : crmon (list (pattern * BarocqBNF.expr)) :=
      match cases with
      | nil => ret nil
      | (c, e) :: cases' =>
          let* ne := norm_expr_rec e in
          let* ncases' := norm_match_cases cases' in
          ret ((c, ne) :: ncases')
      end
    in
    match e with
    | BarocqTyped.ETrue =>
        ret (EAtom ATrue BBool)
    | BarocqTyped.EFalse =>
        ret (EAtom AFalse BBool)
    | BarocqTyped.EInt32 i s =>
        ret (EAtom (AInt32 i s) (BInt32 s))
    | BarocqTyped.EInt64 i s =>
        ret (EAtom (AInt64 i s) (BInt64 s))
    | BarocqTyped.EConstr x i ty =>
        ret (EAtom (AConstr x i ty) ty)
    | BarocqTyped.EVar x ty =>
        ret (EAtom (AVar x ty) ty)
    | BarocqTyped.ECast e1 ty =>
        norm_exprlist e [e1]
    | BarocqTyped.EUnaryOp op e1 _ =>
        norm_exprlist e [e1]
    | BarocqTyped.EBinaryOp op e1 e2 _ =>
        norm_exprlist e [e1; e2]
    | BarocqTyped.EArrayGet e1 e2 _ _ =>
        norm_exprlist e [e1; e2]
    | BarocqTyped.EArraySet e1 e2 e3 _ =>
        norm_exprlist e [e1; e2; e3]
    | BarocqTyped.ERecordProj e1 k _ _ =>
        norm_exprlist e [e1]
    | BarocqTyped.ERecordUpdate e1 k e2 _ =>
        norm_exprlist e [e1; e2]
    | BarocqTyped.EApp e1 args _ =>
        norm_exprlist e (e1 :: args)
    | BarocqTyped.EIfThenElse e1 e2 e3 ty =>
        let* (le, c) := norm_expr_aux e1 in
        let* ne2 := norm_expr_rec e2 in
        let* ne3 := norm_expr_rec e3 in
        ret (mk_norm le (EIfThenElse c ne2 ne3 ty))
    | BarocqTyped.EMatch e1 cases ty =>
        let* (le, a) := norm_expr_aux e1 in
        let* ncases := norm_match_cases cases in
        ret (mk_norm le (EMatch a ncases ty))
    | BarocqTyped.ELetIn x e1 e2 ty =>
        let* ne1 := norm_expr_rec e1 in
        let* ne2 := norm_expr_rec e2 in
        ret (ELetIn x ne1 ne2 ty)
    | BarocqTyped.EAttr s e =>
        let* ne := norm_expr_rec e in
        ret (EAttr s ne)
  end.
    
  Close Scope state_err_monad_scope.

  Definition norm_expr (e: BarocqTyped.expr) : res BarocqBNF.expr :=
    let* ne := norm_expr_rec e 1%positive in
    eret (fst ne).

  Definition norm_function (f: BarocqTyped.function) : res BarocqBNF.function :=
    let* body_norm := norm_expr (fn_body f) in
    eret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body_norm
    |}.

  Fixpoint norm_program_rec (prog: BarocqTyped.program) : res (BarocqBNF.program) :=
    match prog with
    | nil => eret (mk_program nil nil nil)
    | d :: prog' =>
        let* b_prog := norm_program_rec prog' in
        let '(mk_program b_defs b_types b_tabs) := b_prog in
        match d with
        | BarocqTyped.DefType x td =>
            eret (mk_program b_defs ((x, td) :: b_types) b_tabs)
        | BarocqTyped.DefConst x l ty =>
            let b_defs' := Syntax.DefConst x l ty :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | BarocqTyped.DefFun x f =>
            let* f' := norm_function f in
            let b_defs' := Syntax.DefFun x f' :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | BarocqTyped.DeclType t su =>
            eret (mk_program b_defs b_types ((t, su) :: b_tabs))
        | BarocqTyped.DeclConst x ty =>
            let b_defs' := Syntax.DeclConst x ty :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | BarocqTyped.DeclFun x tparams tret =>
            let b_defs' := Syntax.DeclFun x tparams tret :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        end
    end.

End NORM.

Definition norm_program (arch: Target.archi) (prog: BarocqTyped.program) : res BarocqBNF.program :=
  norm_program_rec (BarocqTyped.pure_functions prog) prog.
  