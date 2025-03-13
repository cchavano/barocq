From Coq Require Import PArith String List.
From compcert Require Import Clightdefs Integers.
From BarocqComp Require Import Error Monads Common Syntax Types Barocq BarocqBNF.
Import ListNotations.
Import MonCounterErr.

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
  | _ => MonError.fail
  end.

Definition spread_atomlist (e: Barocq.expr) (la: list atom) : res BarocqBNF.expr :=
  match e with
  | Barocq.EUnaryOp op _ =>
      let* a := nth_err la 0 in
      eret (EAtom (AUnaryOp op a))
  | Barocq.EBinaryOp op _ _ =>
      let* a1 := nth_err la 0 in
      let* a2 := nth_err la 1 in
      eret (EAtom (ABinaryOp op a1 a2))
  | Barocq.EArrayGet _ _ =>
      let* a1 := nth_err la 0 in
      let* a2 := nth_err la 1 in
      eret (EArrayGet a1 a2)
  | Barocq.EArraySet _ _ _ =>
      let* a1 := nth_err la 0 in
      let* a2 := nth_err la 1 in
      let* a3 := nth_err la 2 in
      eret (EArraySet a1 a2 a3)
  | Barocq.EStructProj _ x =>
      let* a := nth_err la 0 in
      eret (EStructProj a x)
  | Barocq.EStructUpdate _ x _ =>
      let* a1 := nth_err la 0 in
      let* a2 := nth_err la 1 in
      eret (EStructUpdate a1 x a2)
  | Barocq.EApp _ _ =>
      let* a := nth_err la 0 in
      let args := tail la in
      eret (EApp a args)
  | _ => MonError.fail
  end.

Open Scope state_err_monad_scope.

Definition fresh_var : crmon ident := Common.fresh_var_err "b".

Fixpoint normalize_expr_rec (e: Barocq.expr) : crmon BarocqBNF.expr :=
  let fix normalize_exprlist_rec (e: Barocq.expr) (le: list Barocq.expr) (la: list atom) : crmon BarocqBNF.expr :=
    match le with
    | nil => lift_err (spread_atomlist e (rev' la))
    | e1 :: le' =>
        match atom_of_expr e1 with
        | OK a => normalize_exprlist_rec e le' (a :: la)
        | Error _ =>
            let* x := fresh_var in
            let* ne1 := normalize_expr_rec e1 in
            let* ler := normalize_exprlist_rec e le' (AVar x :: la) in
            ret (ELetIn x ne1 ler)
        end
    end
  in
  let normalize_exprlist (e: Barocq.expr) (le: list Barocq.expr) : crmon BarocqBNF.expr :=
    normalize_exprlist_rec e le nil
  in
  match e with
  | Barocq.ETrue =>
      ret (EAtom ATrue)
  | Barocq.EFalse =>
      ret (EAtom AFalse)
  | Barocq.EInt32 i =>
      ret (EAtom (AInt32 i))
  | Barocq.EInt64 i =>
      ret (EAtom (AInt64 i))
  | Barocq.EVar x =>
      ret (EAtom (AVar (transl_user_ident x)))
  | Barocq.EUnaryOp op e1 =>
      normalize_exprlist e [e1]
  | Barocq.EBinaryOp op e1 e2 =>
      normalize_exprlist e [e1; e2]
  | Barocq.EArrayGet e1 e2 =>
      normalize_exprlist e [e1; e2]
  | Barocq.EArraySet e1 e2 e3 =>
      normalize_exprlist e [e1; e2; e3]
  | Barocq.EStructProj e1 k =>
      normalize_exprlist e [e1]
  | Barocq.EStructUpdate e1 k e2 =>
      normalize_exprlist e [e1; e2]
  | Barocq.EApp e1 args =>
      normalize_exprlist e (e1 :: args)
  | Barocq.EIfThenElse e1 e2 e3 =>
      let* ne2 := normalize_expr_rec e2 in
      let* ne3 := normalize_expr_rec e3 in
      match atom_of_expr e1 with
      | OK a => ret (EIfThenElse a ne2 ne3)
      | Error _ =>
          let* x1 := fresh_var in
          let* ne1 := normalize_expr_rec e1 in
          ret (ELetIn x1 ne1 (EIfThenElse (AVar x1) ne2 ne3))
      end
  | Barocq.ELetIn x e1 e2 =>
      let* ne1 := normalize_expr_rec e1 in
      let* ne2 := normalize_expr_rec e2 in
      ret (ELetIn (transl_user_ident x) ne1 ne2)
  end.

Close Scope state_err_monad_scope.

Definition normalize_expr (e: Barocq.expr) : res BarocqBNF.expr :=
  let* ne := normalize_expr_rec e 0 in
  eret (fst ne).

Definition normalize_params (params: list (ident * ctyp)) : list (ident * ctyp) :=
  map (fun '(x, tx) => (transl_user_ident x, tx)) params.

Definition normalize_function (f: Barocq.function) : res BarocqBNF.function :=
  let* body_norm := normalize_expr (fn_body f) in
  eret {|
    fn_return := fn_return f;
    fn_params := normalize_params (fn_params f);
    fn_body := body_norm
  |}.

Fixpoint normalize_program_rec (ts: types) (prog: Barocq.program) : res BarocqBNF.program :=
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
          normalize_program_rec ts' prog'
      | Barocq.DefConst x l ty =>
          let* r := normalize_program_rec ts prog' in
          eret {|
            prog_defs := (Syntax.DefConst (transl_user_ident x) l ty) :: (prog_defs r);
            prog_types := (prog_types r)
          |}
      | Barocq.DefFun x f =>
          let* f' := normalize_function f in
          let* r := normalize_program_rec ts prog' in
          eret {|
            prog_defs := (Syntax.DefFun (transl_user_ident x) f') :: (prog_defs r);
            prog_types := prog_types r
          |}
      end
  end.

Definition normalize_program (prog: Barocq.program) : res BarocqBNF.program :=
  normalize_program_rec tempty prog.

    