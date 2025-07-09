From Coq Require Import PArith String List.
From compcert Require Import Clightdefs Integers.
From BarocqComp Require Import Error Monads Utils Syntax Types Typing Barocq BarocqTransf BarocqBNF.
Import ListNotations.
Import MonCounterErr.

(** Normalization *)

Fixpoint atom_of_expr (e: Barocq.expr) : res atom :=
  match e with
  | Barocq.ETrue => eret ATrue
  | Barocq.EFalse => eret AFalse
  | Barocq.EInt32 i s => eret (AInt32 i s)
  | Barocq.EInt64 i s => eret (AInt64 i s)
  | Barocq.EVar x => eret (AVar x)
  | Barocq.ECast e1 ty =>
      let* a1 := atom_of_expr e1 in
      eret (ACast a1 ty)
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
  | Barocq.ECast _ ty =>
      let* a := nth_err la 0 in
      eret (EAtom (ACast a ty))
  | Barocq.EUnaryOp op _ =>
      let* a := nth_err la 0 in
      eret (EAtom (AUnaryOp op a))
  | Barocq.EBinaryOp op _ _ =>
      let* a1 := nth_err la 0 in
      let* a2 := nth_err la 1 in
      match op with
      | BopAndbool =>
          eret (EIfThenElse a1 (EAtom a2) (EAtom AFalse))
      | BopOrbool =>
          eret (EIfThenElse a1 (EAtom ATrue) (EAtom a2))
      | _ => eret (EAtom (ABinaryOp op a1 a2))
      end
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

Definition fresh_var : crmon ident := Utils.fresh_var_err "b".

Fixpoint norm_expr_rec (e: Barocq.expr) : crmon BarocqBNF.expr :=
  let fix norm_exprlist_rec (e: Barocq.expr) (le: list Barocq.expr) (la: list atom) : crmon BarocqBNF.expr :=
    match le with
    | nil => lift_err (spread_atomlist e (rev' la))
    | e1 :: le' =>
        match atom_of_expr e1 with
        | OK a => norm_exprlist_rec e le' (a :: la)
        | Error _ =>
            let* x := fresh_var in
            let* ne1 := norm_expr_rec e1 in
            let* ler := norm_exprlist_rec e le' (AVar x :: la) in
            ret (ELetIn x ne1 ler)
        end
    end
  in
  let norm_exprlist (e: Barocq.expr) (le: list Barocq.expr) : crmon BarocqBNF.expr :=
    norm_exprlist_rec e le nil
  in
  let fix norm_access_list_rec (a: atom) (acs: list Barocq.access) (acs_norm: list Syntax.access)
    : crmon BarocqBNF.expr :=
    match acs with
    | nil => ret (EDeepAccess a (rev acs_norm))
    | ac :: acs' =>
        match ac with
        | Barocq.AcStructField f =>
            norm_access_list_rec a acs' (Syntax.AcStructField f :: acs_norm)
        | Barocq.AcArrayIndex e =>
            match atom_of_expr e with
            | OK ae => norm_access_list_rec a acs' ((Syntax.AcArrayIndex ae) :: acs_norm)
            | Error _ =>
              let* xe := fresh_var in
              let* be := norm_expr_rec e in
              let* ber := norm_access_list_rec a acs' ((Syntax.AcArrayIndex (AVar xe)) :: acs_norm) in
              ret (ELetIn xe be ber)
            end
        end
    end
  in
  let norm_deep_access (e: Barocq.expr) (acs: list Barocq.access) : crmon BarocqBNF.expr :=
    match atom_of_expr e with
    | OK a => norm_access_list_rec a acs nil
    | Error _ =>
        let* x := fresh_var in
        let* be := norm_expr_rec e in
        let* bacs := norm_access_list_rec (AVar x) acs nil in
        ret (ELetIn x be bacs)
    end
  in
  let fix norm_ite_cond (e: Barocq.expr) : crmon (list (ident * BarocqBNF.expr) * atom) :=
    match e with
    | ETrue => ret (nil, ATrue)
    | EFalse => ret (nil, AFalse)
    | Barocq.EInt32 i s => ret (nil, AInt32 i s)
    | Barocq.EInt64 i s => ret (nil, AInt64 i s)
    | Barocq.EVar x => ret (nil, AVar x)
    | Barocq.ECast e1 ty =>
      let* (li1, a1) := norm_ite_cond e1 in
      ret (li1, ACast a1 ty)
    | EUnaryOp op e1 =>
        let* (li, a1) := norm_ite_cond e1 in
        ret (li, AUnaryOp op a1)
    | EBinaryOp op e1 e2 =>
        let* (li1, a1) := norm_ite_cond e1 in
        let* (li2, a2) := norm_ite_cond e2 in
        ret (li1 ++ li2, ABinaryOp op a1 a2)
    | _ =>
        let* x := fresh_var in
        let* be := norm_expr_rec e in
        ret ((x, be) :: nil, AVar x)
    end
  in
  let fix norm_ite (le: list (ident * BarocqBNF.expr)) (c: atom) (a: BarocqBNF.expr) (b: BarocqBNF.expr) : crmon BarocqBNF.expr :=
    match le with
    | nil => ret (EIfThenElse c a b)
    | (x, be) :: le' =>
        let* ber := norm_ite le' c a b in
        ret (ELetIn x be ber)
    end
  in
  match e with
  | Barocq.ETrue =>
      ret (EAtom ATrue)
  | Barocq.EFalse =>
      ret (EAtom AFalse)
  | Barocq.EInt32 i s =>
      ret (EAtom (AInt32 i s))
  | Barocq.EInt64 i s =>
      ret (EAtom (AInt64 i s))
  | Barocq.EVar x =>
      ret (EAtom (AVar x))
  | Barocq.ECast e1 ty =>
      norm_exprlist e [e1]
  | Barocq.EUnaryOp op e1 =>
      norm_exprlist e [e1]
  | Barocq.EBinaryOp op e1 e2 =>
      norm_exprlist e [e1; e2]
  | Barocq.EArrayGet e1 e2 =>
      norm_exprlist e [e1; e2]
  | Barocq.EArraySet e1 e2 e3 =>
      norm_exprlist e [e1; e2; e3]
  | Barocq.EStructProj e1 k =>
      norm_exprlist e [e1]
  | Barocq.EStructUpdate e1 k e2 =>
      norm_exprlist e [e1; e2]
  | Barocq.EDeepAccess e1 acs =>
      norm_deep_access e1 acs
  | Barocq.EApp e1 args =>
      norm_exprlist e (e1 :: args)
  | Barocq.EIfThenElse e1 e2 e3 =>
      let* ne2 := norm_expr_rec e2 in
      let* ne3 := norm_expr_rec e3 in
      match atom_of_expr e1 with
      | OK a => ret (EIfThenElse a ne2 ne3)
      | Error _ =>
          let* (le, c) := norm_ite_cond e1 in
          norm_ite le c ne2 ne3
      end
  | Barocq.ELetIn x e1 e2 =>
      let* ne1 := norm_expr_rec e1 in
      let* ne2 := norm_expr_rec e2 in
      ret (ELetIn x ne1 ne2)
  end.
  
Close Scope state_err_monad_scope.

Definition norm_expr (e: Barocq.expr) : res BarocqBNF.expr :=
  let* ne := norm_expr_rec e 0 in
  eret (fst ne).

Definition norm_function (f: Barocq.function) : res BarocqBNF.function :=
  let* body_norm := norm_expr (fn_body f) in
  eret {|
    fn_return := fn_return f;
    fn_params := fn_params f;
    fn_body := body_norm
  |}.

Fixpoint norm_program_rec (prog: Barocq.program) : res (list BarocqBNF.globdef * list type_def) :=
  match prog with
  | nil => eret (nil, nil)
  | d :: prog' =>
      match d with
      | Barocq.DefType a fields =>
          let* (ndefs, types) := norm_program_rec prog' in
          eret (ndefs, TdStruct {| sd_name := a; sd_fields := fields |} :: types)
      | Barocq.DefConst x l ty =>
          let* (ndefs, types) := norm_program_rec prog' in
          eret (Syntax.DefConst x l ty :: ndefs, types)
      | Barocq.DefFun x f =>
          let* f' := norm_function f in
          let* (ndefs, types) := norm_program_rec prog' in
          eret (Syntax.DefFun x f' :: ndefs, types)
      | Barocq.DeclType t tk =>
          let* (ndefs, types) := norm_program_rec prog' in
          eret (ndefs, TdAbstract t tk :: types)
      | Barocq.DeclConst x ty =>
          let* (ndefs, types) := norm_program_rec prog' in
          eret (Syntax.DeclConst x ty :: ndefs, types)
      | Barocq.DeclFun x tparams tret =>
          let* (ndefs, types) := norm_program_rec prog' in
          eret (Syntax.DeclFun x tparams tret :: ndefs, types)
      end
  end.

Definition norm_program (prog: Barocq.program) : res BarocqBNF.program :=
  let* prog := BarocqTransf.transf_program prog in
  let* (defs, types) := norm_program_rec prog in
  eret {|
    Syntax.prog_defs := defs;
    Syntax.prog_types := types
  |}.