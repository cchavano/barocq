From Stdlib Require Import PArith String List.
From compcert Require Import Clightdefs Integers.
From BarocqComp Require Import Ident Res StateMonads Maps2 Utils Syntax Types Benum Typing Barocq BarocqBNF.
Import ListNotations.

Local Open Scope error_monad_scope.

(** Normalization *)


Section NORM.

  Variable pure_funs: SSet.t.

  Definition bnfexpr_of_atomlist (e: BarocqTyped.expr) (la: list atom) : res BarocqBNF.expr :=
    match e with
    | BarocqTyped.ECast _ ty =>
        do a <- list_nth_err la 0;
        eret (EAtom (ACast a ty))
    | BarocqTyped.EUnaryOp op _ ty =>
        do a <- list_nth_err la 0;
        eret (EAtom (AUnaryOp op a ty))
    | BarocqTyped.EBinaryOp op _ _ ty =>
        do a1 <- list_nth_err la 0;
        do a2 <- list_nth_err la 1;
        eret (EAtom (ABinaryOp op a1 a2 ty))
    | BarocqTyped.EArrayGet _ _ ly ty =>
        do a1 <- list_nth_err la 0;
        do a2 <- list_nth_err la 1;
        eret (EAtom (AArrayGet a1 a2 ly ty))
    | BarocqTyped.EArraySet _ _ _ ty =>
        do a1 <- list_nth_err la 0;
        do a2 <- list_nth_err la 1;
        do a3 <- list_nth_err la 2;
        eret (EArraySet a1 a2 a3 ty)
    | BarocqTyped.ERecordProj _ x ly ty =>
        do a <- list_nth_err la 0;
        eret (EAtom (ARecordProj a x ly ty))
    | BarocqTyped.ERecordUpdate _ x _ ty =>
        do a1 <- list_nth_err la 0;
        do a2 <- list_nth_err la 1;
        eret (ERecordUpdate a1 x a2 ty)
    | BarocqTyped.EApp (BarocqTyped.EVar f tf) _ ty =>
        do a <- list_nth_err la 0;
        let args := tail la in
        if SSet.mem f pure_funs then
          eret (EAtom (APureCall f tf args ty))
        else
          eret (EApp a args ty)
    | _ => efail
    end.

  Fixpoint atom_of_expr (e:BarocqTyped.expr) : res atom :=
    match e with
    | BarocqTyped.ETrue => eret ATrue
    | BarocqTyped.EFalse => eret AFalse
    | BarocqTyped.EInt32 i s => eret (AInt32 i s)
    | BarocqTyped.EInt64 i s => eret (AInt64 i s)
    | BarocqTyped.EConstr id i bt => eret (AConstr id i bt)
    | BarocqTyped.EVar id bt => eret (AVar id bt)
    | BarocqTyped.ECast e bt =>
        do a <- atom_of_expr e ;
        eret (ACast a bt)
    | BarocqTyped.EUnaryOp op e bt =>
        do a <- atom_of_expr e;
        eret (AUnaryOp op a bt)
    | BarocqTyped.EBinaryOp op e1 e2 bt =>
        do a1 <- atom_of_expr e1;
        do a2 <- atom_of_expr e2;
        eret (ABinaryOp op a1 a2 bt)
    | BarocqTyped.EArrayGet e1 e2 ly bt =>
        do a1 <- atom_of_expr e1;
        do a2 <- atom_of_expr e2;
        eret (AArrayGet a1 a2 ly bt)
    | BarocqTyped.EArraySet _ _ _ _ => Error (msg "array set is not an atom")
    | BarocqTyped.ERecordProj e1 id ly bt =>
        do a1 <- atom_of_expr e1;
        eret (ARecordProj a1 id ly bt)
    | BarocqTyped.ERecordUpdate _ _ _ _ => Error (msg "record update is not an atom")
    | BarocqTyped.EApp e1 l1 bt =>
        match e1 with
        | BarocqTyped.EVar x bt =>  if negb (SSet.mem x pure_funs)
                        then Error (msg "function should be pure")
                        else
                          do l1 <- mmap atom_of_expr l1;
                          eret (APureCall x bt l1 bt)
        | _ => Error (msg "function should be a function name")
        end
  | BarocqTyped.EIfThenElse  _ _ _ _ => Error (msg "conditional is not an atom")
  | BarocqTyped.EMatch _ _ _ => Error (msg "match is not an atom")
  | BarocqTyped.ELetIn _ _ _ _ => Error (msg "let is not an atom")
  | BarocqTyped.EActR _ _      => Error (msg "a (activation) record  is not an atom")
  | BarocqTyped.ELetW _ _ _ _ _ _  => Error (msg "a loop is not an atom")
  | BarocqTyped.EAttr _ _ => Error (msg "an attribute is not an atom")
    end.


  Close Scope error_monad_scope.

  Import MonCounterErr.

  Local Open Scope state_err_monad_scope.

  Definition fresh_var : crmon ident := Utils.fresh_var_err "b".

  Section NORMINIT.
    Variable norm_expr_rec : BarocqTyped.expr -> crmon BarocqBNF.expr.

    Fixpoint norm_while_init (l:list (ident * BarocqTyped.expr)) : crmon (list  (ident * BarocqBNF.expr)) :=
      match l with
      | nil => sret nil
      | (v,e)::l => do e1 <- norm_expr_rec e;
                    do l1 <- norm_while_init l;
                    sret ((v,e1) ::l1)
      end.
  End NORMINIT.

  Fixpoint letseq (le:smaplist BarocqBNF.expr) (e:BarocqBNF.expr) (bt:btyp) : BarocqBNF.expr :=
    match le with
    | nil => e
    | (x,be) :: le' => ELetIn x be (letseq le' e bt) bt
    end.

  Section NORMAUX.
    Variable norm_expr_rec : BarocqTyped.expr -> crmon BarocqBNF.expr.


    Fixpoint norm_expr_aux (e: BarocqTyped.expr) : crmon ((smaplist BarocqBNF.expr) * atom) :=
      match e with
      | BarocqTyped.ETrue => sret (nil, ATrue)
      | BarocqTyped.EFalse => sret (nil, AFalse)
      | BarocqTyped.EInt32 i s => sret (nil, AInt32 i s)
      | BarocqTyped.EInt64 i s => sret (nil, AInt64 i s)
      | BarocqTyped.EConstr x n ty => sret (nil, AConstr x n ty)
      | BarocqTyped.EVar x ty => sret (nil, AVar x ty)
      | BarocqTyped.ECast e1 ty =>
          do (li1, a1) <- norm_expr_aux e1;
          sret (li1, ACast a1 ty)
      | BarocqTyped.EUnaryOp op e1 ty =>
          do (li, a1) <- norm_expr_aux e1;
          sret (li, AUnaryOp op a1 ty)
      | BarocqTyped.EBinaryOp op e1 e2 ty =>
          do (li1, a1) <- norm_expr_aux e1;
          do (li2, a2) <- norm_expr_aux e2;
          sret (li1 ++ li2, ABinaryOp op a1 a2 ty)
      | BarocqTyped.EArrayGet e1 e2 ly ty =>
          do (li1, a1) <- norm_expr_aux e1;
          do (li2, a2) <- norm_expr_aux e2;
          do x <- fresh_var;
          sret (li1 ++ li2, AArrayGet a1 a2 ly ty)
      | BarocqTyped.EArraySet e1 e2 e3 ty =>
          do (li1, a1) <- norm_expr_aux e1;
          do (li2, a2) <- norm_expr_aux e2;
          do (li3, a3) <- norm_expr_aux e3;
          do x <- fresh_var;
          sret (li1 ++ li2 ++ li3 ++ [(x, EArraySet a1 a2 a3 ty)], AVar x ty)
      | BarocqTyped.ERecordProj e1 f ly ty =>
          do (li1, a1) <- norm_expr_aux e1;
          do x <- fresh_var;
          sret (li1, ARecordProj a1 f ly ty)
      | BarocqTyped.ERecordUpdate e1 f e2 ty =>
          do (li1, a1) <- norm_expr_aux e1;
          do (li2, a2) <- norm_expr_aux e2;
          do x <- fresh_var;
          sret (li1 ++ li2 ++ [(x, ERecordUpdate a1 f a2 ty)], AVar x ty)
      | BarocqTyped.EApp e1 args ty =>
          do (li1, a1) <- norm_expr_aux e1;
          do (l_args, a_args) <-
            List.fold_left
              (fun acc arg =>
                do (acc_l, acc_args) <- acc;
                do (lia, a) <- norm_expr_aux arg;
                sret (acc_l ++ lia, acc_args ++ [a]))
              args
              (sret ([], []));
          let impure_call :=
            do x <- fresh_var;
            sret (li1 ++ l_args ++ [(x, EApp a1 a_args ty)], AVar x ty)
          in
          match a1 with
          | AVar f tf =>
              if SSet.mem f pure_funs then
                sret (li1 ++ l_args, APureCall f tf a_args ty)
              else impure_call
          | _ => impure_call
          end
      | _ =>
          do x <- fresh_var;
          do be <- norm_expr_rec e;
          sret ((x, be) :: nil, AVar x (BarocqTyped.typof_expr e))
      end.

    Fixpoint norm_exprlist_rec (e: BarocqTyped.expr) (la: list atom) (le: list BarocqTyped.expr) :
      crmon ((smaplist BarocqBNF.expr) * BarocqBNF.expr) :=
      match le with
      | nil =>
          do er <- lift_err (bnfexpr_of_atomlist e (rev' la));
          sret (nil, er)
      | e1 :: le' =>
          do (lx, a1) <- norm_expr_aux e1;
          do (lr, er) <- norm_exprlist_rec e (a1 :: la) le';
          sret (lx ++ lr, er)
      end.

    Definition norm_exprlist (e: BarocqTyped.expr) (le: list BarocqTyped.expr) : crmon BarocqBNF.expr :=
      do (lx, er) <- norm_exprlist_rec e [] le;
      sret (letseq lx er (btypof_expr er)).

    Fixpoint norm_match_cases (cases: list (pattern * BarocqTyped.expr)) : crmon (list (pattern * BarocqBNF.expr)) :=
      match cases with
      | nil => sret nil
      | (c, e) :: cases' =>
          do ne <- norm_expr_rec e;
          do ncases' <- norm_match_cases cases';
          sret ((c, ne) :: ncases')
      end.

    Fixpoint norm_bindings (l : list (ident * BarocqTyped.expr)) : crmon ((smaplist BarocqBNF.expr) * list (ident *atom)) :=
      match l with
      | nil => sret (nil,nil)
      | (x,e)::l' =>
          do (l1,a1) <- norm_expr_aux e ;
          do (lr,ar) <- norm_bindings l';
          sret (l1++lr,(x,a1)::ar)
      end.


End NORMAUX.


  Fixpoint norm_expr_rec (e: BarocqTyped.expr) : crmon BarocqBNF.expr :=
    match e with
    | BarocqTyped.ETrue =>
        sret (EAtom ATrue)
    | BarocqTyped.EFalse =>
        sret (EAtom AFalse)
    | BarocqTyped.EInt32 i s =>
        sret (EAtom (AInt32 i s))
    | BarocqTyped.EInt64 i s =>
        sret (EAtom (AInt64 i s))
    | BarocqTyped.EConstr x i ty =>
        sret (EAtom (AConstr x i ty))
    | BarocqTyped.EVar x ty =>
        sret (EAtom (AVar x ty))
    | BarocqTyped.ECast e1 ty =>
        norm_exprlist norm_expr_rec e [e1]
    | BarocqTyped.EUnaryOp op e1 _ =>
        norm_exprlist norm_expr_rec e [e1]
    | BarocqTyped.EBinaryOp op e1 e2 _ =>
        norm_exprlist norm_expr_rec e [e1; e2]
    | BarocqTyped.EArrayGet e1 e2 _ _ =>
        norm_exprlist norm_expr_rec e [e1; e2]
    | BarocqTyped.EArraySet e1 e2 e3 _ =>
        norm_exprlist norm_expr_rec e [e1; e2; e3]
    | BarocqTyped.ERecordProj e1 k _ _ =>
        norm_exprlist norm_expr_rec e [e1]
    | BarocqTyped.ERecordUpdate e1 k e2 _ =>
        norm_exprlist norm_expr_rec e [e1; e2]
    | BarocqTyped.EApp e1 args _ =>
        norm_exprlist norm_expr_rec e (e1 :: args)
    | BarocqTyped.EIfThenElse e1 e2 e3 ty =>
        do (le, c) <- norm_expr_aux norm_expr_rec e1;
        do ne2 <- norm_expr_rec e2;
        do ne3 <- norm_expr_rec e3;
        sret (letseq le (EIfThenElse c ne2 ne3 ty) ty)
    | BarocqTyped.EMatch e1 cases ty =>
        do (le, a) <- norm_expr_aux norm_expr_rec e1;
        do ncases <- norm_match_cases norm_expr_rec cases;
        sret (letseq le (EMatch a ncases ty) ty)
    | BarocqTyped.ELetIn x e1 e2 ty =>
        do ne1 <- norm_expr_rec e1;
        do ne2 <- norm_expr_rec e2;
        sret (ELetIn x ne1 ne2 ty)
    | BarocqTyped.EActR l ty =>
        do (le,al) <- norm_bindings norm_expr_rec l ;
        sret (letseq le (EActR al ty) ty)
    | BarocqTyped.ELetW init cond decr body e2 ty =>
        do init' <- norm_while_init norm_expr_rec init ;
        do body' <- norm_expr_rec body;
        do e2'   <- norm_expr_rec e2;
        (** Beware: we assume that [cond] and [decr] are already atoms *)

        do cond' <- lift_err (atom_of_expr cond);
        do decr'  <- lift_err (atom_of_expr decr);
        sret (BarocqBNF.ELetW init' cond' decr' body' e2' ty)
    | BarocqTyped.EAttr s e =>
        do ne <- norm_expr_rec e;
        sret (EAttr s ne)
  end.

  Close Scope state_err_monad_scope.

  Local Open Scope error_monad_scope.

  Definition norm_expr (e: BarocqTyped.expr) : res BarocqBNF.expr :=
    do ne <- norm_expr_rec e 1%positive;
    eret (fst ne).

  Definition norm_function (f: BarocqTyped.function) : res BarocqBNF.function :=
    do body_norm <- norm_expr (fn_body f);
    eret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body_norm
    |}.

  Fixpoint norm_program_rec (prog: BarocqTyped.program) : res (BarocqBNF.program) :=
    match prog with
    | nil => eret (mk_program nil nil nil)
    | d :: prog' =>
        do b_prog <- norm_program_rec prog';
        let '(mk_program b_defs b_types b_tabs) := b_prog in
        match d with
        | BarocqTyped.DefType x td =>
            eret (mk_program b_defs ((x, td) :: b_types) b_tabs)
        | BarocqTyped.DefConst x l ty =>
            let b_defs' := Syntax.DefConst x l ty :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | BarocqTyped.DefFun x f =>
            do f' <- norm_function f;
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

Definition norm_program (prog: BarocqTyped.program) : res BarocqBNF.program :=
  norm_program_rec (BarocqTyped.pure_functions prog) prog.
