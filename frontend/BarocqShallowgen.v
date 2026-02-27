From Coq Require Import List String ZArith.
From compcert Require Import Maps.
From BarocqComp  Require Import Pp Printer.
From BarocqComp Require Import Target Monads Error Maps2 Types Utils Syntax Barray Benum Barocq BarocqShallow.
Import ListNotations.
Import MonCounterErr.

Inductive shallow_version : Type :=
  | ShallowR  (* shallow embedding with native Rocq records and enums. *)
  | ShallowB. (* shallow embedding with Barocq encoding for records and enums. *)

Module Normalization.

  Import BNF.

  Definition bnfexpr_of_atomlist (e: Barocq.expr) (la: list atom) : res BNF.expr :=
    match e with
    | Barocq.ECast _ ty =>
        let* a := list_nth_err la 0 in
        eret (EAtom (ACast a ty))
    | Barocq.EUnaryOp op _ =>
        let* a := list_nth_err la 0 in
        eret (EAtom (AUnaryOp op a))
    | Barocq.EBinaryOp op _ _ =>
        let* a1 := list_nth_err la 0 in
        let* a2 := list_nth_err la 1 in
        eret (EAtom (ABinaryOp op a1 a2))
    | Barocq.EArrayGet _ _ =>
        let* a1 := list_nth_err la 0 in
        let* a2 := list_nth_err la 1 in
        eret (EArrayGet a1 a2)
    | Barocq.EArraySet _ _ _ =>
        let* a1 := list_nth_err la 0 in
        let* a2 := list_nth_err la 1 in
        let* a3 := list_nth_err la 2 in
        eret (EArraySet a1 a2 a3)
    | Barocq.ERecordProj _ x =>
        let* a := list_nth_err la 0 in
        eret (EAtom (ARecordProj a x))
    | Barocq.ERecordUpdate _ x _ =>
        let* a1 := list_nth_err la 0 in
        let* a2 := list_nth_err la 1 in
        eret (EAtom (ARecordUpdate a1 x a2))
    | Barocq.EApp _ _ =>
        let* a := list_nth_err la 0 in
        let args := tail la in
        eret (EApp a args)
    | _ => efail
    end.

  Open Scope state_err_monad_scope.

  Definition fresh_var : crmon ident := Utils.fresh_var_err "b".

  Fixpoint norm_expr_rec (e: Barocq.expr) : crmon BNF.expr :=
    let fix norm_expr_aux (e: Barocq.expr) : crmon (smaplist BNF.expr * atom) :=
      match e with
      | Barocq.ETrue => ret (nil, ATrue)
      | Barocq.EFalse => ret (nil, AFalse)
      | Barocq.EInt32 i s => ret (nil, AInt32 i s)
      | Barocq.EInt64 i s => ret (nil, AInt64 i s)
      | Barocq.EConstr x => ret (nil, AConstr x)
      | Barocq.EVar x => ret (nil, AVar x)
      | Barocq.ECast e1 ty =>
          match ty with
          | BEnum _ =>
              let* (li1, a1) := norm_expr_aux e1 in
              let* x := fresh_var in
              ret (li1 ++ [(x, (EAtom (ACast a1 ty)))], AVar x)
          | _ =>
              let* (li1, a1) := norm_expr_aux e1 in
              ret (li1, ACast a1 ty)
          end
      | Barocq.EUnaryOp op e1 =>
          let* (li, a1) := norm_expr_aux e1 in
          ret (li, AUnaryOp op a1)
      | Barocq.EBinaryOp op e1 e2 =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (li2, a2) := norm_expr_aux e2 in
          match op with
          | BopDiv | BopMod =>
              let* x := fresh_var in
              ret (li1 ++ li2 ++ [(x, (EAtom (ABinaryOp op a1 a2)))], AVar x)
          | _ =>
            ret (li1 ++ li2, ABinaryOp op a1 a2)
          end
      | Barocq.EArrayGet e1 e2 =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (li2, a2) := norm_expr_aux e2 in
          let* x := fresh_var in
          ret (li1 ++ li2 ++ [(x, EArrayGet a1 a2)], AVar x)
      | Barocq.EArraySet e1 e2 e3 =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (li2, a2) := norm_expr_aux e2 in
          let* (li3, a3) := norm_expr_aux e3 in
          let* x := fresh_var in
          ret (li1 ++ li2 ++ li3 ++ [(x, EArraySet a1 a2 a3)], AVar x)
      | Barocq.ERecordProj e1 f =>
          let* (li1, a1) := norm_expr_aux e1 in
          ret (li1, ARecordProj a1 f)
      | Barocq.ERecordUpdate e1 f e2 =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (li2, a2) := norm_expr_aux e2 in
          ret (li1 ++ li2, ARecordUpdate a1 f a2)
      | Barocq.EApp e1 args =>
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
          let* x := fresh_var in
          ret (li1 ++ l_args ++ [(x, EApp a1 a_args)], AVar x)
      | _ =>
        let* x := fresh_var in
        let* be := norm_expr_rec e in
        ret ((x, be) :: nil, AVar x)
      end
    in
    let fix mk_norm (le: smaplist BNF.expr) (e: expr) : BNF.expr :=
      match le with
      | nil => e
      | (x, be) :: le' =>
          ELetIn x be (mk_norm le' e)
      end
    in
    let fix norm_exprlist_rec (e: Barocq.expr) (la: list atom) (le: list Barocq.expr) : crmon (smaplist BNF.expr * BNF.expr) :=
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
    let norm_exprlist (e: Barocq.expr) (le: list Barocq.expr) : crmon BNF.expr :=
      let* (lx, er) := norm_exprlist_rec e [] le in
      ret (mk_norm lx er)
    in
    let fix norm_match_cases (cases: list (pattern * Barocq.expr)) : crmon (list (pattern * BNF.expr)) :=
      match cases with
      | nil => ret nil
      | (c, e) :: cases' =>
          let* ne := norm_expr_rec e in
          let* ncases' := norm_match_cases cases' in
          ret ((c, ne) :: ncases')
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
    | Barocq.EConstr x =>
        ret (EAtom (AConstr x))
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
    | Barocq.ERecordProj e1 k =>
        norm_exprlist e [e1]
    | Barocq.ERecordUpdate e1 k e2 =>
        norm_exprlist e [e1; e2]
    | Barocq.EApp e1 args =>
        norm_exprlist e (e1 :: args)
    | Barocq.EIfThenElse e1 e2 e3 =>
        let* (le, c) := norm_expr_aux e1 in
        let* ne2 := norm_expr_rec e2 in
        let* ne3 := norm_expr_rec e3 in
        ret (mk_norm le (EIfThenElse c ne2 ne3))
    | Barocq.EMatch e1 cases =>
        let* (le, a) := norm_expr_aux e1 in
        let* ncases := norm_match_cases cases in
        ret (mk_norm le (EMatch a ncases))
    | Barocq.ELetIn x e1 e2 =>
        let* ne1 := norm_expr_rec e1 in
        let* ne2 := norm_expr_rec e2 in
        ret (ELetIn x ne1 ne2)
    | Barocq.EAttr s e =>
        let* ne := norm_expr_rec e in
        ret (EAttr s ne)
    end.

  Close Scope state_err_monad_scope.

  Definition norm_expr (e: Barocq.expr) : res BNF.expr :=
    let* ne := norm_expr_rec e 1%positive in
    eret (fst ne).

  Definition norm_function (f: Barocq.function) : res BNF.function :=
    let* body_norm := norm_expr (fn_body f) in
    eret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body_norm
    |}.

  Fixpoint norm_program (prog: Barocq.program) : res (BarocqShallow.BNF.program) :=
    match prog with
    | nil => eret (mk_program nil nil nil)
    | d :: prog' =>
        let* b_prog := norm_program prog' in
        let '(mk_program b_defs b_types b_tabs) := b_prog in
        match d with
        | Barocq.DefType x td =>
            eret (mk_program b_defs ((x, td) :: b_types) b_tabs)
        | Barocq.DefConst x l ty =>
            let b_defs' := Syntax.DefConst x l ty :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | Barocq.DefFun x f =>
            let* f' := norm_function f in
            let b_defs' := Syntax.DefFun x f' :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | Barocq.DeclType t tk =>
            eret (mk_program b_defs b_types ((t, tk) :: b_tabs))
        | Barocq.DeclConst x ty =>
            let b_defs' := Syntax.DeclConst x ty :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | Barocq.DeclFun x tparams tret =>
            let b_defs' := Syntax.DeclFun x tparams tret :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        end
    end.

End Normalization.

Module Normalization2.

  Import BNF.

  Fixpoint atom_of_expr (e: Barocq.expr) : res atom :=
    match e with
    | Barocq.ETrue => eret ATrue
    | Barocq.EFalse => eret AFalse
    | Barocq.EInt32 i s => eret (AInt32 i s)
    | Barocq.EInt64 i s => eret (AInt64 i s)
    | Barocq.EConstr c => eret (AConstr c)
    | Barocq.EVar x => eret (AVar x)
    | Barocq.ECast e1 ty =>
        match ty with
        | BEnum _ => Error (msg "cast of enum is not supported")
        | _ =>
            let* a1 := atom_of_expr e1 in
            eret (ACast a1 ty)
        end
    | Barocq.EUnaryOp op e1 =>
        let* a1 := atom_of_expr e1 in
        eret (AUnaryOp op a1)
    | Barocq.EBinaryOp op e1 e2 =>
        match op with
        | BopDiv | BopMod => Error (msg "div/mod are not supported")
        | _ =>
            let* a1 := atom_of_expr e1 in
            let* a2 := atom_of_expr e2 in
            eret (ABinaryOp op a1 a2)
        end
    | Barocq.ERecordProj e1 x =>
        let* a1 := atom_of_expr e1 in
        eret (ARecordProj a1 x)
    | Barocq.ERecordUpdate e1 x e2 =>
        let* a1 := atom_of_expr e1 in
        let* a2 := atom_of_expr e2 in
        eret (ARecordUpdate a1 x a2)
    | _ => Error (msg (Pp.pp (Pp.pp_expr e)))
    end.

  Open Scope state_err_monad_scope.

  Definition fresh_var : crmon ident := Normalization.fresh_var.

  Fixpoint norm_expr_rec (e: Barocq.expr) : crmon BNF.expr :=
    let fix norm_exprlist_rec (e: Barocq.expr) (la: list atom) (le: list Barocq.expr) : crmon BNF.expr :=
      match le with
      | nil => lift_err (Normalization.bnfexpr_of_atomlist e (rev' la))
      | e1 :: le' =>
          match atom_of_expr e1 with
          | OK a1 => norm_exprlist_rec e (a1 :: la) le'
          | Error _ =>
              let* x := fresh_var in
              let* ne1 := norm_expr_rec e1 in
              let* ner := norm_exprlist_rec e (AVar x :: la) le' in
              ret (ELetIn x ne1 ner)
          end
      end
    in
    let norm_exprlist (e: Barocq.expr) (le: list Barocq.expr) : crmon BNF.expr :=
      norm_exprlist_rec e [] le
    in
    let fix norm_match_cases (cases: list (pattern * Barocq.expr)) : crmon (list (pattern * BNF.expr)) :=
      match cases with
      | nil => ret nil
      | (c, e) :: cases' =>
          let* ne := norm_expr_rec e in
          let* ncases' := norm_match_cases cases' in
          ret ((c, ne) :: ncases')
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
    | Barocq.EConstr x =>
        ret (EAtom (AConstr x))
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
    | Barocq.ERecordProj e1 k =>
        norm_exprlist e [e1]
    | Barocq.ERecordUpdate e1 k e2 =>
        norm_exprlist e [e1; e2]
    | Barocq.EApp e1 args =>
        norm_exprlist e (e1 :: args)
    | Barocq.EIfThenElse e1 e2 e3 =>
        let* ne2 := norm_expr_rec e2 in
        let* ne3 := norm_expr_rec e3 in
        match atom_of_expr e1 with
        | OK a1 => ret (EIfThenElse a1 ne2 ne3)
        | Error _ =>
            let* x1 := fresh_var in
            let* ne1 := norm_expr_rec e1 in
            ret (ELetIn x1 ne1 (EIfThenElse (AVar x1) ne2 ne3))
        end
    | Barocq.EMatch e1 cases =>
        let* ncases := norm_match_cases cases in
        match atom_of_expr e1 with
        | OK a1 => ret (EMatch a1 ncases)
        | Error _ =>
            let* x1 := fresh_var in
            let* ne1 := norm_expr_rec e1 in
            ret (ELetIn x1 ne1 (EMatch (AVar x1) ncases))
        end
    | Barocq.ELetIn x e1 e2 =>
        let* ne1 := norm_expr_rec e1 in
        let* ne2 := norm_expr_rec e2 in
        ret (ELetIn x ne1 ne2)
    | Barocq.EAttr s e =>
        let* ne := norm_expr_rec e in
        ret (EAttr s ne)
    end.

  Close Scope state_err_monad_scope.

  Definition norm_expr (e: Barocq.expr) : res BNF.expr :=
    let* ne := norm_expr_rec e 1%positive in
    eret (fst ne).

  Definition norm_function (f: Barocq.function) : res BNF.function :=
    let* body_norm := norm_expr (fn_body f) in
    eret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body_norm
    |}.

  Fixpoint norm_program (prog: Barocq.program) : res (BarocqShallow.BNF.program) :=
    match prog with
    | nil => eret (mk_program nil nil nil)
    | d :: prog' =>
        let* b_prog := norm_program prog' in
        let '(mk_program b_defs b_types b_tabs) := b_prog in
        match d with
        | Barocq.DefType x td =>
            eret (mk_program b_defs ((x, td) :: b_types) b_tabs)
        | Barocq.DefConst x l ty =>
            let b_defs' := Syntax.DefConst x l ty :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | Barocq.DefFun x f =>
            let* f' := norm_function f in
            let b_defs' := Syntax.DefFun x f' :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | Barocq.DeclType t tk =>
            eret (mk_program b_defs b_types ((t, tk) :: b_tabs))
        | Barocq.DeclConst x ty =>
            let b_defs' := Syntax.DeclConst x ty :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        | Barocq.DeclFun x tparams tret =>
            let b_defs' := Syntax.DeclFun x tparams tret :: b_defs in
            eret (mk_program b_defs' b_types b_tabs)
        end
    end.

End Normalization2.

Module Monadification.

  Import Monadic.

  Section MON.

  Variable arch : Target.archi.

  Variable shver : shallow_version.

  Definition arr_index_mtyp : mtyp :=
    match arch with
    | Ptr32 => MInt32 Unsigned
    | Ptr64 => MInt64 Unsigned
    end.

  Definition typof_literal (l: literal) : mtyp :=
    match l with
    | LTrue
    | LFalse => MBool
    | LInt32 _ s => MInt32 s
    | LInt64 _ s => MInt64 s
    | LArray _ ta => MArray ta
    | LRecord _ rid => MRecord rid
    end.

  Definition typof_atom (a: atom) : mtyp :=
    match a with
    | ATrue
    | AFalse => MBool
    | AInt32 _ s => MInt32 s
    | AInt64 _ s => MInt64 s
    | AConstr _ ty
    | AVar _ ty
    | ACast _ _ ty
    | AUnaryOp _ _ ty
    | ABinaryOp _ _ _ ty
    | ARecordProj  _ _ ty
    | ARecordUpdate _ _ _ ty
    | ALambda _ _ ty
    | ALambdaRet _ _ ty
    | AApp _ _ ty => ty
    end.

  Definition typof_expr (e: expr) : mtyp :=
    match e with
    | EAtom _ ty
    | EArrayGet _ _ ty
    | EArraySet _ _ _ ty
    | EApp _ _ ty
    | EIfThenElse _ _ _ ty
    | EMatch _ _ ty
    | ELetIn _ _ _ ty
    | ELetMon _ _ _ ty
    | ERet _ ty => ty
    | EAttr _ _ ty => ty
    end.

  Fixpoint mtyp_eq_dec (t1 t2: mtyp) : { t1 = t2 } + { t1 <> t2 }.
  Proof.
    decide equality.
    - apply signedness_eq_dec.
    - apply signedness_eq_dec.
    - apply Ident.eq_dec.
    - apply Ident.eq_dec.
    - apply list_eq_dec. apply mtyp_eq_dec.
    - apply Ident.eq_dec.
  Defined.

  Fixpoint pp_mtyp (bt: mtyp) :=
  match bt with
  | MBool => Bstr "bool"
  | MInt32 s => if s then Bstr "i32" else Bstr "u32"
  | MInt64 s => if s then Bstr "i64" else Bstr "u64"
  | MArray bt => Pp.seq (Bstr "[" :: pp_mtyp bt :: Bstr "]" :: nil)
  | MEnum id => Bcat (Bstr "enum ") (Bstr id)
  | MRecord id  => Bcat (Bstr "record ") (Bstr id)
  | MFun args r  => Bcat (pp_list (Bstr " -> ") pp_mtyp args) (pp_mtyp r)
  | MAbs id      => Bcat (Bstr "abs ") (Bstr id)
  | MRes bt      => Bcat (Bstr "res ") (pp_mtyp bt)
  end.

  Definition menv := Typing.TEnv.t mtyp.

  Definition gcontext : Type := STree.t mtyp.

  Definition lcontext : Type := STree.t mtyp.

  Definition gcontext_get (gx: gcontext) (x: ident) : res mtyp :=
    match STree.get x gx with
    | Some t => eret t
    | None => efail
    end.

  Definition gcontext_update (be: menv) (gx: gcontext) (x: ident) (ty: mtyp) : res gcontext :=
    match gcontext_get gx x with
    | OK _ => efail
    | Error _ => eret (STree.set x ty gx)
    end.

  Definition lcontext_get (lx: lcontext) (x: ident) : res mtyp :=
    match STree.get x lx with
    | Some t => eret t
    | None => efail
    end.

  Definition lcontext_update (lx: lcontext) (x: ident) (ty: mtyp) : lcontext :=
    STree.set x ty lx. (* overwrite *)
                   (*
        if mtyp_eq_dec ty t then eret (STree.set x ty lx)
        else
          Error (MSG "lcontext_update: types do not match. Variable "
                     ::
                     MSG x :: MSG " has type ":: MSG (Pp.pp (pp_mtyp t)) :: MSG " instead of " :: MSG (Pp.pp (pp_mtyp ty)) :: nil) *)

  Open Scope state_err_monad_scope.

  Definition fresh_var : crmon ident := Utils.fresh_var_err "b".

  Fixpoint make_lambda_args (n: nat) : crmon (list ident) :=
    match n with
    | 0 => ret nil
    | S n' =>
        let* x := fresh_var in
        let* r := make_lambda_args n' in
        ret (x :: r)
    end.
  
  Definition mtyp_list_eq_dec :
    forall (lx ly : list mtyp), {lx = ly} + {lx <> ly}.
  Proof.
    apply list_eq_dec. apply mtyp_eq_dec.
  Defined.

  Fixpoint eta_expand_rec (f: ident) (ty1: mtyp) (ty2: mtyp) (l: list ident) : crmon atom :=
    match ty1, ty2 with
    | MBool, MBool
    | MInt32 _, MInt32 _
    | MInt64 _, MInt64 _ => ret (AApp f l ty2)
    | MArray ta1, MArray ta2 =>
        if mtyp_eq_dec ta1 ta2 then ret (AApp f l ty2)
        else fail
    | MEnum e1, MEnum e2 =>
        if Ident.eq_dec e1 e2 then ret (AApp f l ty2)
        else fail
    | MRecord r1, MRecord r2 =>
        if Ident.eq_dec r1 r2 then ret (AApp f l ty2)
        else fail
    | MAbs t1, MAbs t2 =>
        if Ident.eq_dec t1 t2 then ret (AApp f l ty1)
        else fail
    | MFun t1 tr1, MFun t2 tr2 =>
        if mtyp_list_eq_dec t1 t2 then
          if mtyp_eq_dec tr1 tr2 then
            ret (AApp f l ty2)
          else
            match tr2 with
            | MRes tr2' =>
                let* args := make_lambda_args (List.length t1) in
                let* a := eta_expand_rec f tr1 tr2' (l ++ args) in
                ret (ALambdaRet args a ty2)
            | _ =>
              let* args := make_lambda_args (List.length t1) in
              let* a := eta_expand_rec f tr1 tr2 (l ++ args) in
              ret (ALambda args a ty2)
            end
        else fail
    | _, _ => fail
    end.
  
  Close Scope state_err_monad_scope.

  Definition eta_expand (f: ident) (ty1: mtyp) (ty2: mtyp) : res atom :=
    match eta_expand_rec f ty1 ty2 nil 1%positive with
    | OK (a, _) => OK a
    | Error e => Error (MSG "eta_expand" :: e)
    end.

  Definition typof_constr (me: menv) (c: ident) : res mtyp :=
    match Typing.TEnv.get_constr_typ me c with
    | Some eid => eret (MEnum eid)
    | None => efail
    end.
    
  Definition typof_var (gx: gcontext) (lx: lcontext) (x: ident) : res mtyp :=
    match lcontext_get lx x with
    | OK ty => eret ty
    | Error _ =>
        match gcontext_get gx x with
        | OK (MArray _)
        | OK (MRecord _)
        | OK (MAbs _)
        | OK (MEnum _) => efail
        | OK ty => eret ty
        | Error _ => efail
        end
    end.

  Definition typecheck_cast (from: mtyp) (to: mtyp) : res mtyp :=
    match from with
    | MBool | MInt32 _ | MInt64 _ =>
        match to with
        | MBool | MInt32 _ | MInt64 _ => eret to
        | MEnum _ => eret (MRes to)
        | _ => efail
        end
    | MEnum _ =>
        match to with
        | MBool | MInt32 _ | MInt64 _ => eret to
        | _ => efail
        end
    | _ => efail
    end.

  Definition typecheck_unary_op (op: unary_op) (ty: mtyp) : res mtyp :=
    match op, ty with
    | UopNotbool, MBool
    | UopNotint, MInt32 _
    | UopNotint, MInt64 _
    | UopNeg, MInt32 _
    | UopNeg, MInt64 _ => eret ty
    | _, _ => efail
    end.

  Definition typecheck_binary_op (op: binary_op) (ty1 ty2: mtyp) : res mtyp :=
    match op with
    | BopAndbool
    | BopOrbool
    | BopXorbool =>
        match ty1, ty2 with
        | MBool, MBool => eret ty1
        | _, _ => efail
        end
    | BopEq
    | BopNeq =>
        match ty1, ty2 with
        | MBool, MBool => eret ty1
        | MInt32 s1, MInt32 s2
        | MInt64 s1, MInt64 s2 =>
            if signedness_eq_dec s1 s2 then eret MBool
            else efail
        | MEnum t1, MEnum t2 =>
          if Ident.eq_dec t1 t2 then eret MBool
          else efail
        | _, _ => efail
        end
    | BopLt
    | BopLe 
    | BopGt
    | BopGe =>
        match ty1, ty2 with
        | MInt32 s1, MInt32 s2
        | MInt64 s1, MInt64 s2 =>
            if signedness_eq_dec s1 s2 then eret MBool
            else efail
        | _, _ => efail
        end
    | _ =>
        match ty1, ty2 with
        | MInt32 s1, MInt32 s2
        | MInt64 s1, MInt64 s2 =>
            if signedness_eq_dec s1 s2 then
              match op with
              | BopDiv | BopMod => eret (MRes ty1)
              | _ => eret ty1
              end
            else efail
        | _, _ => efail
        end
    end.

  Definition typecheck_array_get (ty1 ty2: mtyp) : res mtyp :=
    match ty1 with
    | MArray ta => 
        if mtyp_eq_dec ty2 arr_index_mtyp then
          eret (MRes ta)
        else Error (msg "typecheck_array_get")
    | _ => Error (msg "typecheck_array_get")
    end.

  Definition typecheck_atom_against (a: atom) (ty: mtyp) : res atom :=
    match a with
    | AVar x ((MFun _ _) as tx) => eta_expand x tx ty
    | _ =>
        if mtyp_eq_dec (typof_atom a) ty then eret a
        else Error (msg "typecheck_atom_against")
    end.

  Definition typecheck_array_set (ty1 ty2: mtyp) (a3: atom) : res (atom * mtyp) :=
    let tr := MRes ty1 in
    match ty1 with
    | MArray ta =>
        if mtyp_eq_dec ty2 arr_index_mtyp then
          let* a3' := typecheck_atom_against a3 ta in
          eret (a3', tr)
        else Error (msg "typecheck_array_set")
    | _ => Error (msg "typecheck_array_set")
    end.

  Definition mtypof_field (k: ident) (fields: smaplist mtyp) : res mtyp :=
    MapList.find_err Ident.eq_dec k fields.

  Definition typecheck_record_proj (me: menv) (ty: mtyp) (x: ident) : res mtyp :=
    match ty with
    | MRecord t =>
        let* fields := err_of_opt (Typing.TEnv.get_rdef me t) in
        mtypof_field x fields
    | _ => Error (msg "typecheck_record_proj")
    end.

  Definition typecheck_record_update (me: menv) (ty1: mtyp) (a2: atom) (x: ident) : res (atom * mtyp) :=
    match ty1 with
    | MRecord t =>
        let* fields := err_of_opt (Typing.TEnv.get_rdef me t) in
        let* tx := mtypof_field x fields in
        let* a2' := typecheck_atom_against a2 tx in
        eret (a2', ty1)
    | _ => Error (msg "typecheck_record_update")
    end.

  Definition zval_of_constr (me: menv) (tc: mtyp) (constr: ident) : res Z :=
    match tc with
    | MEnum eid =>
        let* elems := err_of_opt (Typing.TEnv.get_edef me eid) in
        Typing.zval_of_constr_rec elems Z0 constr
    | _ => efail
    end.

  Definition typecheck_pattern (me: menv) (te: mtyp) (elems: list ident) (p: pattern) (unmatched: list ident) : res (list ident) :=
    if list_is_empty unmatched then efail
    else
      match p with
      | PWildcard => eret nil
      | PIdent i z =>
          let* tp := typof_constr me i in
          if mtyp_eq_dec te tp then
            if List.in_dec Ident.eq_dec i elems then
              if List.in_dec Ident.eq_dec i unmatched then
                let* z2 := zval_of_constr me te i in
                if Z.eq_dec z z2 then eret (List.remove Ident.eq_dec i unmatched)
                else efail
              else efail
            else efail     
          else efail
    end.

  Fixpoint typecheck_match_rec (me: menv) (te: mtyp) (elems: list ident) (unmatched: list ident) (cases: list (pattern * mtyp)) : res mtyp :=
    match cases with
    | nil => efail
    | (x, tx) :: nil =>
        let* unmatched' := typecheck_pattern me te elems x unmatched in
        if list_is_empty unmatched' then eret tx
        else efail
    | (x, tx) :: ((_ :: _) as cases') =>
        let* unmatched' := typecheck_pattern me te elems x unmatched in
        let* tr := typecheck_match_rec me te elems unmatched' cases' in
        if mtyp_eq_dec tx tr then eret tr
        else
          match tx, tr with
          | MRes tx', _ =>
              if mtyp_eq_dec tx' tr then eret tx
              else efail
          | _, MRes tr' =>
              if mtyp_eq_dec tx tr' then eret tr
              else efail
          | _, _ => efail
          end
    end.

  Definition typecheck_match (me: menv) (ty: mtyp) (cases: list (pattern * mtyp)) : res mtyp :=
    match ty with
    | MEnum te =>
        let* elems := err_of_opt (Typing.TEnv.get_edef me te) in
        typecheck_match_rec me ty elems elems cases
    | _ => efail
    end.

  Fixpoint monadify_btyp (ty: btyp) : mtyp :=
    match ty with
    | BBool => MBool
    | BInt32 s => MInt32 s
    | BInt64 s => MInt64 s
    | BArray ta _ => MArray (monadify_btyp ta)
    | BEnum el => MEnum el
    | BRecord s _ => MRecord s
    | BFun tparams tret =>
        MFun (map monadify_btyp tparams) (MRes (monadify_btyp tret))
    | BAbs t => MAbs t
    end.

  Definition record_id (ty: mtyp) : res ident :=
    match ty with
    | MRecord rid => eret rid
    | _ => efail
    end.

  Fixpoint typecheck_atom (me : menv) (gx: gcontext) (lx: lcontext) (a: BNF.atom) : res atom :=
    match a with
    | BNF.ATrue => eret ATrue
    | BNF.AFalse => eret AFalse
    | BNF.AInt32 i s => eret (AInt32 i s)
    | BNF.AInt64 i s => eret (AInt64 i s)
    | BNF.AConstr x =>
        let* t := typof_constr me x in
        eret (AConstr x t)
    | BNF.AVar x =>
        let* t := typof_var gx lx x in
        eret (AVar x t)
    | BNF.ACast a1 ty =>
        let* a1' := typecheck_atom me gx lx a1 in
        let ty := monadify_btyp ty in
        let* t := typecheck_cast (typof_atom a1') ty in
        eret (ACast a1' ty t)
    | BNF.AUnaryOp op a1 =>
        let* a1' := typecheck_atom me gx lx a1 in
        let ty1 := typof_atom a1' in
        let* t := typecheck_unary_op op ty1 in
        eret (AUnaryOp op a1' t)
    | BNF.ABinaryOp op a1 a2 =>
        let* a1' := typecheck_atom me gx lx a1 in
        let* a2' := typecheck_atom me gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* t := typecheck_binary_op op ty1 ty2 in
        eret (ABinaryOp op a1' a2' t)
    | BNF.ARecordProj a1 x =>
        let* a1' := typecheck_atom me gx lx a1 in
        let ty1 := typof_atom a1' in
        let* t := typecheck_record_proj me ty1 x in
        eret (ARecordProj a1' x t)
    | BNF.ARecordUpdate a1 x a2 =>
        let* a1' := typecheck_atom me gx lx a1 in
        let* a2' := typecheck_atom me gx lx a2 in
        let ty1 := typof_atom a1' in
        let* (a2', t) := typecheck_record_update me ty1 a2' x in
        eret (ARecordUpdate a1' x a2' t)
    end.

  Definition typecheck_atom_err (me : menv) (gx: gcontext) (lx: lcontext) (a: BNF.atom) : res atom :=
    match typecheck_atom me gx lx a with
    | Error e => Error (MSG "typecheck_atom_err" :: e)
    | OK a => OK a
    end.

  Fixpoint typecheck_call_rec (tparams: list mtyp) (args: list atom) (tret: mtyp) : res (list atom * mtyp) :=
    match tparams, args with
    | nil, nil => eret (nil, tret)
    | tp1 :: tparams', a1 :: args' =>
        let ta1 := typof_atom a1 in
        let* (args1, t) := typecheck_call_rec tparams' args' tret in
        let* a1' := typecheck_atom_against a1 tp1 in
        eret (a1' :: args1, t)
    | _, _ => Error (msg "typecheck_call_rec")
    end.

  Definition typecheck_call (ty1: mtyp) (args: list atom) : res (list atom * mtyp) :=
    match ty1 with
    | MFun tparams tret => typecheck_call_rec tparams args tret
    | _ => Error (msg "typecheck_call")
    end.

  Fixpoint wrap_mtyp (ty: mtyp) : mtyp :=
    match ty with
    | MBool
    | MInt32 _
    | MInt64 _
    | MArray _
    | MRecord _ 
    | MEnum _
    | MAbs _ => MRes ty
    | MFun tparams tret =>
        MRes (MFun tparams (wrap_mtyp tret))
    | MRes _ => ty
    end.

  Definition unwrap_mtyp (ty: mtyp) : mtyp :=
    match ty with
    | MRes t => t
    | _ => ty
    end.

  Definition wrap_atom (a: atom) : res expr :=
    let ty := typof_atom a in
    let ty' := wrap_mtyp ty in
    let* a' :=
      match a with
      | ATrue
      | AFalse
      | AInt32 _ _
      | AInt64 _ _
      | AConstr _ _
      | ACast _ _ _
      | AUnaryOp _ _ _
      | ABinaryOp _ _ _ _
      | ARecordProj _ _ _
      | ARecordUpdate _ _ _ _ => eret a
      | AVar x _ =>
          match ty with
          | MFun _ _ => eta_expand x ty (unwrap_mtyp ty')
          | _ => eret a
          end
      | _ => Error (MSG "wrap_atom:" :: MSG (Pp.pp (Monadic.pp_atom a)) :: nil)
      end
    in eret (ERet (EAtom a' (typof_atom a')) ty').


  Fixpoint monadify_expr_rec (me: menv) (gx: gcontext) (lx: lcontext) (e: BNF.expr) (mflag: bool) : res expr :=
    match e with
    | BNF.EAtom a =>
        let* a' := typecheck_atom_err me gx lx a in
        let ta' := typof_atom a' in
        if mflag then
          match ta' with
          | MRes _ => eret (EAtom a' ta')
          | _ => wrap_atom a'
          end
        else eret (EAtom a' (typof_atom a'))
    | BNF.EArrayGet a1 a2 =>
        let* a1' := typecheck_atom_err me gx lx a1 in
        let* a2' := typecheck_atom_err me gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* t := typecheck_array_get ty1 ty2 in
        eret (EArrayGet a1' a2' t)
    | BNF.EArraySet a1 a2 a3 =>
        let* a1' := typecheck_atom_err me gx lx a1 in
        let* a2' := typecheck_atom_err me gx lx a2 in
        let* a3' := typecheck_atom_err me gx lx a3 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let ty3 := typof_atom a3' in
        let* (a3', t) := typecheck_array_set ty1 ty2 a3' in
        eret (EArraySet a1' a2' a3' t)
    | BNF.EApp a1 args =>
        let* a1' := typecheck_atom_err me gx lx a1 in
        let ty1 := typof_atom a1' in
        let* args' := mmap (typecheck_atom_err me gx lx) args in
        let* (args1, t) := typecheck_call ty1 args' in
        let e' := EApp a1' args1 t in
        if mflag then
          match t with
          | MRes _ => eret e'
          | _ => eret (ERet e' (MRes t))
          end
        else eret e'
    | BNF.EIfThenElse a e1 e2 =>
        let* a' := typecheck_atom_err me gx lx a in
        (* For ShallowB, we want to be as close as possible to the Barocq semantics, so we monadify the two branches. *)
        let mflag :=
          match shver with
          | ShallowR => mflag
          | ShallowB => true
          end
        in
        match (typof_atom a') with
        | MBool =>
            let* e1' := monadify_expr_rec me gx lx e1 mflag in
            let* e2' := monadify_expr_rec me gx lx e2 mflag in
            let ty1 := typof_expr e1' in
            let ty2 := typof_expr e2' in
            if mtyp_eq_dec ty1 ty2 then
              eret (EIfThenElse a' e1' e2' ty1)
            else
              (* It is possible that one branch contains monadic operations and not the other one. *)
              (* In this case, we have to re-monadify the pure branch by setting the imperative 
                 flag to true. *)
              match ty1, ty2 with
              | MRes ty1', _ =>
                  if mtyp_eq_dec ty1' ty2 then
                    let* e2' := monadify_expr_rec me gx lx e2 true in
                    eret (EIfThenElse a' e1' e2' ty1)
                  else Error (msg "ifthenelse")
              | _, MRes ty2' =>
                  if mtyp_eq_dec ty1 ty2' then
                    let* e1' := monadify_expr_rec me gx lx e1 true in
                    eret (EIfThenElse a' e1' e2' ty2)
                  else Error (msg "ifthenelse")
              | _, _ => Error (msg "ifthenelse")

              end
        | _ => Error (msg "Typing error: bool is expected")
        end
    | BNF.EMatch a cases =>
        let* a' := typecheck_atom_err me gx lx a in
        (* For ShallowB, we want to be as close as possible to the Barocq semantics, so we monadify all branches. *)
        let mflag :=
          match shver with
          | ShallowR => mflag
          | ShallowB => true
          end
        in
        let* ncases :=
          MapList.map_err
            (fun ec =>
              let* nep := monadify_expr_rec me gx lx ec mflag in
              eret ((nep, typof_expr nep)))
            cases
        in
        let cases_mtyp := MapList.map (fun '(_, tp) => tp) ncases in
        let* t := typecheck_match me (typof_atom a') cases_mtyp in
        (* If the result type is MRes, we re-monadify all pure branches,
           like for if-then-else expressions *)
        let* ncases :=
          match mflag with
          | false =>
              match t with
              | MRes _ =>
                  MapList.map_err
                    (fun ep => monadify_expr_rec me gx lx ep true)
                    cases
              | _ =>
                  eret (MapList.map fst ncases)
              end
          | true =>
              eret (MapList.map fst ncases)
          end
        in
        eret (EMatch a' ncases t)
    | BNF.ELetIn x e1 e2 =>
        let* e1' := monadify_expr_rec me gx lx e1 false in
        let t := typof_expr e1' in
        match t with
        | MRes tr =>
            let lx' := lcontext_update lx x tr in
            let* e2' := monadify_expr_rec me gx lx' e2 true in
            eret (ELetMon x e1' e2' (typof_expr e2'))
        | _ =>
            let lx' := lcontext_update lx x t in
            let* e2' := monadify_expr_rec me gx lx' e2 (mflag || false) in
            eret (ELetIn x e1' e2' (typof_expr e2'))
        end
    | BNF.EAttr s e =>
        let* e' := monadify_expr_rec me gx lx e false in
        let  t:= typof_expr e' in
        eret (EAttr s e' t)
    end.

  Definition monadify_expr (me: menv) (gx: gcontext) (lx: lcontext) (e: BNF.expr) : res expr :=
    let mflag :=
      match shver with
      | ShallowR => false
      | ShallowB => true
      end
    in
    monadify_expr_rec me gx lx e mflag.

  Definition monadify_function (me: menv) (gx: gcontext) (f: BNF.function) : res function :=
    let params := MapList.map monadify_btyp (Syntax.fn_params f) in
    let lx :=
      List.fold_left
        (fun acc '(x, tx) => lcontext_update acc x tx)
        params
        (STree.empty)
    in
    let* body := monadify_expr me gx lx (Syntax.fn_body f) in
    let tret := typof_expr body in
    let f := {|
      fn_return := typof_expr body;
      fn_params := params;
      fn_body := body
    |} in
    match shver with
    | ShallowR => eret f
    | ShallowB =>
        match tret with
        | MRes _ => eret f
        | _ => Error (msg "Should be monadic!")
        end
    end.

  Fixpoint make_absfun_tparams (tparams1: list (param_attr * btyp)) (tparams2 : list mtyp) : res (list (param_attr * mtyp)) :=
    match tparams1, tparams2 with
    | nil, nil => eret nil
    | (attr1, t1) :: tparams1', t2 :: tparams2' =>
        let* r := make_absfun_tparams tparams1' tparams2' in
        eret ((attr1, t2) :: r)
    | _, _ => Error (msg "make_absfun_tparams")
    end.

  Fixpoint typecheck_array_lit (a: array literal) : res mtyp :=
    match a with
    | nil => efail
    | l :: nil => eret (typof_literal l)
    | l :: a' =>
        let* t := typecheck_array_lit a' in
        if mtyp_eq_dec (typof_literal l) t then eret t
        else Error (msg "typecheck_array_lit")
    end.

  Fixpoint typecheck_struct_lit (l1: smaplist literal) (l2: smaplist mtyp) : bool :=
    match l1, l2 with
    | nil, nil => true
    | (x1, l1) :: l1', (x2, tx2) :: l2' =>
        let tx1 := typof_literal l1 in
        if mtyp_eq_dec tx1 tx2 then typecheck_struct_lit l1' l2'
        else false
    | _, _ => false
    end.

  Fixpoint typecheck_literal (me: menv) (l: BNF.literal) : res literal :=
    match l with
    | Syntax.LTrue => eret LTrue
    | Syntax.LFalse => eret LFalse
    | Syntax.LInt32 i s => eret (LInt32 i s)
    | Syntax.LInt64 i s => eret (LInt64 i s)
    | Syntax.LArray a ta _ =>
        let* a' := mmap (typecheck_literal me) a in
        let* t := typecheck_array_lit a' in
        let ta := monadify_btyp ta in
        if mtyp_eq_dec t ta then eret (LArray a' t)
        else efail
    | Syntax.LRecord rc _ rid =>
        let* rc' := MapList.map_err (typecheck_literal me) rc in
        let* t := err_of_opt (Typing.TEnv.get_rdef me rid) in
        if typecheck_struct_lit rc' t then
          eret (LRecord rc' rid)
        else efail
    end. 


  Fixpoint monadify_globdefs_rec (me: menv) (gx: gcontext) (defs: list BNF.globdef) : res (list globdef) :=
    match defs with
    | nil => eret nil
    | d :: defs' =>
        match d with
        | Syntax.DefConst x l ty =>
            let ty' := monadify_btyp ty in
            let* l' := typecheck_literal me l in
            if mtyp_eq_dec (typof_literal l') ty' then
              let* gx' := gcontext_update me gx x ty' in
              let* r := monadify_globdefs_rec me gx' defs' in
              eret (Syntax.DefConst x l' ty' :: r)
            else efail
        | Syntax.DefFun x f =>
            match monadify_function me gx f with
            | Error e => Error (MSG "Cannot monadify " :: MSG x :: e)
            | OK f'   =>
                let tf := MFun (map snd (fn_params f')) (fn_return f') in
                let* gx' := gcontext_update me gx x tf in
                let* r := monadify_globdefs_rec me gx' defs' in
                eret (Syntax.DefFun x f' :: r)
            end
        | Syntax.DeclConst x ty =>
            let ty' := monadify_btyp ty in
            let* gx' := gcontext_update me gx x ty' in
            let* r := monadify_globdefs_rec me gx' defs' in
            eret (Syntax.DeclConst x ty' :: r)
        | Syntax.DeclFun f tparams tret =>
            let ty'  := monadify_btyp (mk_fun_btyp tparams tret) in
            let* gx' := gcontext_update me gx f ty' in
            let* r := monadify_globdefs_rec me gx' defs' in
            match ty' with
            | MFun tparams' tret' =>
                let* tparams' := make_absfun_tparams tparams tparams' in
                eret (Syntax.DeclFun f tparams' tret' :: r)
            | _ => Error (MSG "DeclFun " :: MSG "wrong typing"::nil)
            end
        end
    end.

  Definition monadify_globdefs (me: menv) (defs: list BNF.globdef) : res (list globdef) :=
    monadify_globdefs_rec me STree.empty defs.

  Definition monadify_type_defs (types: smaplist (type_def field_descr)) : smaplist (type_def (mtyp * layout)) :=
    MapList.map
      (fun td =>
        match td with
        | TdEnum elems => TdEnum elems
        | TdRecord fields =>
            let fields' := MapList.map (fun '(bt, ly) => (monadify_btyp bt, ly)) fields in
            TdRecord fields'
        end)
      types.

  Definition monadify_program (prog: BNF.program) : res program :=
    let types := monadify_type_defs (prog_types prog) in
    let* me :=
      let types :=
        MapList.map
          (fun td =>
            match td with
            | TdEnum elems => TdEnum elems
            | TdRecord fields => TdRecord (MapList.map fst fields)
            end)
          types
      in
      err_of_opt (Typing.TEnv.build types)
    in
    let* defs := monadify_globdefs me (prog_defs prog) in
    eret {|
      prog_defs := defs;
      prog_types := types;
      prog_tabs := (prog_tabs prog);
    |}.

  End MON.

End Monadification.

Open Scope error_monad_scope.

Definition monadify_norm_program (arch: Target.archi) (shver: shallow_version) (prog: Barocq.program) : res Monadic.program :=
  let/c bnf := Normalization.norm_program prog /> "unable to normalize the program" in
  let/c mon := Monadification.monadify_program arch shver bnf /> "unable to monadify the program" in
  eret mon.

Definition monadify_norm2_program (arch: Target.archi) (shver: shallow_version) (prog: Barocq.program) : res Monadic.program :=
  match Normalization2.norm_program prog   with
  | Error e => Error (MSG "Unable to normalize the program (v2):" ::MSG "Error " :: e)
  | OK bnf  => match Monadification.monadify_program arch shver bnf with
               | Error e => Error (MSG "unable to monadify the program (v2):" :: MSG "Error " :: e)
               | OK mon  => OK mon
               end
  end.
