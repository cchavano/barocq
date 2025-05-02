From Coq Require Import List String.
From compcert Require Import Maps.
From BarocqComp Require Import Monads Error MapList Types Utils Syntax Barocq BarocqTransf BarocqShallow.
Import ListNotations.
Import MonCounterErr.

Module Normalization.

  Import BNF.

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
    | Barocq.EStructProj e1 x =>
        let* a1 := atom_of_expr e1 in
        eret (AStructProj a1 x)
    | Barocq.EStructUpdate e1 x e2 =>
        let* a1 := atom_of_expr e1 in
        let* a2 := atom_of_expr e2 in
        eret (AStructUpdate a1 x a2)
    | _ => MonError.fail
    end.

  Definition spread_atomlist (e: Barocq.expr) (la: list atom) : res BNF.expr :=
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
        eret (EAtom (AStructProj a x))
    | Barocq.EStructUpdate _ x _ =>
        let* a1 := nth_err la 0 in
        let* a2 := nth_err la 1 in
        eret (EAtom (AStructUpdate a1 x a2))
    | Barocq.EApp _ _ =>
        let* a := nth_err la 0 in
        let args := tail la in
        eret (EApp a args)
    | _ => MonError.fail
    end.

  Open Scope state_err_monad_scope.

  Definition fresh_var : crmon ident := Utils.fresh_var_err "b".

  Fixpoint norm_expr_rec (e: Barocq.expr) : crmon BNF.expr :=
    let fix norm_exprlist_rec (e: Barocq.expr) (le: list Barocq.expr) (la: list atom) : crmon BNF.expr :=
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
    let norm_exprlist (e: Barocq.expr) (le: list Barocq.expr) : crmon BNF.expr :=
      norm_exprlist_rec e le nil
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
    | Barocq.EDeepAccess _ _ => fail
    | Barocq.EApp e1 args =>
        norm_exprlist e (e1 :: args)
    | Barocq.EIfThenElse e1 e2 e3 =>
        let* ne2 := norm_expr_rec e2 in
        let* ne3 := norm_expr_rec e3 in
        match atom_of_expr e1 with
        | OK a => ret (EIfThenElse a ne2 ne3)
        | Error _ =>
            let* x1 := fresh_var in
            let* ne1 := norm_expr_rec e1 in
            ret (ELetIn x1 ne1 (EIfThenElse (AVar x1) ne2 ne3))
        end
    | Barocq.ELetIn x e1 e2 =>
        let* ne1 := norm_expr_rec e1 in
        let* ne2 := norm_expr_rec e2 in
        ret (ELetIn x ne1 ne2)
    end.

  Close Scope state_err_monad_scope.

  Definition norm_expr (e: Barocq.expr) : res BNF.expr :=
    let* ne := norm_expr_rec e 0 in
    eret (fst ne).

  Definition norm_function (f: Barocq.function) : res BNF.function :=
    let* body_norm := norm_expr (fn_body f) in
    eret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body_norm
    |}.

  Fixpoint norm_program_rec (defs: list Barocq.globdef) : res (list BarocqShallow.BNF.globdef * list struct_def) :=
    match defs with
    | nil => eret (nil, nil)
    | d :: defs' =>
        match d with
        | Barocq.DefStruct a fields =>
            let* (defr, structs) := norm_program_rec defs' in
            eret (defr, {| sd_name := a; sd_fields := fields |} :: structs)
        | Barocq.DefConst x l ty =>
            let* (defr, structs) := norm_program_rec defs' in
            eret (Syntax.DefConst x l ty :: defr, structs)
        | Barocq.DefFun x f =>
            let* f' := norm_function f in
            let* (defr, structs):= norm_program_rec defs' in
            eret (Syntax.DefFun x f' :: defr, structs)
        end
    end.
    
  Definition norm_program (prog: Barocq.program) : res BNF.program :=
    let* (defs, structs) := norm_program_rec prog in
    eret {|
      prog_defs := defs;
      prog_types := structs
    |}.

End Normalization.

Module Monadification.

  Import Monadic.

  Definition typof_atom (a: atom) : mtyp :=
    match a with
    | ATrue ty
    | AFalse ty
    | AInt32 _ ty
    | AInt64 _ ty
    | AVar _ ty
    | ACast _ ty
    | AUnaryOp _ _ ty
    | ABinaryOp _ _ _ ty
    | AStructProj  _ _ ty
    | AStructUpdate _ _ _ ty
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
    | ELetIn _ _ _ ty
    | ELetMon _ _ _ ty
    | ERet _ ty => ty
    end.

  Fixpoint mtyp_eq_dec (t1 t2: mtyp) : { t1 = t2 } + { t1 <> t2 }.
  Proof.
    repeat decide equality.
  Defined.

  Definition senv : Type := ptree (list (ident * mtyp)).

  Definition senv_get (se: senv) (x: ident) : res (list (ident * mtyp)) :=
    err_of_opt (tget se x).

  Definition senv_update (se: senv) (x: ident) (fields: list (ident * mtyp)) : res senv :=
    match senv_get se x with
    | OK _ => MonError.fail
    | Error _ => eret (tset se x fields)
    end.

  Definition gcontext : Type := ptree mtyp.

  Definition lcontext : Type := ptree mtyp.

  Definition gcontext_get (gx: gcontext) (x: ident) : res mtyp :=
    match tget gx x with
    | Some t => eret t
    | None => MonError.fail
    end.

  Definition gcontext_update (gx: gcontext) (x: ident) (ty: mtyp) : res gcontext :=
    match gcontext_get gx x with
    | OK _ => MonError.fail
    | Error _ => eret (tset gx x ty)
    end.

  Definition lcontext_get (lx: lcontext) (x: ident) : res mtyp :=
    match tget lx x with
    | Some t => eret t
    | None => MonError.fail
    end.

  Definition lcontext_update (lx: lcontext) (x: ident) (ty: mtyp) : res lcontext :=
    match lcontext_get lx x with
    | OK t =>
        if mtyp_eq_dec ty t then eret (tset lx x ty)
        else
          MonError.fail
    | Error _ => eret (tset lx x ty)
    end.

  Open Scope state_err_monad_scope.

  Definition fresh_var : crmon ident := Utils.fresh_var_err "x".

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
    | MStruct s1, MStruct s2 =>
        if Ident.eq_dec s1 s2 then ret (AApp f l ty2)
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
    match eta_expand_rec f ty1 ty2 nil 0 with
    | OK (a, _) => OK a
    | Error e => Error e
    end.
  
  Definition typof_var (gx: gcontext) (lx: lcontext) (x: ident) : res mtyp :=
    match (lcontext_get lx x) with
    | OK ty => eret ty
    | Error _ => gcontext_get gx x
    end.

  Definition typecheck_cast (from: mtyp) (to: mtyp) : res mtyp :=
    match from with
    | MBool | MInt32 _ | MInt64 _ =>
      match to with
      | MBool | MInt32 _ | MInt64 _ => eret to
      | _ => MonError.fail
      end
    | _ => MonError.fail
    end.

  Definition typecheck_unary_op (op: unary_op) (ty: mtyp) : res mtyp :=
    match op, ty with
    | UopNotbool, MBool
    | UopNotint, MInt32 _
    | UopNotint, MInt64 _
    | UopNeg, MInt32 _
    | UopNeg, MInt64 _ => eret ty
    | _, _ => MonError.fail
    end.

  Definition typecheck_binary_op (op: binary_op) (ty1 ty2: mtyp) : res mtyp :=
    match op with
    | BopAndbool
    | BopOrbool
    | BopXorbool =>
        match ty1, ty2 with
        | MBool, MBool => eret ty1
        | _, _ => MonError.fail
        end
    | BopEq
    | BopNeq =>
        match ty1, ty2 with
        | MBool, MBool => eret ty1
        | MInt32 s1, MInt32 s2
        | MInt64 s1, MInt64 s2 =>
            if signedness_eq_dec s1 s2 then eret MBool
            else MonError.fail
        | _, _ => MonError.fail
        end
    | BopLt
    | BopLe 
    | BopGt
    | BopGe =>
        match ty1, ty2 with
        | MInt32 s1, MInt32 s2
        | MInt64 s1, MInt64 s2 =>
            if signedness_eq_dec s1 s2 then eret MBool
            else MonError.fail
        | _, _ => MonError.fail
        end
    | _ =>
        match ty1, ty2 with
        | MInt32 s1, MInt32 s2
        | MInt64 s1, MInt64 s2 =>
            if signedness_eq_dec s1 s2 then eret ty1
            else MonError.fail
        | _, _ => MonError.fail
        end
    end.

  Definition typecheck_array_get (ty1 ty2: mtyp) : res mtyp :=
    match ty1, ty2 with
    | MArray ta, MInt32 Unsigned => eret (MRes ta)
    | _, _ => MonError.fail
    end.

  Definition typecheck_atom_against (a: atom) (ty: mtyp) : res atom :=
    match a with
    | AVar x ((MFun _ _) as tx) => eta_expand x tx ty
    | _ =>
        if mtyp_eq_dec (typof_atom a) ty then eret a
        else MonError.fail
    end.

  Definition typecheck_array_set (ty1 ty2: mtyp) (a3: atom) : res (atom * mtyp) :=
    let tr := MRes ty1 in
    match ty1, ty2 with
    | MArray ta, MInt32 Unsigned =>
        let* a3' := typecheck_atom_against a3 ta in
        eret (a3', tr)
    | _, _ => MonError.fail
    end.      

  Definition mtypof_field (k: ident) (fields: list (ident * mtyp)) : res mtyp :=
    find_k_err Ident.eq_dec k fields.

  Definition typecheck_struct_proj (se: senv) (ty: mtyp) (x: ident) : res mtyp :=
    match ty with
    | MStruct t =>
        let* fields := senv_get se t in
        mtypof_field x fields
    | _ => MonError.fail
    end.

  Definition typecheck_struct_update (se: senv) (ty1: mtyp) (a2: atom) (x: ident) : res (atom * mtyp) :=
    match ty1 with
    | MStruct t =>
        let* fields := senv_get se t in
        let* tx := mtypof_field x fields in
        let* a2' := typecheck_atom_against a2 tx in
        eret (a2', ty1)
    | _ => MonError.fail
    end.

  Fixpoint monadify_ctyp (ty: ctyp) : mtyp :=
    match ty with
    | CBool => MBool
    | CInt32 s => MInt32 s
    | CInt64 s => MInt64 s
    | CArray ta => MArray (monadify_ctyp ta)
    | CStruct s => MStruct s
    | CFun tparams tret =>
        MFun (map monadify_ctyp tparams) (MRes (monadify_ctyp tret))
    end.

  Fixpoint typecheck_atom (se : senv) (gx: gcontext) (lx: lcontext) (a: BNF.atom) : res atom :=
    match a with
    | BNF.ATrue => eret (ATrue MBool)
    | BNF.AFalse => eret (AFalse MBool)
    | BNF.AInt32 i s => eret (AInt32 i (MInt32 s))
    | BNF.AInt64 i s => eret (AInt64 i (MInt64 s))
    | BNF.AVar x =>
        let* t := typof_var gx lx x in
        eret (AVar x t)
    | BNF.ACast a1 ty =>
        let* a1' := typecheck_atom se gx lx a1 in
        let t := monadify_ctyp ty in
        eret (ACast a1' t)
    | BNF.AUnaryOp op a1 =>
        let* a1' := typecheck_atom se gx lx a1 in
        let ty1 := typof_atom a1' in
        let* t := typecheck_unary_op op ty1 in
        eret (AUnaryOp op a1' t)
    | BNF.ABinaryOp op a1 a2 =>
        let* a1' := typecheck_atom se gx lx a1 in
        let* a2' := typecheck_atom se gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* t := typecheck_binary_op op ty1 ty2 in
        eret (ABinaryOp op a1' a2' t)
    | BNF.AStructProj a1 x =>
        let* a1' := typecheck_atom se gx lx a1 in
        let ty1 := typof_atom a1' in
        let* t := typecheck_struct_proj se ty1 x in
        eret (AStructProj a1' x t)
    | BNF.AStructUpdate a1 x a2 =>
        let* a1' := typecheck_atom se gx lx a1 in
        let* a2' := typecheck_atom se gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* (a2', t) := typecheck_struct_update se ty1 a2' x in
        eret (AStructUpdate a1' x a2' t)
    end.

  Fixpoint typecheck_call_rec (tparams: list mtyp) (args: list atom) (tret: mtyp) : res (list atom * mtyp) :=
    match tparams, args with
    | nil, nil => eret (nil, tret)
    | tp1 :: tparams', a1 :: args' =>
        let ta1 := typof_atom a1 in
        let* (args1, t) := typecheck_call_rec tparams' args' tret in
        let* a1' := typecheck_atom_against a1 tp1 in
        eret (a1' :: args1, t)
    | _, _ => MonError.fail
    end.

  Definition typecheck_call (ty1: mtyp) (args: list atom) : res (list atom * mtyp) :=
    match ty1 with
    | MFun tparams tret => typecheck_call_rec tparams args tret
    | _ => MonError.fail
    end.

  Fixpoint wrap_mtyp (ty: mtyp) : mtyp :=
    match ty with
    | MBool
    | MInt32 _
    | MInt64 _
    | MArray _
    | MStruct _ => MRes ty
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
      | ATrue _
      | AFalse _
      | AInt32 _ _
      | AInt64 _ _
      | ACast _ _
      | AUnaryOp _ _ _
      | ABinaryOp _ _ _  _
      | AStructProj _ _ _
      | AStructUpdate _ _ _ _ => eret a
      | AVar x _ =>
          match ty with
          | MFun _ _ => eta_expand x ty (unwrap_mtyp ty')
          | _ => eret a
          end
      | _ => MonError.fail
      end
    in eret (ERet a' ty').

  Fixpoint monadify_expr_rec (se: senv) (gx: gcontext) (lx: lcontext) (e: BNF.expr) (imp: bool) : res expr :=
    match e with
    | BNF.EAtom a =>
        let* a' := typecheck_atom se gx lx a in
        if imp then wrap_atom a'
        else eret (EAtom a' (typof_atom a'))
    | BNF.EArrayGet a1 a2 =>
        let* a1' := typecheck_atom se gx lx a1 in
        let* a2' := typecheck_atom se gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* t := typecheck_array_get ty1 ty2 in
        eret (EArrayGet a1' a2' t)
    | BNF.EArraySet a1 a2 a3 =>
        let* a1' := typecheck_atom se gx lx a1 in
        let* a2' := typecheck_atom se gx lx a2 in
        let* a3' := typecheck_atom se gx lx a3 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let ty3 := typof_atom a3' in
        let* (a3', t) := typecheck_array_set ty1 ty2 a3' in
        eret (EArraySet a1' a2' a3' t)
    | BNF.EApp a1 args =>
        let* a1' := typecheck_atom se gx lx a1 in
        let ty1 := typof_atom a1' in
        let* args' := mmap (typecheck_atom se gx lx) args in
        let* (args1, t) := typecheck_call ty1 args' in
        eret (EApp a1' args1 t)
    | BNF.EIfThenElse a e1 e2 =>
        let* a' := typecheck_atom se gx lx a in
        match (typof_atom a') with
        | MBool =>
            let* e1' := monadify_expr_rec se gx lx e1 imp in
            let* e2' := monadify_expr_rec se gx lx e2 imp in
            let ty1 := typof_expr e1' in
            let ty2 := typof_expr e2' in
            if mtyp_eq_dec ty1 ty2 then
              eret (EIfThenElse a' e1' e2' ty1)
            else
              (* It is possible that one branch contains monadic operations and not the other one. *)
              (* In this case, we have to re-monadify the non-monadic branch by setting the imperative 
                 flag to true. *)
              match ty1, ty2 with
              | MRes ty1', _ =>
                  if mtyp_eq_dec ty1' ty2 then
                    let* e2' := monadify_expr_rec se gx lx e2 true in
                    eret (EIfThenElse a' e1' e2' ty1)
                  else MonError.fail
              | _, MRes ty2' =>
                  if mtyp_eq_dec ty1 ty2' then
                    let* e1' := monadify_expr_rec se gx lx e1 true in
                    eret (EIfThenElse a' e1' e2' ty2)
                  else MonError.fail
              | _, _ =>
                  MonError.fail
              end
        | _ => MonError.fail
        end
    | BNF.ELetIn x e1 e2 =>
        let* e1' := monadify_expr_rec se gx lx e1 false in
        let t := typof_expr e1' in
        match t with
        | MRes tr =>
            let* lx' := lcontext_update lx x tr in
            let* e2' := monadify_expr_rec se gx lx' e2 true in
            eret (ELetMon x e1' e2' (typof_expr e2'))
        | _ =>
            let* lx' := lcontext_update lx x t in
            let* e2' := monadify_expr_rec se gx lx' e2 (imp || false) in
            eret (ELetIn x e1' e2' (typof_expr e2'))
        end
    end.
  
  Definition monadify_expr (se: senv) (gx: gcontext) (lx: lcontext) (e: BNF.expr) : res expr :=
    monadify_expr_rec se gx lx e false.

  Definition monadify_function (se: senv) (gx: gcontext) (f: BNF.function) : res function :=
    let params := map_k monadify_ctyp (Syntax.fn_params f) in
    let* lx :=
      fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        params
        (eret tempty)
    in
    let* body := monadify_expr se gx lx (Syntax.fn_body f) in
    eret {|
      fn_return := typof_expr body;
      fn_params := params;
      fn_body := body
    |}.

  Fixpoint monadify_globdefs_rec (se: senv) (gx: gcontext) (defs: list BNF.globdef) : res (list globdef) :=
    match defs with
    | nil => eret nil
    | Syntax.DefConst x l ty :: defs' =>
        let ty' := monadify_ctyp ty in
        let* gx' := gcontext_update gx x ty' in
        let* r := monadify_globdefs_rec se gx' defs' in
        eret (DefConst x l ty' :: r) 
    | Syntax.DefFun x f :: defs' =>
        let* f' := monadify_function se gx f in
        let tf := MFun (map snd (fn_params f')) (fn_return f') in
        let* gx' := gcontext_update gx x tf in
        let* r := monadify_globdefs_rec se gx' defs' in
        eret (DefFun x f' :: r)
    end.

  Definition monadify_globdefs (se: senv) (defs: list BNF.globdef) : res (list globdef) :=
    monadify_globdefs_rec se tempty defs.

  Definition monadify_program (prog: BNF.program) : res program :=
    let structs :=
      List.map
        (fun st =>
          let fields := MapList.map_k monadify_ctyp (Syntax.sd_fields st) in
          {| sd_name := Syntax.sd_name st; sd_fields := fields |})
        (BNF.prog_types prog)
    in
    let* se :=
      Utils.fold_left_err
        (fun acc st =>
          senv_update acc (Monadic.sd_name st) (Monadic.sd_fields st))
        structs
        (eret tempty)
    in
    let* defs := monadify_globdefs se (BarocqShallow.BNF.prog_defs prog) in
    eret {|
      prog_types := structs;
      prog_defs := defs;
    |}.

End Monadification.

Open Scope error_monad_scope.

Definition monadify_norm_program (prog: Barocq.program) : res Monadic.program :=
  (* let prog := BarocqTransf.rename_idents_program prog in *)
  let* bnf := Normalization.norm_program prog in
  Monadification.monadify_program bnf.