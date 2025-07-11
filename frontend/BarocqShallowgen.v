From Coq Require Import List String.
From compcert Require Import Maps.
From BarocqComp Require Import Monads Error MapList Types Utils Syntax Barocq BarocqTransf BarocqShallow.
Import ListNotations.
Import MonCounterErr.

Module Normalization.

  Import BNF.

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
    let fix norm_expr_aux (e: Barocq.expr) : crmon (list (ident * BNF.expr) * atom) :=
      match e with
      | ETrue => ret (nil, ATrue)
      | EFalse => ret (nil, AFalse)
      | Barocq.EInt32 i s => ret (nil, AInt32 i s)
      | Barocq.EInt64 i s => ret (nil, AInt64 i s)
      | Barocq.EVar x => ret (nil, AVar x)
      | Barocq.ECast e1 ty =>
          let* (li1, a1) := norm_expr_aux e1 in
          ret (li1, ACast a1 ty)
      | EUnaryOp op e1 =>
          let* (li, a1) := norm_expr_aux e1 in
          ret (li, AUnaryOp op a1)
      | EBinaryOp op e1 e2 =>
          match op with
          | BopDiv | BopMod =>
              let* x := fresh_var in
              let* be := norm_expr_rec e in
              ret ((x, be) :: nil, AVar x)
          | _ =>
            let* (li1, a1) := norm_expr_aux e1 in
            let* (li2, a2) := norm_expr_aux e2 in
            ret (li1 ++ li2, ABinaryOp op a1 a2)
          end
      | EStructProj e1 f =>
          let* (li1, a1) := norm_expr_aux e1 in
          ret (li1, AStructProj a1 f)
      | EStructUpdate e1 f e2 =>
          let* (li1, a1) := norm_expr_aux e1 in
          let* (li2, a2) := norm_expr_aux e2 in
          ret (li1 ++ li2, AStructUpdate a1 f a2)
      | _ =>
          let* x := fresh_var in
          let* be := norm_expr_rec e in
          ret ((x, be) :: nil, AVar x)
      end
    in
    let fix mk_norm (le: list (ident * BNF.expr)) (e: expr) : BNF.expr :=
      match le with
      | nil => e
      | (x, be) :: le' =>
          ELetIn x be (mk_norm le' e)
      end
    in
    let fix norm_exprlist_rec (e: Barocq.expr) (la: list atom) (le: list Barocq.expr) : crmon (list (ident * BNF.expr) * BNF.expr) :=
      match le with
      | nil =>
          let* er := lift_err (spread_atomlist e (rev' la)) in
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
        let* (le, c) := norm_expr_aux e1 in
        let* ne2 := norm_expr_rec e2 in
        let* ne3 := norm_expr_rec e3 in
        ret (mk_norm le (EIfThenElse c ne2 ne3))
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

  Fixpoint norm_program_rec (prog: Barocq.program) : res (list BarocqShallow.BNF.globdef * list type_def) :=
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
            let* (ndefs, types):= norm_program_rec prog' in
            eret (Syntax.DefFun x f' :: ndefs, types)
        | Barocq.DeclType t tk =>
            let* (ndefs, types) := norm_program_rec prog' in
            eret (ndefs, TdAbstract t tk :: types)
        | Barocq.DeclConst x ty =>
            let* (ndefs, types) := norm_program_rec prog' in
            eret (Syntax.DeclConst x ty :: ndefs, types)
        | Barocq.DeclFun f tparams tret =>
            let* (ndefs, types) := norm_program_rec prog' in
            eret (Syntax.DeclFun f tparams tret :: ndefs, types)
        end
    end.
    
  Definition norm_program (prog: Barocq.program) : res BNF.program :=
    let* (defs, types) := norm_program_rec prog in
    eret {|
      prog_defs := defs;
      prog_types := types
    |}.

End Normalization.

Module Monadification.

  Import Monadic.

  Definition arr_index_mtyp : mtyp :=
    if Archi.ptr64 then MInt64 Unsigned else MInt32 Unsigned.

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
            if signedness_eq_dec s1 s2 then
              match op with
              | BopDiv | BopMod => eret (MRes ty1)
              | _ => eret ty1
              end
            else MonError.fail
        | _, _ => MonError.fail
        end
    end.

  Definition typecheck_array_get (ty1 ty2: mtyp) : res mtyp :=
    match ty1 with
    | MArray ta => 
        if mtyp_eq_dec ty2 arr_index_mtyp then
          eret (MRes ta)
        else MonError.fail
    | _ => MonError.fail
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
    match ty1 with
    | MArray ta =>
        if mtyp_eq_dec ty2 arr_index_mtyp then
          let* a3' := typecheck_atom_against a3 ta in
          eret (a3', tr)
        else MonError.fail
    | _ => MonError.fail
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

  Fixpoint monadify_btyp (ty: btyp) : mtyp :=
    match ty with
    | BBool => MBool
    | BInt32 s => MInt32 s
    | BInt64 s => MInt64 s
    | BArray ta => MArray (monadify_btyp ta)
    | BStruct s => MStruct s
    | BFun tparams tret =>
        MFun (map monadify_btyp tparams) (MRes (monadify_btyp tret))
    | BAbs t => MAbs t
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
        let t := monadify_btyp ty in
        if mtyp_eq_dec (typof_atom a1') t then eret a1'
        else eret (ACast a1' t)
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
    | MStruct _ 
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
    in eret (ERet (EAtom a' (typof_atom a')) ty').

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
        let e' := EApp a1' args1 t in
        if imp then
          match t with
          | MRes _ => eret e'
          | _ => eret (ERet e' (MRes t))
          end
        else eret e'
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
    let params := map_k monadify_btyp (Syntax.fn_params f) in
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

  Fixpoint make_absfun_tparams (tparams1: list (param_attr * btyp)) (tparams2 : list mtyp) : res (list (param_attr * mtyp)) :=
    match tparams1, tparams2 with
    | nil, nil => eret nil
    | (attr1, t1) :: tparams1', t2 :: tparams2' =>
        let* r := make_absfun_tparams tparams1' tparams2' in
        eret ((attr1, t2) :: r)
    | _, _ => MonError.fail
    end.

  Fixpoint monadify_globdefs_rec (se: senv) (gx: gcontext) (defs: list BNF.globdef) : res (list globdef) :=
    match defs with
    | nil => eret nil
    | d :: defs' =>
        match d with
        | Syntax.DefConst x l ty =>
            let ty' := monadify_btyp ty in
            let* gx' := gcontext_update gx x ty' in
            let* r := monadify_globdefs_rec se gx' defs' in
            eret (DefConst x l ty' :: r) 
        | Syntax.DefFun x f =>
            let* f' := monadify_function se gx f in
            let tf := MFun (map snd (fn_params f')) (fn_return f') in
            let* gx' := gcontext_update gx x tf in
            let* r := monadify_globdefs_rec se gx' defs' in
            eret (DefFun x f' :: r)
        | Syntax.DeclConst x ty =>
            let ty' := monadify_btyp ty in
            let* gx' := gcontext_update gx x ty' in
            let* r := monadify_globdefs_rec se gx' defs' in
            eret (DeclConst x ty' :: r)
        | Syntax.DeclFun f tparams tret =>
            let ty' := monadify_btyp (mk_fun_btyp tparams tret) in
            let* gx' := gcontext_update gx f ty' in
            let* r := monadify_globdefs_rec se gx' defs' in
            match ty' with
            | MFun tparams' tret' =>
                let* tparams' := make_absfun_tparams tparams tparams' in
                eret (DeclFun f tparams' tret' :: r)
            | _ => MonError.fail
            end
        end
    end.

  Definition monadify_globdefs (se: senv) (defs: list BNF.globdef) : res (list globdef) :=
    monadify_globdefs_rec se tempty defs.

  Definition monadify_program (prog: BNF.program) : res program :=
    let types :=
      List.map
        (fun td =>
          match td with
          | Syntax.TdStruct st =>
              let fields := MapList.map_k monadify_btyp (Syntax.sd_fields st) in
              TdStruct {| sd_name := Syntax.sd_name st; sd_fields := fields |}
          | Syntax.TdAbstract t tk => TdAbstract t tk
          end)
        (BNF.prog_types prog)
    in
    let* se :=
      Utils.fold_left_err
        (fun acc td =>
          match td with
          | TdStruct st =>
            senv_update acc (Monadic.sd_name st) (Monadic.sd_fields st)
          | TdAbstract _ _ => eret acc
          end)
        types
        (eret tempty)
    in
    let* defs := monadify_globdefs se (BarocqShallow.BNF.prog_defs prog) in
    eret {|
      prog_types := types;
      prog_defs := defs;
    |}.

End Monadification.

Open Scope error_monad_scope.

Definition monadify_norm_program (prog: Barocq.program) : res Monadic.program :=
  let/catch bnf := Normalization.norm_program prog /> "unable to normalize the program" in
  let/catch mon := Monadification.monadify_program bnf /> "unable to monadify the program" in
  eret mon.