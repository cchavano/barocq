From Coq Require Import PArith String List.
From compcert Require Import Clightdefs Integers.
From BarocqComp Require Import Error Monads Utils Syntax Types Barocq BarocqBNF.
Import ListNotations.
Import MonCounterErr.

(** Creation of deep accesses. *)

(* The parser does not create deep access expressions. Each deep access
   eX1X2...Xn is parsed as being (...((eX1)X2)...)Xn, i.e. a sequence of
   EArrayGet and EStructProj, and not as EDeepAccess.
   We first create deep access expressions for all deep accesses to a primitive value. *)

Fixpoint access_list_typ (acs: list BarocqTyped.access) : ctyp :=
  match acs with
  | nil => CBool (* arbitrary type here *)
  | ac :: nil =>
      match ac with
      | BarocqTyped.AcStructField _ ty => ty
      | BarocqTyped.AcArrayIndex _ ty => ty
      end
  | _ :: acs' => access_list_typ acs'
  end.

Definition create_deep_access_aux
  (cda: BarocqTyped.expr -> list Barocq.access -> Barocq.expr * (list Barocq.access))
  (e: BarocqTyped.expr) : Barocq.expr :=
  match cda e nil with
  | (e', nil) => e'
  | (e', _ as acs) =>
      Barocq.EDeepAccess e' acs
  end.

Fixpoint create_deep_access_rec (e: BarocqTyped.expr) (acs: list Barocq.access) : Barocq.expr * (list Barocq.access) :=
  match e with
  | BarocqTyped.ETrue _ => (Barocq.ETrue, acs)
  | BarocqTyped.EFalse _ => (Barocq.EFalse, acs)
  | BarocqTyped.EInt32 i (CInt32 s) => (Barocq.EInt32 i s, acs)
  | BarocqTyped.EInt64 i (CInt64 s) => (Barocq.EInt64 i s, acs)
  | BarocqTyped.EVar x _ => (Barocq.EVar x, acs)
  | BarocqTyped.EArrayGet e1 e2 ty =>
      let e2' := create_deep_access_aux create_deep_access_rec e2 in
      if orb (ctyp_is_prim ty) (negb (list_is_empty acs)) then
        create_deep_access_rec e1 (AcArrayIndex e2' :: acs)
      else
        let e1' := create_deep_access_aux create_deep_access_rec e1 in
        (Barocq.EArrayGet e1' e2', acs)
  | BarocqTyped.EStructProj e1 f ty =>
      if orb (ctyp_is_prim ty) (negb (list_is_empty acs)) then
        create_deep_access_rec e1 (AcStructField f :: acs)
      else
        let e1' := create_deep_access_aux create_deep_access_rec e1 in
        (Barocq.EStructProj e1' f, acs)
  | BarocqTyped.ECast e1 ty =>
      let e1' := create_deep_access_aux create_deep_access_rec e1 in
      (Barocq.ECast e1' ty, acs)
  | BarocqTyped.EUnaryOp op e1 _ =>
      let e1' := create_deep_access_aux create_deep_access_rec e1 in
      (Barocq.EUnaryOp op e1', acs)
  | BarocqTyped.EBinaryOp op e1 e2 _ =>
      let e1' := create_deep_access_aux create_deep_access_rec e1 in
      let e2' := create_deep_access_aux create_deep_access_rec e2 in
      (Barocq.EBinaryOp op e1' e2', acs)
  | BarocqTyped.EArraySet e1 e2 e3 _ =>
      let e1' := create_deep_access_aux create_deep_access_rec e1 in
      let e2' := create_deep_access_aux create_deep_access_rec e2 in
      let e3' := create_deep_access_aux create_deep_access_rec e3 in
      (Barocq.EArraySet e1' e2' e3', acs)
  | BarocqTyped.EStructUpdate e1 f e2 _ =>
      let e1' := create_deep_access_aux create_deep_access_rec e1 in
      let e2' := create_deep_access_aux create_deep_access_rec e2 in
      (Barocq.EStructUpdate e1' f e2', acs)
  | BarocqTyped.EDeepAccess e1 acs1 ty =>
      (* Should be dead code. *)
      let e1' := create_deep_access_aux create_deep_access_rec e1 in
      let acs1' :=
        List.map
          (fun ac =>
            match ac with
            | BarocqTyped.AcStructField f _ => AcStructField f
            | BarocqTyped.AcArrayIndex ei _ =>
                let ei' := create_deep_access_aux create_deep_access_rec ei in
                AcArrayIndex ei'
            end)
          acs1
      in
      if orb (ctyp_is_prim ty) (negb (list_is_empty acs)) then
        (e1', acs1' ++ acs)
      else
        (Barocq.EDeepAccess e1' acs1', acs)
  | BarocqTyped.EApp e1 args _ =>
      let e1' := create_deep_access_aux create_deep_access_rec e1 in
      let args' := List.map (create_deep_access_aux create_deep_access_rec) args in
      (Barocq.EApp e1' args', acs)
  | BarocqTyped.EIfThenElse e1 e2 e3 _ =>
      let e1' := create_deep_access_aux create_deep_access_rec e1 in
      let e2' := create_deep_access_aux create_deep_access_rec e2 in
      let e3' := create_deep_access_aux create_deep_access_rec e3 in
      (Barocq.EIfThenElse e1' e2' e3', acs)
  | BarocqTyped.ELetIn x e1 e2 _ =>
      let e1' := create_deep_access_aux create_deep_access_rec e1 in
      let e2' := create_deep_access_aux create_deep_access_rec e2 in
      (Barocq.ELetIn x e1' e2', acs)
  | _ =>
    (* The rest are ill-typed constant integers, we return an arbitraty expression. *)
    (ETrue, acs)
  end.

Definition create_deep_access (e: BarocqTyped.expr) : Barocq.expr :=
  create_deep_access_aux create_deep_access_rec e.

(** Normalization *)

Fixpoint atom_of_expr (e: Barocq.expr) : res atom :=
  match e with
  | Barocq.ETrue => eret ATrue
  | Barocq.EFalse => eret AFalse
  | Barocq.EInt32 i s => eret (AInt32 i s)
  | Barocq.EInt64 i s => eret (AInt64 i s)
  | Barocq.EVar x => eret (AVar (transl_user_ident x))
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

Definition fresh_var : crmon ident := Utils.fresh_var_err "b".

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
  let fix normalize_access_list_rec (a: atom) (acs: list Barocq.access) (acs_norm: list Syntax.access)
    : crmon BarocqBNF.expr :=
    match acs with
    | nil => ret (EDeepAccess a (rev acs_norm))
    | ac :: acs' =>
        match ac with
        | Barocq.AcStructField f =>
            normalize_access_list_rec a acs' (Syntax.AcStructField f :: acs_norm)
        | Barocq.AcArrayIndex e =>
            match atom_of_expr e with
            | OK ae => normalize_access_list_rec a acs' ((Syntax.AcArrayIndex ae) :: acs_norm)
            | Error _ =>
              let* xe := fresh_var in
              let* be := normalize_expr_rec e in
              let* ber := normalize_access_list_rec a acs' ((Syntax.AcArrayIndex (AVar xe)) :: acs_norm) in
              ret (ELetIn xe be ber)
            end
        end
    end
  in
  let normalize_deep_access (e: Barocq.expr) (acs: list Barocq.access) : crmon BarocqBNF.expr :=
    match atom_of_expr e with
    | OK a => normalize_access_list_rec a acs nil
    | Error _ =>
        let* x := fresh_var in
        let* be := normalize_expr_rec e in
        let* bacs := normalize_access_list_rec (AVar x) acs nil in
        ret (ELetIn x be bacs)
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
      ret (EAtom (AVar (transl_user_ident x)))
  | Barocq.ECast e1 ty =>
      normalize_exprlist e [e1]
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
  | Barocq.EDeepAccess e1 acs =>
      normalize_deep_access e1 acs
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

Definition normalize_expr (e: BarocqTyped.expr) : res BarocqBNF.expr :=
  let e := create_deep_access e in
  let* ne := normalize_expr_rec e 0 in
  eret (fst ne).

Definition normalize_params (params: list (ident * ctyp)) : list (ident * ctyp) :=
  map (fun '(x, tx) => (transl_user_ident x, tx)) params.

Definition normalize_function (f: BarocqTyped.function) : res BarocqBNF.function :=
  let* body_norm := normalize_expr (fn_body f) in
  eret {|
    fn_return := fn_return f;
    fn_params := normalize_params (fn_params f);
    fn_body := body_norm
  |}.

Fixpoint normalize_program_rec (ts: types) (prog: BarocqTyped.program) : res BarocqBNF.program :=
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
          normalize_program_rec ts' prog'
      | BarocqTyped.DefConst x l ty =>
          let* r := normalize_program_rec ts prog' in
          eret {|
            prog_defs := (Syntax.DefConst (transl_user_ident x) l ty) :: (prog_defs r);
            prog_types := (prog_types r)
          |}
      | BarocqTyped.DefFun x f =>
          let* f' := normalize_function f in
          let* r := normalize_program_rec ts prog' in
          eret {|
            prog_defs := (Syntax.DefFun (transl_user_ident x) f') :: (prog_defs r);
            prog_types := prog_types r
          |}
      end
  end.

Definition normalize_program (prog: BarocqTyped.program) : res BarocqBNF.program :=
  normalize_program_rec tempty prog.