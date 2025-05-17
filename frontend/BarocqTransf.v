From Coq Require Import List String.
From BarocqComp Require Import Error Utils Types Syntax Barocq.

(** * Barocq to Barocq transformations *)

(** ** Transformation of logical AND/OR expressions *)

Fixpoint transf_logical_expr (e: Barocq.expr) : Barocq.expr :=
  let fix transf_logical_access (ac: Barocq.access) : Barocq.access :=
    match ac with
    | AcArrayIndex e1 => AcArrayIndex (transf_logical_expr e1)
    | _ => ac
    end
  in
  match e with
  | ETrue
  | EFalse
  | EInt32 _ _
  | EInt64 _ _
  | EVar _ => e
  | ECast e1 ty =>
      let e1' := transf_logical_expr e1 in
      ECast e1' ty
  | EUnaryOp op e1 =>
      let e1' := transf_logical_expr e1 in
      EUnaryOp op e1'
  | EBinaryOp op e1 e2 =>
      let e1' := transf_logical_expr e1 in
      let e2' := transf_logical_expr e2 in
      match op with
      | BopAndbool => EIfThenElse e1' e2' (EFalse)
      | BopOrbool => EIfThenElse e1' (ETrue) e2'
      | _ => e
      end
  | EArrayGet e1 e2 =>
      let e1' := transf_logical_expr e1 in
      let e2' := transf_logical_expr e2 in
      EArrayGet e1' e2'
  | EArraySet e1 e2 e3 =>
      let e1' := transf_logical_expr e1 in
      let e2' := transf_logical_expr e2 in
      let e3' := transf_logical_expr e3 in
      EArraySet e1' e2' e3'
  | EStructProj e1 f =>
      let e1' := transf_logical_expr e1 in
      EStructProj e1' f
  | EStructUpdate e1 f e2 =>
      let e1' := transf_logical_expr e1 in
      let e2' := transf_logical_expr e2 in
      EStructUpdate e1' f e2'
  | EDeepAccess e1 acs =>
      let e1' := transf_logical_expr e1 in
      let acs' := List.map transf_logical_access acs in
      EDeepAccess e1' acs'
  | EApp e1 args =>
      let e1' := transf_logical_expr e1 in
      let args' := List.map transf_logical_expr args in
      EApp e1' args'
  | EIfThenElse e1 e2 e3 =>
      let e1' := transf_logical_expr e1 in
      let e2' := transf_logical_expr e2 in
      let e3' := transf_logical_expr e3 in
      EIfThenElse e1' e2' e3'
  | ELetIn x e1 e2 =>
      let e1' := transf_logical_expr e1 in
      let e2' := transf_logical_expr e2 in
      ELetIn x e1' e2' 
  end.

Definition transf_logical_function (f: Barocq.function) : Barocq.function :=
  {|
    fn_return := fn_return f;
    fn_params := fn_params f;
    fn_body := transf_logical_expr (fn_body f)
  |}.

Definition transf_logical_globdef (def: Barocq.globdef) : Barocq.globdef :=
  match def with
  | DefFun x f => DefFun x (transf_logical_function f)
  | _ => def
  end.

Definition transf_logical_program (prog: Barocq.program) : Barocq.program :=
  List.map transf_logical_globdef prog.

(** ** Generation of deep accesses *)

(* The parser does not create deep access expressions. Each deep access
   eX1X2...Xn is parsed as (...((eX1)X2)...)Xn, i.e. a sequence of
   EArrayGet and EStructProj, not as a EDeepAccess.
   Deep accesses are only generated for accesses to a primitive value. *)

Fixpoint access_list_typ (acs: list BarocqTyped.access) : btyp :=
  match acs with
  | nil => BBool (* arbitrary type *)
  | ac :: nil =>
      match ac with
      | BarocqTyped.AcStructField _ ty => ty
      | BarocqTyped.AcArrayIndex _ ty => ty
      end
  | _ :: acs' => access_list_typ acs'
  end.

Fixpoint create_deep_access_expr (e: BarocqTyped.expr) : Barocq.expr :=
  let fix create_deep_access_rec (e: BarocqTyped.expr) (acs: list Barocq.access)
    : Barocq.expr * (list Barocq.access) :=
    match e with
    | BarocqTyped.ETrue _ => (Barocq.ETrue, acs)
    | BarocqTyped.EFalse _ => (Barocq.EFalse, acs)
    | BarocqTyped.EInt32 i (BInt32 s) => (Barocq.EInt32 i s, acs)
    | BarocqTyped.EInt64 i (BInt64 s) => (Barocq.EInt64 i s, acs)
    | BarocqTyped.EVar x _ => (Barocq.EVar x, acs)
    | BarocqTyped.EArrayGet e1 e2 ty =>
        let e2' := create_deep_access_expr e2 in
        if orb (ctyp_is_prim ty) (negb (list_is_empty acs)) then
          create_deep_access_rec e1 (AcArrayIndex e2' :: acs)
        else
          let e1' := create_deep_access_expr e1 in
          (Barocq.EArrayGet e1' e2', acs)
    | BarocqTyped.EStructProj e1 f ty =>
        if orb (ctyp_is_prim ty) (negb (list_is_empty acs)) then
          create_deep_access_rec e1 (AcStructField f :: acs)
        else
          let e1' := create_deep_access_expr e1 in
          (Barocq.EStructProj e1' f, acs)
    | BarocqTyped.ECast e1 ty =>
        let e1' := create_deep_access_expr e1 in
        (Barocq.ECast e1' ty, acs)
    | BarocqTyped.EUnaryOp op e1 _ =>
        let e1' := create_deep_access_expr e1 in
        (Barocq.EUnaryOp op e1', acs)
    | BarocqTyped.EBinaryOp op e1 e2 _ =>
        let e1' := create_deep_access_expr e1 in
        let e2' := create_deep_access_expr e2 in
        (Barocq.EBinaryOp op e1' e2', acs)
    | BarocqTyped.EArraySet e1 e2 e3 _ =>
        let e1' := create_deep_access_expr e1 in
        let e2' := create_deep_access_expr e2 in
        let e3' := create_deep_access_expr e3 in
        (Barocq.EArraySet e1' e2' e3', acs)
    | BarocqTyped.EStructUpdate e1 f e2 _ =>
        let e1' := create_deep_access_expr e1 in
        let e2' := create_deep_access_expr e2 in
        (Barocq.EStructUpdate e1' f e2', acs)
    | BarocqTyped.EDeepAccess e1 acs1 ty =>
        (* Should be dead code. *)
        let e1' := create_deep_access_expr e1 in
        let acs1' :=
          List.map
            (fun ac =>
              match ac with
              | BarocqTyped.AcStructField f _ => AcStructField f
              | BarocqTyped.AcArrayIndex ei _ =>
                  let ei' := create_deep_access_expr ei in
                  AcArrayIndex ei'
              end)
            acs1
        in
        if orb (ctyp_is_prim ty) (negb (list_is_empty acs)) then
          (e1', acs1' ++ acs)
        else
          (Barocq.EDeepAccess e1' acs1', acs)
    | BarocqTyped.EApp e1 args _ =>
        let e1' := create_deep_access_expr e1 in
        let args' := List.map (create_deep_access_expr) args in
        (Barocq.EApp e1' args', acs)
    | BarocqTyped.EIfThenElse e1 e2 e3 _ =>
        let e1' := create_deep_access_expr e1 in
        let e2' := create_deep_access_expr e2 in
        let e3' := create_deep_access_expr e3 in
        (Barocq.EIfThenElse e1' e2' e3', acs)
    | BarocqTyped.ELetIn x e1 e2 _ =>
        let e1' := create_deep_access_expr e1 in
        let e2' := create_deep_access_expr e2 in
        (Barocq.ELetIn x e1' e2', acs)
    | _ =>
      (* The rest are ill-typed constant integers, we return an arbitraty expression. *)
      (ETrue, acs)
    end
  in
  match create_deep_access_rec e nil with
  | (e', nil) => e'
  | (e', _ as acs) =>
      Barocq.EDeepAccess e' acs
  end.

Definition create_deep_access_function (f: BarocqTyped.function) : Barocq.function :=
  {|
    fn_return := fn_return f;
    fn_params := fn_params f;
    fn_body := create_deep_access_expr (fn_body f)
  |}.

Definition create_deep_access_globdef (def: BarocqTyped.globdef) : Barocq.globdef :=
  match def with
  | BarocqTyped.DefType s fields => DefType s fields
  | BarocqTyped.DefConst x l ty => DefConst x l ty
  | BarocqTyped.DefFun x f => DefFun x (create_deep_access_function f)
  | BarocqTyped.DeclType t tk => DeclType t tk
  | BarocqTyped.DeclConst x ty => DeclConst x ty
  | BarocqTyped.DeclFun f tparams tret => DeclFun f tparams tret
  end.

Definition create_deep_access_program (prog: BarocqTyped.program) : Barocq.program :=
  List.map create_deep_access_globdef prog.

(** ** Combination of the two transformations *)

Definition transf_program (prog: Barocq.program) : res Barocq.program :=
  let prog := transf_logical_program prog in
  let* prog := Barocq.Typing.typecheck_program prog in
  ret (create_deep_access_program prog).