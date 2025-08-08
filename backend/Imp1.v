From Coq Require Import List String.
From compcert Require Import Integers.
From BarocqComp Require Import Benum Error Maps2 Utils Syntax Types Typing Barray.

(** * Abstract syntax *)

(** ** Literals *)

Definition literal : Type := Syntax.literal.

(** ** Atoms *)

Definition atom : Type := Syntax.atom.

(** ** Statements *)
 
Inductive statement : Type :=
  | StSet : ident -> comp -> statement
  | StIfThenElse : atom -> statement -> statement -> statement
  | StSwitch : atom -> list (pattern * statement) -> statement
  | StSequence : statement -> statement -> statement
  | StReturn : atom -> statement.

(** ** Functions *)

Definition function : Type := Syntax.function statement.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function.

(** ** Programs *)

Definition program : Type := Syntax.program globdef.

Module Typed.

  (** * Typed abstract syntax *)

  (** ** Literals *)

  Definition literal : Type := Syntax.Typed.literal.

  (** ** Atoms *)
    
  Definition atom : Type := Syntax.Typed.atom.

  (** ** Computations *)

  Definition comp : Type := Syntax.Typed.comp.

  (** ** Statements *)

  Inductive statement : Type :=
    | StSet : ident -> comp -> statement
    | StIfThenElse : atom -> statement -> statement -> statement
    | StSwitch : atom -> list (pattern * statement) -> statement
    | StSequence : statement -> statement -> statement
    | StReturn : atom -> statement.

  (** ** Functions *)

  Definition function : Type := Syntax.function statement.

  (** ** Global definitions *)

  Definition globdef : Type := Syntax.globdef literal function.

  (** ** Programs *)

  Definition program : Type := Syntax.program globdef.

End Typed.

Module Aliasing_AST.

  (** * Typed abstract syntax with aliasing information *)

  Parameter ABSDOM : Type.

  (** ** Literals *)

  Definition literal : Type := Syntax.Typed.literal.

  (** ** Atoms *)
    
  Definition atom : Type := Syntax.Typed.atom.

  (** ** Computations *)

  Definition comp : Type := Syntax.Typed.comp.

  (** ** Statements *)

  Inductive statement : Type :=
    | StSet : ident -> comp -> ABSDOM -> ABSDOM -> statement
    | StIfThenElse : atom -> statement -> statement -> ABSDOM -> ABSDOM -> statement
    | StSwitch : atom -> list (pattern * statement) -> ABSDOM -> ABSDOM -> statement
    | StSequence : statement -> statement -> statement
    | StReturn : atom -> ABSDOM -> ABSDOM -> statement.

  (** ** Functions *)

  Definition function : Type := Syntax.function statement.

  (** ** Global definitions *)

  Definition globdef : Type := Syntax.globdef literal function.

  (** ** Programs *)

  Definition program : Type := Syntax.program globdef.

End Aliasing_AST.

Module Imp1Typed := Imp1.Typed.

Module Typing.

  Import Syntax.Typed.
  Import Imp1Typed.
  Import ListNotations.

  Section ARCHI.

  Variable arch : Target.archi.

  Fixpoint typecheck_atom (be: benv) (gx: gcontext) (lx: lcontext) (a: Syntax.atom) : res Syntax.Typed.atom :=
    match a with
    | Syntax.ATrue => ret (ATrue BBool)
    | Syntax.AFalse => ret (AFalse BBool)
    | Syntax.AInt32 i s => ret (AInt32 i (BInt32 s))
    | Syntax.AInt64 i s => ret (AInt64 i (BInt64 s))
    | Syntax.AConstr x =>
        let* t := typof_constr be x in
        ret (AConstr x t)
    | Syntax.AVar x =>
        let* t := typof_var gx lx x in
        ret (AVar x t)
    | Syntax.ACast a1 ty =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* t := typecheck_cast (typof_atom a1') ty in
        ret (ACast a1' t)
    | Syntax.AUnaryOp op a1 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let ty1 := typof_atom a1' in
        let* t := typecheck_unary_op op ty1 in
        ret (AUnaryOp op a1' t)
    | Syntax.ABinaryOp op a1 a2 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* t := typecheck_binary_op op ty1 ty2 in
        ret (ABinaryOp op a1' a2' t)
    end.

  Fixpoint typecheck_access (be: benv) (gx: gcontext) (lx: lcontext) (ty: btyp) (acs: list Syntax.access) : res (btyp * list Syntax.Typed.access) :=
    match acs with
    | nil => ret (ty, nil)
    | ac :: acs' =>
        match ac with
        | Syntax.AcRecordField f =>
            let* ty' := typecheck_record_proj be ty f in
            let* (r, lr) := typecheck_access be gx lx ty' acs' in
            ret (r, (AcRecordField f ty') :: lr)
        | Syntax.AcArrayIndex ai =>
            let* ai' := typecheck_atom be gx lx ai in
            let* ty' := typecheck_array_get arch ty (typof_atom ai') in
            let* (r, lr) := typecheck_access be gx lx ty' acs' in
            ret (r, (AcArrayIndex ai' ty') :: lr)
        end
    end.

  Definition typecheck_comp (be: benv) (gx: gcontext) (lx: lcontext) (c: Syntax.comp) : res Imp1Typed.comp :=
    match c with
    | Syntax.CpAtom a =>
        let* a' := typecheck_atom be gx lx a in
        ret (CpAtom a' (typof_atom a'))
    | Syntax.CpArrayGet a1 a2 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* ty := typecheck_array_get arch ty1 ty2 in
        ret (CpArrayGet a1' a2' ty)
    | Syntax.CpArraySet a1 a2 a3 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let* a3' := typecheck_atom be gx lx a3 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let ty3 := typof_atom a3' in
        let* ty := typecheck_array_set arch ty1 ty2 ty3 in
        ret (CpArraySet a1' a2' a3' ty)
    | Syntax.CpRecordProj a x =>
        let* a' := typecheck_atom be gx lx a in
        let tya := typof_atom a' in
        let* ty := typecheck_record_proj be tya x in
        ret (CpRecordProj a' x ty)
    | Syntax.CpRecordUpdate a1 x a2 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* ty := typecheck_record_update be ty1 ty2 x in
        ret (CpRecordUpdate a1' x a2' ty)
    | Syntax.CpDeepAccess a acs =>
        let* a' := typecheck_atom be gx lx a in
        let* (t, acs') := typecheck_access be gx lx (typof_atom a') acs in
        ret (CpDeepAccess a' acs' t)
    | Syntax.CpCall a args =>
        let* a' := typecheck_atom be gx lx a in
        let tya := typof_atom a' in
        let* args' := mmap (typecheck_atom be gx lx) args in
        let targs := map typof_atom args' in
        let* ty := typecheck_call tya targs in
        ret (CpCall a' args' ty)
    end.

  (* Should be checked if the context contains the same set of set variables. ? *)
  Definition merge_contexts (lx1 lx2: lcontext) : res lcontext :=
    STree.fold
      (fun acc k v =>
        let* acc := acc in
        lcontext_update acc k v)
      lx2
      (ret lx1).

  Fixpoint typecheck_statement (be: benv) (gx: gcontext) (lx: lcontext) (tret: btyp) (s: Imp1.statement) : res (Imp1Typed.statement * lcontext) :=
    let fix typecheck_match_rec (be: benv) (gx: gcontext) (lx: lcontext) (te: btyp) (tret: btyp) (elems: list ident) (unmatched: list ident)
      (cases: list (pattern * Imp1.statement)) : res (list (pattern * Imp1Typed.statement) * lcontext) :=
      match cases with
      | nil => fail
      | (x, sx) :: nil =>
          let* unmatched' := typecheck_pattern be te elems x unmatched in
          if list_is_empty unmatched' then
            let* (sx', lx') := typecheck_statement be gx lx tret sx in
            ret (((x, sx') :: nil), lx')
          else
            failwith "Imp1.Typing.typecheck_match_rec: non-exhaustive pattern-matching"
      | (x, sx) :: ((_ :: _) as cases') =>
          let* unmatched' := typecheck_pattern be te elems x unmatched in
          let* (sx', lx') := typecheck_statement be gx lx tret sx in
          let* (cases_typed, lxr) := typecheck_match_rec be gx lx te tret elems unmatched' cases' in
          let* lxm := merge_contexts lx' lxr in
          ret (((x, sx') :: cases_typed), lxm)
      end
    in
    let typecheck_match (be: benv) (gx: gcontext) (lx: lcontext) (tret: btyp) (ty: btyp)
      (cases: list (pattern * Imp1.statement)) : res (list (pattern * Imp1Typed.statement) * lcontext) :=
      match ty with
      | BEnum te =>
          let* elems := benv_get_edef be te in
          typecheck_match_rec be gx lx ty tret elems elems cases
      | _ => failwith "Imp1.Typing.typecheck_match: enum type expected"
      end
    in
    match s with
    | Imp1.StSet x c =>
        let* c' := typecheck_comp be gx lx c in
        let* lx' := lcontext_update lx x (typof_comp c') in
        ret (StSet x c', lx')
    | Imp1.StIfThenElse a s1 s2 =>
        let* (s1', lx1) := typecheck_statement be gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement be gx lx tret s2 in
        let* a' := typecheck_atom be gx lx a in
        match typof_atom a' with
        | BBool =>
            let* lx' := merge_contexts lx1 lx2 in
            ret (StIfThenElse a' s1' s2', lx')
        | _ => failwith "Imp1.Typing.typecheck_statement: atom of type bool expected"
        end
    | Imp1.StSwitch a cases =>
        let* a' := typecheck_atom be gx lx a in
        let* (cases_typed, lx') := typecheck_match be gx lx tret (typof_atom a') cases in
        ret (StSwitch a' cases_typed, lx')
    | Imp1.StSequence s1 s2 =>
        let* (s1', lx1) := typecheck_statement be gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement be gx lx1 tret s2 in
        ret (StSequence s1' s2', lx2)
    | Imp1.StReturn a =>
        let* a' := typecheck_atom be gx lx a in
        let ty := typof_atom a' in
        if btyp_eq_dec ty tret then
          ret (StReturn a', lx)
        else
          failwith "Imp1.Typing.typecheck_statement: return type mismatch"
    end.

  Definition typecheck_function (be: benv) (gx: gcontext) (f: Imp1.function) : res Imp1Typed.function :=
    let* lx :=
      list_fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        (fn_params f)
        (ret STree.empty)
    in
    let* (body, _) := typecheck_statement be gx lx (fn_return f) (fn_body f) in
    ret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}.
  
  Fixpoint typecheck_globdefs_rec (be: benv) (gx: gcontext) (defs: list Imp1.globdef) : res (list Imp1Typed.globdef) :=
    match defs with
    | nil => ret nil
    | d :: defs' =>
        match d with
        | DefConst x l ty =>
            let* l' := typecheck_literal be l in
            if btyp_eq_dec ty (typof_literal l') then
              let* gx := gcontext_update gx x ty in
              let* rd := typecheck_globdefs_rec be gx defs' in
              ret (DefConst x l' ty :: rd)
            else
              failwith "Imp1.Typing.typecheck_globdefs: type mismatch in constant definition"
        | DefFun x f =>
            let* f' := typecheck_function be gx f in
            let* gx := gcontext_update gx x (mk_fun_btyp (fn_params f') (fn_return f')) in
            let* rd := typecheck_globdefs_rec be gx defs' in
            ret (DefFun x f' :: rd)
        | DeclConst x ty =>
            let* gx := gcontext_update gx x ty in
            let* rd := typecheck_globdefs_rec be gx defs' in
            ret (DeclConst x ty :: rd)
        | DeclFun x tparams tret =>
            let* gx := gcontext_update gx x (mk_fun_btyp tparams tret) in
            let* rd := typecheck_globdefs_rec be gx defs' in
            ret (DeclFun x tparams tret :: rd)
        end
    end.

  Definition typecheck_globdefs (be: benv) (defs: list Imp1.globdef) : res (list Imp1Typed.globdef) :=
    typecheck_globdefs_rec be STree.empty defs.

  Definition build_benv (types: list type_def) : res benv :=
    Utils.list_fold_left_err
      (fun acc_be td =>
        match td with
        | TdEnum ed =>
            let* be' := benv_update_defs acc_be (ed_name ed) (Adt_enum (ed_elems ed)) in
            let* be' :=
              list_fold_left_err
                (fun acc_be1 e => benv_update_constr_types acc_be1 e (ed_name ed))
                (ed_elems ed)
                (ret be')
            in
            ret be'
        | TdRecord rd =>
            let* be' := benv_update_defs acc_be (rd_name rd) (Adt_record (rd_fields rd)) in
            ret be'
        | TdAbstract _ _ => ret acc_be
        end)
      types
      (ret benv_empty).

  Definition typecheck_program (prog: Imp1.program) : res Imp1Typed.program :=
    let* be := build_benv (prog_types prog) in
    let* defs := typecheck_globdefs be (prog_defs prog) in
    ret {|
      prog_defs := defs;
      prog_types := prog_types prog;
    |}.

  End ARCHI.

End Typing.

Module Imp1Typing := Imp1.Typing.