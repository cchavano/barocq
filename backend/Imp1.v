From Coq Require Import List String.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Error Utils Syntax Types Typing Array.

(** * Abstract syntax *)

(** ** Literals *)

Definition literal : Type := Syntax.literal.

(** ** Atoms *)

Definition atom : Type := Syntax.atom.

(** ** Statements *)
 
Inductive statement : Type :=
  | StSet : ident -> comp -> statement
  | StIfThenElse : atom -> statement -> statement -> statement
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
    | StIfThenElse : atom -> statement -> statement -> statement
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

  Definition typof_var (gx: gcontext) (lx: lcontext) (x: ident) : res btyp :=
    match lcontext_get lx x with
    | OK ty => eret ty
    | Error _ =>
        match gcontext_get gx x with
        | OK (BArray _)
        | OK (BStruct _) =>
            failwith "Imp1.Typing.typof_var: the use of global structures or arrays is not yet supported"
        | OK ty => eret ty
        | Error e => Error e
        end
    end.

  Fixpoint typecheck_atom (gx: gcontext) (lx: lcontext) (a: Syntax.atom) : res Syntax.Typed.atom :=
    match a with
    | Syntax.ATrue => ret (ATrue BBool)
    | Syntax.AFalse => ret (AFalse BBool)
    | Syntax.AInt32 i s => ret (AInt32 i (BInt32 s))
    | Syntax.AInt64 i s => ret (AInt64 i (BInt64 s))
    | Syntax.AVar x =>
        let* t := typof_var gx lx x in
        ret (AVar x t)
    | Syntax.ACast a1 ty =>
        let* a1' := typecheck_atom gx lx a1 in
        let* t := typecheck_cast (typof_atom a1') ty in
        ret (ACast a1' t)
    | Syntax.AUnaryOp op a1 =>
        let* a1' := typecheck_atom gx lx a1 in
        let ty1 := typof_atom a1' in
        let* t := typecheck_unary_op op ty1 in
        ret (AUnaryOp op a1' t)
    | Syntax.ABinaryOp op a1 a2 =>
        let* a1' := typecheck_atom gx lx a1 in
        let* a2' := typecheck_atom gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* t := typecheck_binary_op op ty1 ty2 in
        ret (ABinaryOp op a1' a2' t)
    end.

  Fixpoint typecheck_access (se: senv) (gx: gcontext) (lx: lcontext) (ty: btyp) (acs: list Syntax.access) : res (btyp * list Syntax.Typed.access) :=
    match acs with
    | nil => ret (ty, nil)
    | ac :: acs' =>
        match ac with
        | Syntax.AcStructField f =>
            let* ty' := typecheck_struct_proj se ty f in
            let* (r, lr) := typecheck_access se gx lx ty' acs' in
            ret (r, (AcStructField f ty') :: lr)
        | Syntax.AcArrayIndex ai =>
            let* ai' := typecheck_atom gx lx ai in
            let* ty' := typecheck_array_get ty (typof_atom ai') in
            let* (r, lr) := typecheck_access se gx lx ty' acs' in
            ret (r, (AcArrayIndex ai' ty') :: lr)
        end
    end.

  Definition typecheck_comp (se: senv) (gx: gcontext) (lx: lcontext) (c: Syntax.comp) : res Imp1Typed.comp :=
    match c with
    | Syntax.CpAtom a =>
        let* a' := typecheck_atom gx lx a in
        ret (CpAtom a' (typof_atom a'))
    | Syntax.CpArrayGet a1 a2 =>
        let* a1' := typecheck_atom gx lx a1 in
        let* a2' := typecheck_atom gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* ty := typecheck_array_get ty1 ty2 in
        ret (CpArrayGet a1' a2' ty)
    | Syntax.CpArraySet a1 a2 a3 =>
        let* a1' := typecheck_atom gx lx a1 in
        let* a2' := typecheck_atom gx lx a2 in
        let* a3' := typecheck_atom gx lx a3 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let ty3 := typof_atom a3' in
        let* ty := typecheck_array_set ty1 ty2 ty3 in
        ret (CpArraySet a1' a2' a3' ty)
    | Syntax.CpStructProj a x =>
        let* a' := typecheck_atom gx lx a in
        let tya := typof_atom a' in
        let* ty := typecheck_struct_proj se tya x in
        ret (CpStructProj a' x ty)
    | Syntax.CpStructUpdate a1 x a2 =>
        let* a1' := typecheck_atom gx lx a1 in
        let* a2' := typecheck_atom gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* ty := typecheck_struct_update se ty1 ty2 x in
        ret (CpStructUpdate a1' x a2' ty)
    | Syntax.CpDeepAccess a acs =>
        let* a' := typecheck_atom gx lx a in
        let* (t, acs') := typecheck_access se gx lx (typof_atom a') acs in
        ret (CpDeepAccess a' acs' t)
    | Syntax.CpCall a args =>
        let* a' := typecheck_atom gx lx a in
        let tya := typof_atom a' in
        let* args' := mmap (typecheck_atom gx lx) args in
        let targs := map typof_atom args' in
        let* ty := typecheck_call tya targs in
        ret (CpCall a' args' ty)
    end.

  (* Should be checked if the context contains the same set of set variables. ?*)
  Definition merge_context (lx1 lx2: lcontext) : res lcontext :=
    PTree.fold
      (fun acc k v =>
        let* acc := acc in
        lcontext_update acc k v)
      lx2
      (ret lx1).

  Fixpoint typecheck_statement (se: senv) (gx: gcontext) (lx: lcontext) (tret: btyp) (s: Imp1.statement) : res (Imp1Typed.statement * lcontext) := 
    match s with
    | Imp1.StSet x c =>
        let* c' := typecheck_comp se gx lx c in
        let* lx' := lcontext_update lx x (typof_comp c') in
        ret (StSet x c', lx')
    | Imp1.StIfThenElse a s1 s2 =>
        let* (s1', lx1) := typecheck_statement se gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement se gx lx tret s2 in
        let* a' := typecheck_atom gx lx a in
        match typof_atom a' with
        | BBool =>
            let* lx' := merge_context lx1 lx2 in
            ret (StIfThenElse a' s1' s2', lx')
        | _ => failwith "Imp1.Typing.typecheck_statement: atom of type bool expected"
        end
    | Imp1.StSequence s1 s2 =>
        let* (s1', lx1) := typecheck_statement se gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement se gx lx1 tret s2 in
        ret (StSequence s1' s2', lx2)
    | Imp1.StReturn a =>
        let* a' := typecheck_atom gx lx a in
        let ty := typof_atom a' in
        if btyp_eq_dec ty tret then
          ret (StReturn a', lx)
        else
          failwith "Imp1.Typing.typecheck_statement: return type mismatch"
    end.

  Definition typecheck_function (se: senv) (gx: gcontext) (f: Imp1.function) : res Imp1Typed.function :=
    let* lx :=
      fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        (fn_params f)
        (ret tempty)
    in
    let* (body, _) := typecheck_statement se gx lx (fn_return f) (fn_body f) in
    ret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}.
  
  Fixpoint typecheck_globdefs_rec (se: senv) (gx: gcontext) (defs: list Imp1.globdef) : res (list Imp1Typed.globdef) :=
    match defs with
    | nil => ret nil
    | d :: defs' =>
        match d with
        | DefConst x l ty =>
            let* l' := typecheck_literal se l in
            if btyp_eq_dec ty (typof_literal l') then
              let* gx := gcontext_update gx x ty in
              let* rd := typecheck_globdefs_rec se gx defs' in
              ret (DefConst x l' ty :: rd)
            else
              failwith "Imp1.Typing.typecheck_globdefs: type mismatch in constant definition"
        | DefFun x f =>
            let* f' := typecheck_function se gx f in
            let* gx := gcontext_update gx x (mk_fun_btyp (fn_params f') (fn_return f')) in
            let* rd := typecheck_globdefs_rec se gx defs' in
            ret (DefFun x f' :: rd)
        | DeclConst x ty =>
            let* gx := gcontext_update gx x ty in
            let* rd := typecheck_globdefs_rec se gx defs' in
            ret (DeclConst x ty :: rd)
        | DeclFun x tparams tret =>
            let* gx := gcontext_update gx x (mk_fun_btyp tparams tret) in
            let* rd := typecheck_globdefs_rec se gx defs' in
            ret (DeclFun x tparams tret :: rd)
        end
    end.

  Definition typecheck_globdefs (se: senv) (defs: list Imp1.globdef) : res (list Imp1Typed.globdef) :=
    typecheck_globdefs_rec se tempty defs.

  Definition typecheck_program (prog: Imp1.program) : res Imp1Typed.program :=
    let* se :=
      Utils.fold_left_err
        (fun acc td =>
          match td with
          | TdStruct st => senv_update acc (sd_name st) (sd_fields st)
          | TdAbstract _ _ => ret acc
          end)
        (prog_types prog)
        (eret tempty)
    in
    let* defs := typecheck_globdefs se (prog_defs prog) in
    ret {|
      prog_defs := defs;
      prog_types := prog_types prog;
    |}.

End Typing.

Module Imp1Typing := Imp1.Typing.