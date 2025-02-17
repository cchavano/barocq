From Coq Require Import List String.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Error Common Syntax Types Typing Array.

Local Open Scope error_monad_scope.

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

Module Imp1Typed := Imp1.Typed.

Module Typing.

  Import Syntax.Typed.
  Import Imp1Typed.
  Import ListNotations.

  Definition typof_var (gx: gcontext) (lx: lcontext) (x: ident) : res ctyp :=
    match lcontext_get lx x with
    | OK ty => eret ty
    | Error _ =>
        match gcontext_get gx x with
        | OK (CArray _)
        | OK (CStruct _) =>
            failwith "The use of global structures or arrays is not yet supported"
        | OK ty => eret ty
        | Error e => Error e
        end
    end.

  Fixpoint typecheck_atom (gx: gcontext) (lx: lcontext) (a: Syntax.atom) : res Syntax.Typed.atom :=
    match a with
    | Syntax.ATrue => ret (ATrue CBool)
    | Syntax.AFalse => ret (AFalse CBool)
    | Syntax.AInt32 i => ret (AInt32 i CInt32)
    | Syntax.AInt64 i => ret (AInt64 i CInt64)
    | Syntax.AVar x =>
        let* t := typof_var gx lx x in
        ret (AVar x t)
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

  Definition typecheck_comp (ts: types) (gx: gcontext) (lx: lcontext) (c: Syntax.comp) : res Imp1Typed.comp :=
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
        let* ty := typecheck_struct_proj ts tya x in
        ret (CpStructProj a' x ty)
    | Syntax.CpStructUpdate a1 x a2 =>
        let* a1' := typecheck_atom gx lx a1 in
        let* a2' := typecheck_atom gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* ty := typecheck_struct_update ts ty1 ty2 x in
        ret (CpStructUpdate a1' x a2' ty)
    | Syntax.CpCall a args =>
        let* a' := typecheck_atom gx lx a in
        let tya := typof_atom a' in
        let* args' := mmap (typecheck_atom gx lx) args in
        let targs := map typof_atom args' in
        let* ty := typecheck_call tya targs in
        ret (CpCall a' args' ty)
    end.

  Definition merge_context (lx1 lx2: lcontext) : res lcontext :=
    PTree.fold
      (fun acc k v =>
        let* acc := acc in
        lcontext_update acc k v)
      lx2
      (ret lx1).

  Fixpoint typecheck_statement (ts: types) (gx: gcontext) (lx: lcontext) (tret: ctyp) (s: Imp1.statement) : res (Imp1Typed.statement * lcontext) := 
    match s with
    | Imp1.StSet x c =>
        let* c' := typecheck_comp ts gx lx c in
        let* lx' := lcontext_update lx x (typof_comp c') in
        ret (StSet x c', lx')
    | Imp1.StIfThenElse a s1 s2 =>
        let* (s1', lx1) := typecheck_statement ts gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement ts gx lx tret s2 in
        let* a' := typecheck_atom gx lx a in
        match typof_atom a' with
        | CBool =>
            let* lx' := merge_context lx1 lx2 in
            ret (StIfThenElse a' s1' s2', lx')
        | _ => failwith "Imp1.Typing.typecheck_statement: atom of type bool expected"
        end
    | Imp1.StSequence s1 s2 =>
        let* (s1', lx1) := typecheck_statement ts gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement ts gx lx1 tret s2 in
        ret (StSequence s1' s2', lx2)
    | Imp1.StReturn a =>
        let* a' := typecheck_atom gx lx a in
        let ty := typof_atom a' in
        if ctyp_eq_dec ty tret then
          ret (StReturn a', lx)
        else
          failwith "Imp1.Typing.typecheck_statement: return type mismatch"
    end.

  Definition typecheck_function (ts: types) (gx: gcontext) (f: Imp1.function) : res Imp1Typed.function :=
    let* lx :=
      fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        (fn_params f)
        (ret tempty)
    in
    let* (body, _) := typecheck_statement ts gx lx (fn_return f) (fn_body f) in
    ret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}.
  
  Fixpoint typecheck_globdefs_rec (ts: types) (gx: gcontext) (defs: list Imp1.globdef) : res (list Imp1Typed.globdef) :=
    match defs with
    | nil => ret nil
    | DefConst x l ty :: defs' =>
        let* l' := typecheck_literal ts l in
        if ctyp_eq_dec ty (typof_literal l') then
          let* gx := gcontext_update gx x ty in
          let* rd := typecheck_globdefs_rec ts gx defs' in
          ret (DefConst x l' ty :: rd)
        else
          failwith "Imp1.Typing.typecheck_globdefs: type mismatch in constant definition"
    | DefFun x f :: defs' =>
        let* f' := typecheck_function ts gx f in
        let* gx := gcontext_update gx x (cfun_typ (fn_params f') (fn_return f')) in
        let* rd := typecheck_globdefs_rec ts gx defs' in
        ret (DefFun x f' :: rd)
    end.

  Definition typecheck_globdefs (ts: types) (defs: list Imp1.globdef) : res (list Imp1Typed.globdef) :=
    typecheck_globdefs_rec ts tempty defs.

  Definition typecheck_program (prog: Imp1.program) : res Imp1Typed.program :=
    let* defs := typecheck_globdefs (prog_types prog) (prog_defs prog) in
    ret {|
      prog_defs := defs;
      prog_types := prog_types prog
    |}.

End Typing.

Module Imp1Typing := Imp1.Typing.