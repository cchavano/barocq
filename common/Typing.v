From Coq Require Import List String.
From BarocqComp Require Import Error MapList Utils Types Syntax Array.
Import ListNotations.
Import Syntax.Typed.

(** * Environments for types *)

(** ** Struct name to concrete struct fields *)

Definition senv : Type := ptree (list (ident * ctyp)).

Definition senv_get (se: senv) (x: ident) : res (list (ident * ctyp)) :=
  err_of_opt (tget se x).

Definition senv_update (se: senv) (x: ident) (fields: list (ident * ctyp)) : res senv :=
  match senv_get se x with
  | OK _ => fail
  | Error _ => ret (tset se x fields)
  end.
 
(** ** Struct name to plain struct fields *)

Definition tenv : Type := ptree (list (ident * typ)).

Definition tenv_get (te: tenv) (x: ident) : res (list (ident * typ)) := err_of_opt (tget te x).

(** ** Conversion of concrete types to plain types *)

Definition tenv_update (te: tenv) (x: ident) (fields: list (ident * typ)) : res tenv :=
  match tenv_get te x with
  | OK _ => fail
  | Error _ => ret (tset te x fields)
  end.

Fixpoint ctyp_to_typ (te: tenv) (ty: ctyp) : res typ :=
  match ty with
  | CBool => ret TBool
  | CInt32 s => ret (TInt32 s)
  | CInt64 s => ret (TInt64 s)
  | CArray ta =>
      let* ta' := ctyp_to_typ te ta in 
      ret (TArray ta')
  | CStruct tx =>
      let* fields := tenv_get te tx in
      ret (TStruct tx fields)
  | CFun tparams tret =>
      let* tparams' := mmap (ctyp_to_typ te) tparams in
      let* tret' := ctyp_to_typ te tret in
      ret (TFun tparams' tret')
  end.

Definition typof_literal (l: literal) : ctyp :=
  match l with
  | LTrue ty => ty
  | LFalse ty => ty
  | LInt32 _ ty => ty
  | LInt64 _ ty => ty
  | LArray _ ty => ty
  | LStruct _ ty => ty
  end.

Definition typof_atom (a: atom) : ctyp :=
  match a with
  | ATrue ty
  | AFalse ty
  | AInt32 _ ty
  | AInt64 _ ty
  | AVar _ ty
  | ACast _ ty
  | AUnaryOp _ _ ty
  | ABinaryOp _ _ _ ty => ty
  end.

Definition typof_comp (c: comp) : ctyp :=
  match c with
  | CpAtom _ ty
  | CpArrayGet _ _ ty
  | CpArraySet _ _ _ ty
  | CpStructProj _ _ ty
  | CpStructUpdate _ _ _ ty
  | CpDeepAccess _ _ ty
  | CpCall _ _ ty => ty
  end.

Definition gcontext : Type := ptree ctyp.

Definition lcontext : Type := ptree ctyp.

Definition gcontext_get (gx: gcontext) (x: ident) : res ctyp :=
  match tget gx x with
  | Some t => ret t
  | None => failwith "Typing.gcontext_get: unknown identifier"
  end.

Definition gcontext_update (gx: gcontext) (x: ident) (ty: ctyp) : res gcontext :=
  match gcontext_get gx x with
  | OK _ => failwith "Typing.gcontext_update: global symbol already defined"
  | Error _ => ret (tset gx x ty)
  end.

Definition lcontext_get (lx: lcontext) (x: ident) : res ctyp :=
  match tget lx x with
  | Some t => ret t
  | None => failwith "Typing.lcontext_get: unknown identifier"
  end.

Definition lcontext_update (lx: lcontext) (x: ident) (ty: ctyp) : res lcontext :=
  match lcontext_get lx x with
  | OK t =>
      if ctyp_eq_dec ty t then ret (tset lx x ty)
      else
        failwith "Typing.lcontext_update: variable shadowing with a different type"
  | Error _ => ret (tset lx x ty)
  end.

Definition typof_var (gx: gcontext) (lx: lcontext) (x: ident) : res ctyp :=
  match (lcontext_get lx x) with
  | OK ty => ret ty
  | Error _ =>
      let/catch t := gcontext_get gx x /> "Typing.typof_var: unknown variable" in
      ret t
  end.

Definition typecheck_cast (from: ctyp) (to: ctyp) : res ctyp :=
  match from with
  | CBool | CInt32 _ | CInt64 _ =>
    match to with
    | CBool | CInt32 _ | CInt64 _ => ret to
    | _ => fail
    end
  | _ => fail
  end.

Definition typecheck_unary_op (op: unary_op) (ty: ctyp) : res ctyp :=
  match op, ty with
  | UopNotbool, CBool
  | UopNotint, CInt32 _
  | UopNotint, CInt64 _
  | UopNeg, CInt32 _
  | UopNeg, CInt64 _
  | UopPlus, CInt32 _
  | UopPlus, CInt64 _ => ret ty
  | _, _ => failwith "Typing.typecheck_unary_op: type mismatch"
  end.

Definition typecheck_binary_op (op: binary_op) (ty1 ty2: ctyp) : res ctyp :=
  match op with
  | BopAndbool
  | BopOrbool
  | BopXorbool =>
      match ty1, ty2 with
      | CBool, CBool => ret ty1
      | _, _ => failwith "Typing.typecheck_binary_op: type mismatch"
      end
  | BopEq
  | BopNeq =>
      match ty1, ty2 with
      | CBool, CBool => ret ty1
      | CInt32 s1, CInt32 s2
      | CInt64 s1, CInt64 s2 =>
          if signedness_eq_dec s1 s2 then ret CBool
          else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
          failwith "Typing.typecheck_binary_op: type mismatch"
      end
  | BopLt
  | BopLe 
  | BopGt
  | BopGe =>
      match ty1, ty2 with
      | CInt32 s1, CInt32 s2
      | CInt64 s1, CInt64 s2 =>
          if signedness_eq_dec s1 s2 then ret CBool
          else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
        failwith "Typing.typecheck_binary_op: type mismatch"
      end
  | _ =>
      match ty1, ty2 with
      | CInt32 s1, CInt32 s2
      | CInt64 s1, CInt64 s2 =>
          if signedness_eq_dec s1 s2 then ret ty1
          else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
        failwith "Typing.typecheck_binary_op: type mismatch"
      end
  end.

Definition typecheck_array_get (ty1 ty2: ctyp) : res ctyp :=    
  match ty1 with
  | CArray ta =>
      if ctyp_eq_dec ty2 arr_index_ctyp then ret ta
      else failwith "Typing.typecheck_array_get: array index type mismatch"
  | _ => failwith "Typing.typecheck_array_get: array typed expected"
  end.

Definition typecheck_array_set (ty1 ty2 ty3: ctyp) : res ctyp :=
  match ty1 with
  | CArray ta =>
      if ctyp_eq_dec ty2 arr_index_ctyp then
        if ctyp_eq_dec ta ty3 then ret ty1
        else failwith "Typing.typecheck_array_set: type mismatch"
      else failwith "Typing.typecheck_array_set: array index type mismatch"
  | _ => failwith "Typing.typecheck_array_set: array type expected"
  end.

Definition typecheck_struct_proj (se: senv) (ty: ctyp) (x: ident) : res ctyp :=
  match ty with
  | CStruct t =>
      let/catch fields := senv_get se t
        /> "Typing.typecheck_struct_proj: unknown struct type"
      in
      ctypof_field x fields
  | _ => failwith "Typing.typecheck_struct_proj: struct type expected"
  end.

Definition typecheck_struct_update (se: senv) (ty1 ty2: ctyp) (x: ident) : res ctyp :=
  match ty1 with
  | CStruct t =>
      let/catch fields := senv_get se t
        /> "Typing.typecheck_struct_proj: unknown struct type"
      in
      let* tx := ctypof_field x fields in
      if ctyp_eq_dec tx ty2 then ret ty1
      else failwith "Typing.typecheck_struct_update: type mismatch"
  | _ => failwith "Typing.typecheck_struct_update: struct type expected"
  end.

  Inductive access_ctyp : Type :=
    | ActypAcStructField : ident -> access_ctyp
    | ActypAcArrayIndex : ctyp -> access_ctyp.

  Fixpoint typecheck_access (se: senv) (gx: gcontext) (lx: lcontext) (ty: ctyp) (acs: list access_ctyp) : res (ctyp * list ctyp) := 
    match acs with
    | nil => ret (ty, nil)
    | ac :: acs' =>
        match ac with
        | ActypAcStructField f =>
            let* ty' := typecheck_struct_proj se ty f in
            let* (r, lr) := typecheck_access se gx lx ty' acs' in
            ret (r, ty' :: lr)
        | ActypAcArrayIndex ta =>
            let* ty' := typecheck_array_get ty ta in
            let* (r, lr) := typecheck_access se gx lx ty' acs' in
            ret (r, ty' :: lr)
        end
    end.

Fixpoint typecheck_call_rec (tparams targs: list ctyp) (tret: ctyp) : res ctyp :=
  match tparams, targs with
  | nil, nil => ret tret
  | tp1 :: tparams', ta1 :: targs' =>
      if ctyp_eq_dec tp1 ta1 then
        typecheck_call_rec tparams' targs' tret
      else 
        failwith "Typing.typecheck_call_rec: type mismatch"
  | _, _ =>
      failwith "Typing.typecheck_call_rec: wrong number of arguments"
  end.

Definition typecheck_call (ty: ctyp) (targs: list ctyp) : res ctyp :=
  match ty with
  | CFun tparams tret => typecheck_call_rec tparams targs tret
  | _ => failwith "Typing.typecheck_call: function type expected"
  end.

Fixpoint typecheck_array_lit (a: array literal) : res ctyp :=
  match a with
  | nil => failwith "Typing.typecheck_array_lit: empty array"
  | l :: nil => ret (typof_literal l)
  | l :: a' =>
      let* t := typecheck_array_lit a' in
      if ctyp_eq_dec (typof_literal l) t then ret t
      else failwith "Typing.typecheck_array_lit: type mismatch"
  end.

Fixpoint typecheck_struct_lit (l1: list (ident * literal)) (l2: list (ident * ctyp)) : bool :=
  match l1, l2 with
  | nil, nil => true
  | (x1, l1) :: l1', (x2, tx2) :: l2' =>
      let tx1 := typof_literal l1 in
      if ctyp_eq_dec tx1 tx2 then typecheck_struct_lit l1' l2'
      else false
  | _, _ => false
  end.

Fixpoint typecheck_literal (se: senv) (l: Syntax.literal) : res literal :=
  match l with
  | Syntax.LTrue => ret (LTrue CBool)
  | Syntax.LFalse => ret (LFalse CBool)
  | Syntax.LInt32 i s => ret (LInt32 i (CInt32 s))
  | Syntax.LInt64 i s => ret (LInt64 i (CInt64 s))
  | Syntax.LArray a =>
      let* a' := mmap (typecheck_literal se) a in
      let* t := typecheck_array_lit a' in
      ret (LArray a' (CArray t))
  | Syntax.LStruct st x =>
      let* st' := map_k_err (typecheck_literal se) st in
      let* t := senv_get se x in
      if typecheck_struct_lit st' t then ret (LStruct st' (CStruct x))
      else failwith "Typing.typecheck_literal: struct type mismatch"
  end.