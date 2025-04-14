From Coq Require Import List String.
From BarocqComp Require Import Error MapList Common Types Syntax Array.
Import ListNotations.
Import Syntax.Typed.

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

Definition typecheck_unary_op (op: unary_op) (ty: ctyp) : res ctyp :=
  match op, ty with
  | UopNotbool, CBool
  | UopNotint, CInt32 _
  | UopNotint, CInt64 _
  | UopNeg, CInt32 _
  | UopNeg, CInt64 _ => ret ty
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
          if signedness_eq s1 s2 then ret CBool
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
          if signedness_eq s1 s2 then ret CBool
          else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
        failwith "Typing.typecheck_binary_op: type mismatch"
      end
  | _ =>
      match ty1, ty2 with
      | CInt32 s1, CInt32 s2
      | CInt64 s1, CInt64 s2 =>
          if signedness_eq s1 s2 then ret ty1
          else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
        failwith "Typing.typecheck_binary_op: type mismatch"
      end
  end.

Definition typecheck_array_get (ty1 ty2: ctyp) : res ctyp :=
  match ty1 with
  | CArray ta =>
      match ty2 with
      | CInt32 Unsigned => ret ta
      | _ => failwith "Typing.typecheck_array_get: u32 expected for array indexes"
      end
  | _ => failwith "Typing.typecheck_array_get: array typed expected"
  end.

Definition typecheck_array_set (ty1 ty2 ty3: ctyp) : res ctyp :=
  match ty1 with
  | CArray ta =>
      match ty2 with
      | CInt32 Unsigned =>
          if ctyp_eq_dec ta ty3 then ret ty1
          else failwith "Typing.typecheck_array_set: type mismatch"
      | _ => failwith "Typing.typecheck_array_set: u32 type expected for array indexes"
      end
  | _ => failwith "Typing.typecheck_array_set: array type expected"
  end.

Definition typecheck_struct_proj (ts: types) (ty: ctyp) (x: ident) : res ctyp :=
  match ty with
  | CStruct t =>
      let/catch fields := types_get ts t
        /> "Typing.typecheck_struct_proj: unknown struct type"
      in
      ctypof_field x fields
  | _ => failwith "Typing.typecheck_struct_proj: struct type expected"
  end.

Definition typecheck_struct_update (ts: types) (ty1 ty2: ctyp) (x: ident) : res ctyp :=
  match ty1 with
  | CStruct t =>
      let/catch fields := types_get ts t
        /> "Typing.typecheck_struct_proj: unknown struct type"
      in
      let* tx := ctypof_field x fields in
      if ctyp_eq_dec tx ty2 then ret ty1
      else failwith "Typing.typecheck_struct_update: type mismatch"
  | _ => failwith "Typing.typecheck_struct_update: struct type expected"
  end.

  Inductive access_ctyp : Type :=
    | ActypStructField : ident -> access_ctyp
    | ActypArrayIndex : ctyp -> access_ctyp.

  Fixpoint typecheck_access (ts: types) (gx: gcontext) (lx: lcontext) (ty: ctyp) (acs: list access_ctyp) : res (ctyp * list ctyp) := 
    match acs with
    | nil => ret (ty, nil)
    | ac :: acs' =>
        match ac with
        | ActypStructField f =>
            let* ty' := typecheck_struct_proj ts ty f in
            let* (r, lr) := typecheck_access ts gx lx ty' acs' in
            ret (r, ty' :: lr)
        | ActypArrayIndex ta =>
            let* ty' := typecheck_array_get ty ta in
            let* (r, lr) := typecheck_access ts gx lx ty' acs' in
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
      if eq_dec_bool ctyp_eq_dec (typof_literal l) t then ret t
      else failwith "Typing.typecheck_array_lit: type mismatch"
  end.

Fixpoint typecheck_struct_lit (l1: list (ident * literal)) (l2: list (ident * ctyp)) : bool :=
  match l1, l2 with
  | nil, nil => true
  | (x1, l1) :: l1', (x2, tx2) :: l2' =>
      let tx1 := typof_literal l1 in
      (eq_dec_bool ctyp_eq_dec tx1 tx2) && typecheck_struct_lit l1' l2'
  | _, _ => false
  end.

Fixpoint typecheck_literal (ts: types) (l: Syntax.literal) : res literal :=
  match l with
  | Syntax.LTrue => ret (LTrue CBool)
  | Syntax.LFalse => ret (LFalse CBool)
  | Syntax.LInt32 i s => ret (LInt32 i (CInt32 s))
  | Syntax.LInt64 i s => ret (LInt64 i (CInt64 s))
  | Syntax.LArray a =>
      let* a' := mmap (typecheck_literal ts) a in
      let* t := typecheck_array_lit a' in
      ret (LArray a' (CArray t))
  | Syntax.LStruct st x =>
      let* st' := map_k_err (typecheck_literal ts) st in
      let* t := types_get ts x in
      if typecheck_struct_lit st' t then ret (LStruct st' (CStruct x))
      else failwith "Typing.typecheck_literal: struct type mismatch"
  end.