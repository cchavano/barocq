From Coq Require Import List String.
From BarocqComp Require Import Error MapList Utils Types Syntax Barray.
Import ListNotations.
Import Syntax.Typed.

(** * Environments for types *)

(** ** Record name to concrete record fields *)

Definition renv : Type := ptree (list (ident * btyp)).

Definition renv_get (re: renv) (x: ident) : res (list (ident * btyp)) :=
  err_of_opt (tget re x).

Definition renv_update (re: renv) (x: ident) (fields: list (ident * btyp)) : res renv :=
  match renv_get re x with
  | OK _ => fail
  | Error _ => ret (tset re x fields)
  end.
 
(** ** Record name to plain record fields *)

Definition tenv : Type := ptree (list (ident * typ)).

Definition tenv_get (te: tenv) (x: ident) : res (list (ident * typ)) := err_of_opt (tget te x).

(** ** Conversion of concrete types to plain types *)

Definition tenv_update (te: tenv) (x: ident) (fields: list (ident * typ)) : res tenv :=
  match tenv_get te x with
  | OK _ => fail
  | Error _ => ret (tset te x fields)
  end.

Fixpoint btyp_to_typ (te: tenv) (ty: btyp) : res typ :=
  match ty with
  | BBool => ret TBool
  | BInt32 s => ret (TInt32 s)
  | BInt64 s => ret (TInt64 s)
  | BArray ta =>
      let* ta' := btyp_to_typ te ta in 
      ret (TArray ta')
  | BRecord tx =>
      let* fields := tenv_get te tx in
      ret (TRecord tx fields)
  | BFun tparams tret =>
      let* tparams' := mmap (btyp_to_typ te) tparams in
      let* tret' := btyp_to_typ te tret in
      ret (TFun tparams' tret')
  | BAbs t => ret (TAbs t)
  end.

Definition typof_literal (l: literal) : btyp :=
  match l with
  | LTrue ty => ty
  | LFalse ty => ty
  | LInt32 _ ty => ty
  | LInt64 _ ty => ty
  | LArray _ ty => ty
  | LRecord _ ty => ty
  end.

Definition typof_atom (a: atom) : btyp :=
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

Definition typof_comp (c: comp) : btyp :=
  match c with
  | CpAtom _ ty
  | CpArrayGet _ _ ty
  | CpArraySet _ _ _ ty
  | CpRecordProj _ _ ty
  | CpRecordUpdate _ _ _ ty
  | CpDeepAccess _ _ ty
  | CpCall _ _ ty => ty
  end.

Definition gcontext : Type := ptree btyp.

Definition lcontext : Type := ptree btyp.

Definition gcontext_get (gx: gcontext) (x: ident) : res btyp :=
  match tget gx x with
  | Some t => ret t
  | None => failwith "Typing.gcontext_get: unknown identifier"
  end.

Definition gcontext_update (gx: gcontext) (x: ident) (ty: btyp) : res gcontext :=
  match gcontext_get gx x with
  | OK _ => failwith "Typing.gcontext_update: global symbol already defined"
  | Error _ => ret (tset gx x ty)
  end.

Definition lcontext_get (lx: lcontext) (x: ident) : res btyp :=
  match tget lx x with
  | Some t => ret t
  | None => failwith "Typing.lcontext_get: unknown identifier"
  end.

Definition lcontext_update (lx: lcontext) (x: ident) (ty: btyp) : res lcontext :=
  match lcontext_get lx x with
  | OK t =>
      if btyp_eq_dec ty t then ret (tset lx x ty)
      else
        failwith "Typing.lcontext_update: variable shadowing with a different type"
  | Error _ => ret (tset lx x ty)
  end.

Definition typof_var (gx: gcontext) (lx: lcontext) (x: ident) : res btyp :=
  match (lcontext_get lx x) with
  | OK ty => ret ty
  | Error _ =>
      let/catch t := gcontext_get gx x /> "Typing.typof_var: unknown variable" in
      ret t
  end.

Definition typecheck_cast (from: btyp) (to: btyp) : res btyp :=
  match from with
  | BBool | BInt32 _ | BInt64 _ =>
    match to with
    | BBool | BInt32 _ | BInt64 _ => ret to
    | _ => fail
    end
  | _ => fail
  end.

Definition typecheck_unary_op (op: unary_op) (ty: btyp) : res btyp :=
  match op, ty with
  | UopNotbool, BBool
  | UopNotint, BInt32 _
  | UopNotint, BInt64 _
  | UopNeg, BInt32 _
  | UopNeg, BInt64 _
  | UopPlus, BInt32 _
  | UopPlus, BInt64 _ => ret ty
  | _, _ => failwith "Typing.typecheck_unary_op: type mismatch"
  end.

Definition typecheck_binary_op (op: binary_op) (ty1 ty2: btyp) : res btyp :=
  match op with
  | BopAndbool
  | BopOrbool
  | BopXorbool =>
      match ty1, ty2 with
      | BBool, BBool => ret ty1
      | _, _ => failwith "Typing.typecheck_binary_op: type mismatch"
      end
  | BopEq
  | BopNeq =>
      match ty1, ty2 with
      | BBool, BBool => ret ty1
      | BInt32 s1, BInt32 s2
      | BInt64 s1, BInt64 s2 =>
          if signedness_eq_dec s1 s2 then ret BBool
          else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
          failwith "Typing.typecheck_binary_op: type mismatch"
      end
  | BopLt
  | BopLe 
  | BopGt
  | BopGe =>
      match ty1, ty2 with
      | BInt32 s1, BInt32 s2
      | BInt64 s1, BInt64 s2 =>
          if signedness_eq_dec s1 s2 then ret BBool
          else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
        failwith "Typing.typecheck_binary_op: type mismatch"
      end
  | _ =>
      match ty1, ty2 with
      | BInt32 s1, BInt32 s2
      | BInt64 s1, BInt64 s2 =>
          if signedness_eq_dec s1 s2 then ret ty1
          else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
        failwith "Typing.typecheck_binary_op: type mismatch"
      end
  end.

Definition typecheck_array_get (ty1 ty2: btyp) : res btyp :=    
  match ty1 with
  | BArray ta =>
      if btyp_eq_dec ty2 arr_index_btyp then ret ta
      else failwith "Typing.typecheck_array_get: array index type mismatch"
  | _ => failwith "Typing.typecheck_array_get: array typed expected"
  end.

Definition typecheck_array_set (ty1 ty2 ty3: btyp) : res btyp :=
  match ty1 with
  | BArray ta =>
      if btyp_eq_dec ty2 arr_index_btyp then
        if btyp_eq_dec ta ty3 then ret ty1
        else failwith "Typing.typecheck_array_set: type mismatch"
      else failwith "Typing.typecheck_array_set: array index type mismatch"
  | _ => failwith "Typing.typecheck_array_set: array type expected"
  end.

Definition typecheck_record_proj (re: renv) (ty: btyp) (x: ident) : res btyp :=
  match ty with
  | BRecord t =>
      let/catch fields := renv_get re t
        /> "Typing.typecheck_record_proj: unknown struct type"
      in
      btypof_field x fields
  | _ => failwith "Typing.typecheck_record_proj: struct type expected"
  end.

Definition typecheck_record_update (re: renv) (ty1 ty2: btyp) (x: ident) : res btyp :=
  match ty1 with
  | BRecord t =>
      let/catch fields := renv_get re t
        /> "Typing.typecheck_record_proj: unknown struct type"
      in
      let* tx := btypof_field x fields in
      if btyp_eq_dec tx ty2 then ret ty1
      else failwith "Typing.typecheck_record_update: type mismatch"
  | _ => failwith "Typing.typecheck_record_update: struct type expected"
  end.

  Inductive access_btyp : Type :=
    | AbtypAcRecordField : ident -> access_btyp
    | AbtypAcArrayIndex : btyp -> access_btyp.

  Fixpoint typecheck_access (re: renv) (gx: gcontext) (lx: lcontext) (ty: btyp) (acs: list access_btyp) : res (btyp * list btyp) := 
    match acs with
    | nil => ret (ty, nil)
    | ac :: acs' =>
        match ac with
        | AbtypAcRecordField f =>
            let* ty' := typecheck_record_proj re ty f in
            let* (r, lr) := typecheck_access re gx lx ty' acs' in
            ret (r, ty' :: lr)
        | AbtypAcArrayIndex ta =>
            let* ty' := typecheck_array_get ty ta in
            let* (r, lr) := typecheck_access re gx lx ty' acs' in
            ret (r, ty' :: lr)
        end
    end.

Fixpoint typecheck_call_rec (tparams targs: list btyp) (tret: btyp) : res btyp :=
  match tparams, targs with
  | nil, nil => ret tret
  | tp1 :: tparams', ta1 :: targs' =>
      if btyp_eq_dec tp1 ta1 then
        typecheck_call_rec tparams' targs' tret
      else 
        failwith "Typing.typecheck_call_rec: type mismatch"
  | _, _ =>
      failwith "Typing.typecheck_call_rec: wrong number of arguments"
  end.

Definition typecheck_call (ty: btyp) (targs: list btyp) : res btyp :=
  match ty with
  | BFun tparams tret => typecheck_call_rec tparams targs tret
  | _ => failwith "Typing.typecheck_call: function type expected"
  end.

Fixpoint typecheck_array_lit (a: array literal) : res btyp :=
  match a with
  | nil => failwith "Typing.typecheck_array_lit: empty array"
  | l :: nil => ret (typof_literal l)
  | l :: a' =>
      let* t := typecheck_array_lit a' in
      if btyp_eq_dec (typof_literal l) t then ret t
      else failwith "Typing.typecheck_array_lit: type mismatch"
  end.

Fixpoint typecheck_struct_lit (l1: list (ident * literal)) (l2: list (ident * btyp)) : bool :=
  match l1, l2 with
  | nil, nil => true
  | (x1, l1) :: l1', (x2, tx2) :: l2' =>
      let tx1 := typof_literal l1 in
      if btyp_eq_dec tx1 tx2 then typecheck_struct_lit l1' l2'
      else false
  | _, _ => false
  end.

Fixpoint typecheck_literal (re: renv) (l: Syntax.literal) : res literal :=
  match l with
  | Syntax.LTrue => ret (LTrue BBool)
  | Syntax.LFalse => ret (LFalse BBool)
  | Syntax.LInt32 i s => ret (LInt32 i (BInt32 s))
  | Syntax.LInt64 i s => ret (LInt64 i (BInt64 s))
  | Syntax.LArray a =>
      let* a' := mmap (typecheck_literal re) a in
      let* t := typecheck_array_lit a' in
      ret (LArray a' (BArray t))
  | Syntax.LRecord rc x =>
      let* rc' := map_k_err (typecheck_literal re) rc in
      let* t := renv_get re x in
      if typecheck_struct_lit rc' t then ret (LRecord rc' (BRecord x))
      else failwith "Typing.typecheck_literal: struct type mismatch"
  end.