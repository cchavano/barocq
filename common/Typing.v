From Coq Require Import List String.
From BarocqComp Require Import Error Maps2 Utils Types Syntax Barray Benum.
Import ListNotations.
Import Syntax.Typed.

(** * Environments of types *)

(** ** Identifiers to type definitions + enum constructors to enum identifier *)

Record benv := mk_benv {
  benv_defs : STree.t (adt_definition btyp);
  benv_constr_types : STree.t ident
}.

Definition benv_empty : benv := {|
  benv_defs := STree.empty;
  benv_constr_types := STree.empty
|}.

Definition benv_get_edef (be: benv) (x: ident) : res (list ident) :=
  match STree.get x be.(benv_defs) with
  | Some (Adt_enum elems) => ret elems
  | _ => fail
  end.

Definition benv_get_rdef (be: benv) (x: ident) : res (smaplist btyp) :=
  match STree.get x be.(benv_defs) with
  | Some (Adt_record fields) => ret fields
  | _ => fail
  end.

Definition benv_get_constr_typ (be: benv) (x: ident) : res ident :=
  err_of_opt (STree.get x be.(benv_constr_types)).

Definition benv_update_defs (be: benv) (x: ident) (adt: adt_definition btyp) : res benv :=
  let types := be.(benv_defs) in
  match STree.get x types with
  | Some _ => fail
  | None =>
      ret {|
        benv_defs := STree.set x adt types;
        benv_constr_types := be.(benv_constr_types)
      |}
  end.

Definition benv_update_constr_types (be: benv) (elem: ident) (eid: ident) : res benv :=
  let elems := be.(benv_constr_types) in
  match STree.get elem be.(benv_constr_types) with
  | Some _ => fail
  | None =>
      ret {|
        benv_defs := be.(benv_defs);
        benv_constr_types := STree.set elem eid elems
      |}
  end.

Record tenv := mk_tenv {
  tenv_defs : STree.t (adt_definition typ);
  tenv_constr_types : STree.t ident
}.

Definition tenv_empty : tenv := {|
  tenv_defs := STree.empty;
  tenv_constr_types := STree.empty
|}.

Definition tenv_get_edef (be: tenv) (x: ident) : res (list ident) :=
  match STree.get x be.(tenv_defs) with
  | Some (Adt_enum elems) => ret elems
  | _ => fail
  end.

Definition tenv_get_rdef (be: tenv) (x: ident) : res (smaplist typ) :=
  match STree.get x be.(tenv_defs) with
  | Some (Adt_record fields) => ret fields
  | _ => fail
  end.

Definition tenv_get_constr_typ (be: tenv) (x: ident) : res ident :=
  err_of_opt (STree.get x be.(tenv_constr_types)).

Definition tenv_update_defs (be: tenv) (x: ident) (adt: adt_definition typ) : res tenv :=
  let types := be.(tenv_defs) in
  match STree.get x types with
  | Some _ => fail
  | None =>
      ret {|
        tenv_defs := STree.set x adt types;
        tenv_constr_types := be.(tenv_constr_types)
      |}
  end.

Definition tenv_update_constr_types (be: tenv) (elem: ident) (eid: ident) : res tenv :=
  let elems := be.(tenv_constr_types) in
  match STree.get elem be.(tenv_constr_types) with
  | Some _ => fail
  | None =>
      ret {|
        tenv_defs := be.(tenv_defs);
        tenv_constr_types := STree.set elem eid elems
      |}
  end.

(** ** Conversion of concrete types to plain types *)

Fixpoint btyp_to_typ (te: tenv) (ty: btyp) : res typ :=
  match ty with
  | BBool => ret TBool
  | BInt32 s => ret (TInt32 s)
  | BInt64 s => ret (TInt64 s)
  | BArray ta =>
      let* ta' := btyp_to_typ te ta in 
      ret (TArray ta')
  | BEnum tn =>
      let* elems := tenv_get_edef te tn in
      ret (TEnum tn elems) 
  | BRecord tr =>
      let* fields := tenv_get_rdef te tr in
      ret (TRecord tr fields)
  | BFun tparams tret =>
      let* tparams' := mmap (btyp_to_typ te) tparams in
      let* tret' := btyp_to_typ te tret in
      ret (TFun tparams' tret')
  | BAbs t => ret (TAbs t)
  end.

Definition tenv_update_type_def (te:tenv) (t : type_def btyp) : res tenv :=
  match t with
  | TdEnum {| ed_name := x ; ed_elems := l |} =>
      tenv_update_defs te x (Adt_enum l)
  | TdRecord {| rd_name := x ; rd_fields := l |} =>
      let* l' := MapList.map_err (btyp_to_typ te) l in
      tenv_update_defs te x (Adt_record l')
  | TdAbstract id s => OK te
  end.

Fixpoint xtenv_of_type_defs (te:tenv) (tds: list (type_def btyp)) :=
  match tds with
  | nil => OK te
  | t::tds => let* te' := tenv_update_type_def te t in
              xtenv_of_type_defs te' tds
  end.

Definition tenv_of_type_defs (tds: list (type_def btyp)) :=
  xtenv_of_type_defs tenv_empty tds.

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
  | AConstr _ ty
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

Definition gcontext : Type := STree.t btyp.

Definition lcontext : Type := STree.t btyp.

Definition gcontext_get (gx: gcontext) (x: ident) : res btyp :=
  match STree.get x gx with
  | Some t => ret t
  | None => failwith "Typing.gcontext_get: unknown identifier"
  end.

Definition gcontext_update (gx: gcontext) (x: ident) (ty: btyp) : res gcontext :=
  match gcontext_get gx x with
  | OK _ => failwith "Typing.gcontext_update: global symbol already defined"
  | Error _ => ret (STree.set x ty gx)
  end.

Definition lcontext_get (lx: lcontext) (x: ident) : res btyp :=
  match STree.get x lx with
  | Some t => ret t
  | None => failwith "Typing.lcontext_get: unknown identifier"
  end.

Definition lcontext_update (lx: lcontext) (x: ident) (ty: btyp) : res lcontext :=
  match lcontext_get lx x with
  | OK t =>
      if btyp_eq_dec ty t then ret (STree.set x ty lx)
      else
        failwith "Typing.lcontext_update: variable shadowing with a different type"
  | Error _ => ret (STree.set x ty lx)
  end.

Definition typof_constr (be: benv) (c: ident) : res btyp :=
  match benv_get_constr_typ be c with
  | OK eid => ret (BEnum eid)
  | Error _ => failwith "Typing.typof_constr: undefined enum constructor"
  end.

Definition typof_var (gx: gcontext) (lx: lcontext) (x: ident) : res btyp :=
  match lcontext_get lx x with
  | OK ty => eret ty
  | Error _ =>
      match gcontext_get gx x with
      | OK (BArray _)
      | OK (BRecord _)
      | OK (BAbs _) =>
          failwith "Typing.typof_var: the use of non-primitive global constants is not supported"
      | OK (BEnum _) =>
          failwith "Typing.typof_var: enum constructors cannot be used in constant definitions"
      | OK ty => eret ty
      | Error _ => failwith "Typing.typof_var: unknown identifier"
      end
  end.

Definition typecheck_cast (from: btyp) (to: btyp) : res btyp :=
  match from with
  | BBool | BInt32 _ | BInt64 _ =>
      match to with
      | BBool | BInt32 _ | BInt64 _ | BEnum _ => ret to
      | _ => fail
      end
  | BEnum _ =>
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
      | BEnum t1, BEnum t2 =>
          if Ident.eq_dec t1 t2 then ret BBool
          else failwith "Typing.typecheck_binary_op: type mismach"
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

Definition typecheck_array_get (arch: Target.archi) (ty1 ty2: btyp) : res btyp :=    
  match ty1 with
  | BArray ta =>
      if btyp_eq_dec ty2 (arr_index_btyp arch) then ret ta
      else failwith "Typing.typecheck_array_get: array index type mismatch"
  | _ => failwith "Typing.typecheck_array_get: array typed expected"
  end.

Definition typecheck_array_set (arch: Target.archi) (ty1 ty2 ty3: btyp) : res btyp :=
  match ty1 with
  | BArray ta =>
      if btyp_eq_dec ty2 (arr_index_btyp arch) then
        if btyp_eq_dec ta ty3 then ret ty1
        else failwith "Typing.typecheck_array_set: type mismatch"
      else failwith "Typing.typecheck_array_set: array index type mismatch"
  | _ => failwith "Typing.typecheck_array_set: array type expected"
  end.

Definition typecheck_record_proj (be: benv) (ty: btyp) (x: ident) : res btyp :=
  match ty with
  | BRecord t =>
      let/catch fields := benv_get_rdef be t
        /> "Typing.typecheck_record_proj: unknown record type"
      in
      btypof_field x fields
  | _ => failwith "Typing.typecheck_record_proj: record type expected"
  end.

Definition typecheck_record_update (be: benv) (ty1 ty2: btyp) (x: ident) : res btyp :=
  match ty1 with
  | BRecord t =>
      let/catch fields := benv_get_rdef be t
        /> "Typing.typecheck_record_proj: unknown record type"
      in
      let* tx := btypof_field x fields in
      if btyp_eq_dec tx ty2 then ret ty1
      else failwith "Typing.typecheck_record_update: type mismatch"
  | _ => failwith "Typing.typecheck_record_update: record type expected"
  end.

  Inductive access_btyp : Type :=
    | AbtypAcRecordField : ident -> access_btyp
    | AbtypAcArrayIndex : btyp -> access_btyp.

  Fixpoint typecheck_access (arch: Target.archi) (be: benv) (gx: gcontext) (lx: lcontext) (ty: btyp) (acs: list access_btyp) : res (btyp * list btyp) := 
    match acs with
    | nil => ret (ty, nil)
    | ac :: acs' =>
        match ac with
        | AbtypAcRecordField f =>
            let* ty' := typecheck_record_proj be ty f in
            let* (r, lr) := typecheck_access arch be gx lx ty' acs' in
            ret (r, ty' :: lr)
        | AbtypAcArrayIndex ta =>
            let* ty' := typecheck_array_get arch ty ta in
            let* (r, lr) := typecheck_access arch be gx lx ty' acs' in
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

Fixpoint typecheck_struct_lit (l1: smaplist literal) (l2: smaplist btyp) : bool :=
  match l1, l2 with
  | nil, nil => true
  | (x1, l1) :: l1', (x2, tx2) :: l2' =>
      let tx1 := typof_literal l1 in
      if btyp_eq_dec tx1 tx2 then typecheck_struct_lit l1' l2'
      else false
  | _, _ => false
  end.

Definition typecheck_pattern (be: benv) (te: btyp) (elems: list ident) (p: pattern) (unmatched: list ident) : res (list ident) :=
  if list_is_empty unmatched then
    failwith "Typing.typecheck_pattern: redundant pattern"
  else
    match p with
    | PWildcard => ret nil
    | PIdent i =>
        let* tp := typof_constr be i in
        if btyp_eq_dec te tp then
          if List.in_dec Ident.eq_dec i elems then
            if List.in_dec Ident.eq_dec i unmatched then
              ret (List.remove Ident.eq_dec i unmatched)
            else
              failwith "Typing.typecheck_pattern: redundant pattern"
          else
            failwith "Typing.typecheck_pattern: pattern is not an enum element"        
        else failwith "Typing.typecheck_pattern: pattern type mismatch"
  end.

Fixpoint typecheck_match_rec (be: benv) (te: btyp) (elems: list ident) (unmatched: list ident) (cases: list (pattern * btyp)) : res btyp :=
  match cases with
  | nil => fail
  | (x, tx) :: nil =>
      let* unmatched' := typecheck_pattern be te elems x unmatched in
      if list_is_empty unmatched' then ret tx
      else failwith "Typing.typecheck_match_rec: non-exhaustive pattern-matching"
  | (x, tx) :: ((_ :: _) as cases') =>
      let* unmatched' := typecheck_pattern be te elems x unmatched in
      let* tr := typecheck_match_rec be te elems unmatched' cases' in
      if btyp_eq_dec tx tr then ret tr
      else failwith "Typing.typecheck_match_rec: type mismtach"
  end.

Definition typecheck_match (be: benv) (ty: btyp) (cases: list (pattern * btyp)) : res btyp :=
  match ty with
  | BEnum te =>
      let* elems := benv_get_edef be te in
      typecheck_match_rec be ty elems elems cases
  | _ => failwith "Typing.typecheck_match: enum type expected"
  end.

Fixpoint typecheck_literal (be: benv) (l: Syntax.literal) : res literal :=
  match l with
  | Syntax.LTrue => ret (LTrue BBool)
  | Syntax.LFalse => ret (LFalse BBool)
  | Syntax.LInt32 i s => ret (LInt32 i (BInt32 s))
  | Syntax.LInt64 i s => ret (LInt64 i (BInt64 s))
  | Syntax.LArray a =>
      let* a' := mmap (typecheck_literal be) a in
      let* t := typecheck_array_lit a' in
      ret (LArray a' (BArray t))
  | Syntax.LRecord rc x =>
      let* rc' := MapList.map_err (typecheck_literal be) rc in
      let* t := benv_get_rdef be x in
      if typecheck_struct_lit rc' t then ret (LRecord rc' (BRecord x))
      else failwith "Typing.typecheck_literal: record type mismatch"
  end.
