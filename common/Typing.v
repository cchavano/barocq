From Coq Require Import List String ZArith Bool.
From BarocqComp Require Import Error Maps2 Utils Types Syntax Barray Benum.
Import ListNotations.
Import Syntax.Typed.

(** * Environments of types *)

(** ** Identifiers to type definitions + enum constructors to enum identifier *)

Module TEnv.

  Set Implicit Arguments.

  Section TYP.

  Variable typ : Type.

  Record t := mk_tenv {
    tenv_defs : STree.t (type_def typ);
    tenv_constr_types : STree.t ident;
  }.

  Definition empty : t := {|
    tenv_defs := STree.empty;
    tenv_constr_types := STree.empty
  |}.

  Definition get_edef (te: t) (x: ident) : res (list ident) :=
    match STree.get x (tenv_defs te) with
    | Some (TdEnum elems) => ret elems
    | _ => fail
    end.

  Definition get_rdef (te: t) (x: ident) : res (smaplist typ) :=
    match STree.get x (tenv_defs te) with
    | Some (TdRecord fields) => ret fields
    | _ => fail
    end.

  Definition get_constr_typ (te: t) (x: ident) : res ident :=
    err_of_opt (STree.get x (tenv_constr_types te)).

  Definition update_constr_types (te: t) (elem: ident) (eid: ident) : res t :=
    let elems := (tenv_constr_types te) in
    match STree.get elem elems with
    | Some _ => fail
    | None =>
        ret {|
          tenv_defs := (tenv_defs te);
          tenv_constr_types := STree.set elem eid elems
        |}
  end.

  Definition update_defs (te: t) (x: ident) (td: type_def typ) : res t :=
    let types := tenv_defs te in
    match STree.get x types with
    | Some _ => fail
    | None =>
        let te' := mk_tenv (STree.set x td types) (tenv_constr_types te) in
        match td with
        | TdEnum elems =>
            list_fold_left_err
              (fun acc_te constr => update_constr_types acc_te constr x)
              elems
              (ret te')
        | _ => ret te'
        end
    end.

  Definition build (types: smaplist (type_def typ)) : res t :=
    Utils.list_fold_left_err
      (fun acc_be '(tid, td) => update_defs acc_be tid td)
      types
      (eret empty).

  End TYP.

End TEnv.

Arguments TEnv.empty {typ}.

Definition benv := TEnv.t field_descr.

Definition tenv := TEnv.t typ.

(** ** Conversion of concrete types to plain types *)

Fixpoint btyp_to_typ (te: tenv) (ty: btyp) : res typ :=
  match ty with
  | BBool => ret TBool
  | BInt32 s => ret (TInt32 s)
  | BInt64 s => ret (TInt64 s)
  | BArray ta _ =>
      let* ta' := btyp_to_typ te ta in 
      ret (TArray ta')
  | BEnum tn =>
      let* elems := TEnv.get_edef te tn in
      ret (TEnum tn elems) 
  | BRecord tr _ =>
      let* fields := TEnv.get_rdef te tr in
      ret (TRecord tr fields)
  | BFun tparams tret =>
      let* tparams' := mmap (btyp_to_typ te) tparams in
      let* tret' := btyp_to_typ te tret in
      ret (TFun tparams' tret')
  | BAbs t => ret (TAbs t)
  end.

Definition tenv_update_type_def (te:tenv) (tid: ident) (t : type_def field_descr) : res tenv :=
  match t with
  | TdEnum elems =>
      TEnv.update_defs te tid (TdEnum elems)
  | TdRecord fields =>
      let* fields' := MapList.map_err (btyp_to_typ te) (MapList.map fst fields) in
      TEnv.update_defs te tid (TdRecord fields')
  end.

Fixpoint xtenv_of_type_defs (te:tenv) (tds: smaplist (type_def field_descr)) : res tenv :=
  match tds with
  | nil => OK te
  | (tid, t)::tds => let* te' := tenv_update_type_def te tid t in
              xtenv_of_type_defs te' tds
  end.

Definition tenv_of_type_defs (tds: smaplist (type_def field_descr)) : res tenv :=
  xtenv_of_type_defs TEnv.empty tds.

Definition typof_literal (l: literal) : btyp :=
  match l with
  | LTrue
  | LFalse => BBool
  | LInt32 _ s => BInt32 s
  | LInt64 _ s => BInt64 s
  | LArray _ ta ly => BArray ta ly
  | LRecord rc ub rid => BRecord rid ub
  end.

Definition typof_atom (a: atom) : btyp :=
  match a with
  | ATrue
  | AFalse => BBool
  | AInt32 _ s => BInt32 s
  | AInt64 _ s => BInt64 s
  | AConstr _ _ ty
  | AVar _ ty
  | ACast _ ty
  | AUnaryOp _ _ ty
  | ABinaryOp _ _ _ ty
  | AArrayGet _ _ _ ty
  | ARecordProj _ _ _ ty 
  | APureCall _ _ _ ty => ty 
  end.

Definition typof_comp (c: comp) : btyp :=
  match c with
  | CpAtom _ ty
  | CpArraySet _ _ _ ty
  | CpRecordUpdate _ _ _ ty
  | CpCall _ _ _ ty => ty
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
  match TEnv.get_constr_typ be c with
  | OK eid => ret (BEnum eid)
  | Error _ => failwith "Typing.typof_constr: undefined enum constructor"
  end.

Definition typof_var (gx: gcontext) (lx: lcontext) (x: ident) : res btyp :=
  match lcontext_get lx x with
  | OK ty => eret ty
  | Error _ =>
      match gcontext_get gx x with
      | OK (BArray _ _)
      | OK (BRecord _ _)
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
  | BArray ta _ =>
      if btyp_eq_dec ty2 (arr_index_btyp arch) then ret ta
      else failwith "Typing.typecheck_array_get: array index type mismatch"
  | _ => failwith "Typing.typecheck_array_get: array typed expected"
  end.

Definition typecheck_array_get2 (arch: Target.archi) (ty1 ty2: btyp) : res field_descr :=    
  match ty1 with
  | BArray ta ly =>
      if btyp_eq_dec ty2 (arr_index_btyp arch) then ret (ta, ly)
      else failwith "Typing.typecheck_array_get2: array index type mismatch"
  | _ => failwith "Typing.typecheck_array_get2: array type expected"
  end.

Definition typecheck_array_set (arch: Target.archi) (ty1 ty2 ty3: btyp) : res btyp :=
  match ty1 with
  | BArray ta _ =>
      if btyp_eq_dec ty2 (arr_index_btyp arch) then
        if btyp_eq_dec ta ty3 then ret ty1
        else failwith "Typing.typecheck_array_set: type mismatch"
      else failwith "Typing.typecheck_array_set: array index type mismatch"
  | _ => failwith "Typing.typecheck_array_set: array type expected"
  end.

Definition typecheck_record_proj (be: benv) (ty: btyp) (x: ident) : res btyp :=
  match ty with
  | BRecord t _ =>
      let/catch fields := TEnv.get_rdef be t
        /> "Typing.typecheck_record_proj: unknown record type"
      in
      btypof_field x (MapList.map fst fields)
  | _ => failwith "Typing.typecheck_record_proj: record type expected"
  end.

Definition typecheck_record_proj2 (be: benv) (ty: btyp) (x: ident) : res field_descr :=
  match ty with
  | BRecord t _ =>
      let/catch fields := TEnv.get_rdef be t
        /> "Typing.typecheck_record_proj: unknown record type"
      in
      MapList.find_err Ident.eq_dec x fields
  | _ => failwith "Typing.typecheck_record_proj: record type expected"
  end.

Definition typecheck_record_update (be: benv) (ty1 ty2: btyp) (x: ident) : res btyp :=
  match ty1 with
  | BRecord t _ =>
      let/catch fields := TEnv.get_rdef be t
        /> "Typing.typecheck_record_proj: unknown record type"
      in
      let* tx := btypof_field x (MapList.map fst fields) in
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

Fixpoint typecheck_literal (be: benv) (l: Syntax.literal) : res literal :=
  match l with
  | Syntax.LTrue => ret LTrue
  | Syntax.LFalse => ret LFalse
  | Syntax.LInt32 i s => ret (LInt32 i s)
  | Syntax.LInt64 i s => ret (LInt64 i s)
  | Syntax.LArray a ta ly =>
      let* a' := mmap (typecheck_literal be) a in
      let* t := typecheck_array_lit a' in
      if btyp_eq_dec ta t then ret (LArray a' t ly)
      else fail
  | Syntax.LRecord rc ub x =>
      let* rc' := MapList.map_err (typecheck_literal be) rc in
      let* t := TEnv.get_rdef be x in
      if typecheck_struct_lit rc' (MapList.map fst t) then ret (LRecord rc' ub x)
      else failwith "Typing.typecheck_literal: record type mismatch"
  end.

Fixpoint zval_of_constr_rec (elems: list ident) (i: Z) (constr: ident) : res Z :=
  match elems with
  | nil => fail
  | ci :: elems' => 
      if Ident.eq_dec ci constr then ret i
      else zval_of_constr_rec elems' (Z.add i Z.one) constr
  end.

Definition zval_of_constr (be: benv) (tc: btyp) (constr: ident) : res Z :=
  match tc with
  | BEnum eid =>
      let* elems := TEnv.get_edef be eid in
      zval_of_constr_rec elems Z0 constr
  | _ => fail
  end.

Definition typecheck_pattern (be: benv) (te: btyp) (elems: list ident) (p: pattern) (unmatched: list ident) : res (list ident) :=
  if list_is_empty unmatched then
    failwith "Typing.typecheck_pattern: redundant pattern"
  else
    match p with
    | PWildcard => ret nil
    | PIdent i z =>
        let* tp := typof_constr be i in
        if btyp_eq_dec te tp then
          if List.in_dec Ident.eq_dec i elems then
            if List.in_dec Ident.eq_dec i unmatched then
              let* z2 := zval_of_constr be te i in
              if Z.eq_dec z z2 then ret (List.remove Ident.eq_dec i unmatched)
              else failwith "Typing.typecheck_pattern: wrong Z value of pattern"
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
      let* elems := TEnv.get_edef be te in
      typecheck_match_rec be ty elems elems cases
  | _ => failwith "Typing.typecheck_match: enum type expected"
  end.

Module Typ.
  (* Typing functions operating on [typ] *)
  Definition typecheck_unary_op (op: unary_op) (ty: typ) : res typ :=
    match op, ty with
    | UopNotbool, TBool
    | UopNotint, TInt32 _
    | UopNotint, TInt64 _
    | UopNeg, TInt32 _
    | UopNeg, TInt64 _
    | UopPlus, TInt32 _
    | UopPlus, TInt64 _ => ret ty
    | _, _ => failwith "Typing.typecheck_unary_op: type mismatch"
    end.


  Definition is_bool (ty:typ) :=
    match ty with
    | TBool => true
    | _     => false
    end.

  Definition same_num (t1 t2:typ) :=
    match t1 , t2 with
    | TInt32 s1, TInt32 s2
    | TInt64 s1, TInt64 s2 =>
        if signedness_eq_dec s1 s2 then true
        else false
    | TEnum t1 l1, TEnum t2 l2 =>
        if Ident.eq_dec t1 t2 then
          forall2b String.eqb l1 l2
        else false
    |  _ , _ => false
  end.

  Definition same_int (t1 t2:typ) :=
    match t1 , t2 with
    | TInt32 s1, TInt32 s2
    | TInt64 s1, TInt64 s2 =>
        if signedness_eq_dec s1 s2 then true
        else false
    |  _ , _ => false
  end.



  Definition typecheck_binary_op (op: binary_op) (ty1 ty2: typ) : res typ :=
    match op with
    | BopAndbool
    | BopOrbool
    | BopXorbool => if is_bool ty1 && is_bool ty2
                    then ret TBool
                    else failwith "Typing.typecheck_binary_op: type mismatch"
    | BopEq
    | BopNeq => if same_num ty1 ty2 || (is_bool ty1 && is_bool ty2)
                then ret TBool
                else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
    | BopLt
    | BopLe
    | BopGt
    | BopGe => if same_num ty1 ty2
               then ret TBool
               else failwith "Typing.typecheck_binary_op: type mismatch"
    | _ =>  if same_int ty1 ty2
            then ret ty1
            else failwith "Typing.typecheck_binary_op: integer signedness mismatch"
  end.


End Typ.
