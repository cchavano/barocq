From Coq Require Import List String ZArith Bool.
From BarocqComp Require Import Res Option Maps2 Utils Types Syntax Barray Benum.
Import ListNotations.
Local Open Scope option_monad_scope.

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

  Definition get_edef (te: t) (x: ident) : option (list ident) :=
    match STree.get x (tenv_defs te) with
    | Some (TdEnum elems) => ret elems
    | _ => fail
    end.

  Definition get_rdef (te: t) (x: ident) : option (smaplist typ) :=
    match STree.get x (tenv_defs te) with
    | Some (TdRecord fields) => ret fields
    | _ => fail
    end.

  Definition get_constr_typ (te: t) (x: ident) : option ident :=
    STree.get x (tenv_constr_types te).

  Definition update_constr_types (te: t) (elem: ident) (eid: ident) : option t :=
    let elems := (tenv_constr_types te) in
    match STree.get elem elems with
    | Some _ => fail
    | None =>
        ret {|
          tenv_defs := (tenv_defs te);
          tenv_constr_types := STree.set elem eid elems
        |}
  end.

  Definition update_defs (te: t) (x: ident) (td: type_def typ) : option t :=
    let types := tenv_defs te in
    match STree.get x types with
    | Some _ => fail
    | None =>
        let te' := mk_tenv (STree.set x td types) (tenv_constr_types te) in
        match td with
        | TdEnum elems =>
            fold_left_err
              (fun acc_te constr => update_constr_types acc_te constr x)
              elems
              te'
        | _ => ret te'
        end
    end.

  Definition build (types: smaplist (type_def typ)) : option t :=
    fold_left_err
      (fun acc_be '(tid, td) => update_defs acc_be tid td)
      types
      empty.

  End TYP.

End TEnv.

Arguments TEnv.empty {typ}.

Definition benv := TEnv.t field_descr.

Definition tenv := TEnv.t typ.

(** ** Conversion of concrete types to plain types *)

Fixpoint btyp_to_typ (te: tenv) (ty: btyp) : option typ :=
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

Definition tenv_update_type_def (te:tenv) (tid: ident) (t : type_def field_descr) : option tenv :=
  match t with
  | TdEnum elems =>
      TEnv.update_defs te tid (TdEnum elems)
  | TdRecord fields =>
      let* fields' := mmap_assoc (btyp_to_typ te) (MapList.map fst fields) in
      TEnv.update_defs te tid (TdRecord fields')
  end.

Fixpoint xtenv_of_type_defs (te:tenv) (tds: smaplist (type_def field_descr)) : option tenv :=
  match tds with
  | nil => Some te
  | (tid, t)::tds => let* te' := tenv_update_type_def te tid t in
              xtenv_of_type_defs te' tds
  end.

Definition tenv_of_type_defs (tds: smaplist (type_def field_descr)) : option tenv :=
  xtenv_of_type_defs TEnv.empty tds.

Definition gcontext : Type := STree.t btyp.

Definition lcontext : Type := STree.t btyp.

Definition gcontext_get (gx: gcontext) (x: ident) : res btyp :=
  match STree.get x gx with
  | Some t => eret t
  | None => efailwith "Typing.gcontext_get: unknown identifier"
  end.

Definition gcontext_update (gx: gcontext) (x: ident) (ty: btyp) : res gcontext :=
  match gcontext_get gx x with
  | OK _ => efailwith "Typing.gcontext_update: global symbol already defined"
  | Error _ => eret (STree.set x ty gx)
  end.

Definition lcontext_get (lx: lcontext) (x: ident) : res btyp :=
  match STree.get x lx with
  | Some t => eret t
  | None => efailwith "Typing.lcontext_get: unknown identifier"
  end.

Definition lcontext_update (lx: lcontext) (x: ident) (ty: btyp) : lcontext :=
  STree.set x ty lx.

Definition lcontext_update_imp (lx: lcontext) (x: ident) (ty: btyp) : res lcontext :=
  match lcontext_get lx x with
  | OK t =>
      if btyp_eq_dec ty t then eret (STree.set x ty lx)
      else
        efailwith "Typing.lcontext_update: variable shadowing with a different type"
  | Error _ => eret (STree.set x ty lx)
  end.
  
Definition typof_constr (be: benv) (c: ident) : res btyp :=
  match Res.of_opt (TEnv.get_constr_typ be c) with
  | OK eid => eret (BEnum eid)
  | Error _ => efailwith "Typing.typof_constr: undefined enum constructor"
  end.

Definition typof_var (gx: gcontext) (lx: lcontext) (x: ident) : res btyp :=
  match lcontext_get lx x with
  | OK ty => eret ty
  | Error _ =>
      match gcontext_get gx x with
      | OK (BArray _ _)
      | OK (BRecord _ _)
      | OK (BAbs _) =>
          efailwith "Typing.typof_var: the use of non-primitive global constants is not supported"
      | OK (BEnum _) =>
          efailwith "Typing.typof_var: enum constructors cannot be used in constant definitions"
      | OK ty => eret ty
      | Error _ => efailwith "Typing.typof_var: unknown identifier"
      end
  end.

Definition typof_atom (te: tenv) (a: atom) : option typ :=
  btyp_to_typ te (btypof_atom a).

Definition typof_comp (te:tenv) (c: comp) : option typ :=
  btyp_to_typ te (btypof_comp c).

Definition typecheck_cast (from: btyp) (to: btyp) : option btyp :=
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
  | UopPlus, BInt64 _ => eret ty
  | _, _ => efailwith "Typing.typecheck_unary_op: type mismatch"
  end.

Definition typecheck_binary_op (op: binary_op) (ty1 ty2: btyp) : res btyp :=
  match op with
  | BopAndbool
  | BopOrbool
  | BopXorbool =>
      match ty1, ty2 with
      | BBool, BBool => eret ty1
      | _, _ => efailwith "Typing.typecheck_binary_op: type mismatch"
      end
  | BopEq
  | BopNeq =>
      match ty1, ty2 with
      | BBool, BBool => eret ty1
      | BInt32 s1, BInt32 s2
      | BInt64 s1, BInt64 s2 =>
          if signedness_eq_dec s1 s2 then eret BBool
          else efailwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | BEnum t1, BEnum t2 =>
          if Ident.eq_dec t1 t2 then eret BBool
          else efailwith "Typing.typecheck_binary_op: type mismach"
      | _, _ =>
          efailwith "Typing.typecheck_binary_op: type mismatch"
      end
  | BopLt
  | BopLe 
  | BopGt
  | BopGe =>
      match ty1, ty2 with
      | BInt32 s1, BInt32 s2
      | BInt64 s1, BInt64 s2 =>
          if signedness_eq_dec s1 s2 then eret BBool
          else efailwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
        efailwith "Typing.typecheck_binary_op: type mismatch"
      end
  | _ =>
      match ty1, ty2 with
      | BInt32 s1, BInt32 s2
      | BInt64 s1, BInt64 s2 =>
          if signedness_eq_dec s1 s2 then eret ty1
          else efailwith "Typing.typecheck_binary_op: integer signedness mismatch"
      | _, _ =>
        efailwith "Typing.typecheck_binary_op: type mismatch"
      end
  end.

Definition typecheck_array_get (arch: Target.archi) (ty1 ty2: btyp) : res btyp :=    
  match ty1 with
  | BArray ta _ =>
      if btyp_eq_dec ty2 (arr_index_btyp arch) then eret ta
      else efailwith "Typing.typecheck_array_get: array index type mismatch"
  | _ => efailwith "Typing.typecheck_array_get: array typed expected"
  end.

Definition typecheck_array_get2 (arch: Target.archi) (ty1 ty2: btyp) : res field_descr :=    
  match ty1 with
  | BArray ta ly =>
      if btyp_eq_dec ty2 (arr_index_btyp arch) then OK (ta, ly)
      else efailwith "Typing.typecheck_array_get2: array index type mismatch"
  | _ => efailwith "Typing.typecheck_array_get2: array type expected"
  end.

Definition typecheck_array_set (arch: Target.archi) (ty1 ty2 ty3: btyp) : res btyp :=
  match ty1 with
  | BArray ta _ =>
      if btyp_eq_dec ty2 (arr_index_btyp arch) then
        if btyp_eq_dec ta ty3 then OK ty1
        else efailwith "Typing.typecheck_array_set: type mismatch"
      else efailwith "Typing.typecheck_array_set: array index type mismatch"
  | _ => efailwith "Typing.typecheck_array_set: array type expected"
  end.

Local Open Scope error_monad_scope.

Definition typecheck_record_proj (be: benv) (ty: btyp) (x: ident) : res btyp :=
  match ty with
  | BRecord t _ =>
      do/c fields <- Res.of_opt (TEnv.get_rdef be t)
         /> efailwith "Typing.typecheck_record_proj: unknown record type";
      Res.of_opt (btypof_field x (MapList.map fst fields))
  | _ => efailwith "Typing.typecheck_record_proj: record type expected"
  end.

Definition typecheck_record_proj2 (be: benv) (ty: btyp) (x: ident) : res field_descr :=
  match ty with
  | BRecord t _ =>
      do/c fields <- Res.of_opt (TEnv.get_rdef be t)
        /> efailwith "Typing.typecheck_record_proj: unknown record type";
      MapList.find_err Ident.eq_dec x fields
  | _ => efailwith "Typing.typecheck_record_proj: record type expected"
  end.

Definition typecheck_record_update (be: benv) (ty1 ty2: btyp) (x: ident) : res btyp :=
  match ty1 with
  | BRecord t _ =>
      do/c fields <- Res.of_opt (TEnv.get_rdef be t)
        /> efailwith "Typing.typecheck_record_proj: unknown record type";
      do tx <- Res.of_opt (btypof_field x (MapList.map fst fields));
      if btyp_eq_dec tx ty2 then eret ty1
      else efailwith "Typing.typecheck_record_update: type mismatch"
  | _ => efailwith "Typing.typecheck_record_update: record type expected"
  end.

Fixpoint typecheck_call_rec (tparams targs: list btyp) (tret: btyp) : res btyp :=
  match tparams, targs with
  | nil, nil => eret tret
  | tp1 :: tparams', ta1 :: targs' =>
      if btyp_eq_dec tp1 ta1 then
        typecheck_call_rec tparams' targs' tret
      else 
        efailwith "Typing.typecheck_call_rec: type mismatch"
  | _, _ =>
      efailwith "Typing.typecheck_call_rec: wrong number of arguments"
  end.

Definition typecheck_call (ty: btyp) (targs: list btyp) : res btyp :=
  match ty with
  | BFun tparams tret => typecheck_call_rec tparams targs tret
  | _ => efailwith "Typing.typecheck_call: function type expected"
  end.

Fixpoint typecheck_array_lit (a: array literal) : res btyp :=
  match a with
  | nil => efailwith "Typing.typecheck_array_lit: empty array"
  | l :: nil => eret (btypof_literal l)
  | l :: a' =>
      do t <- typecheck_array_lit a';
      if btyp_eq_dec (btypof_literal l) t then OK t
      else efailwith "Typing.typecheck_array_lit: type mismatch"
  end.

Fixpoint typecheck_struct_lit (l1: smaplist literal) (l2: smaplist btyp) : bool :=
  match l1, l2 with
  | nil, nil => true
  | (x1, l1) :: l1', (x2, tx2) :: l2' =>
      let tx1 := btypof_literal l1 in
      if btyp_eq_dec tx1 tx2 then typecheck_struct_lit l1' l2'
      else false
  | _, _ => false
  end.

Fixpoint typecheck_literal (be: benv) (l: Syntax.literal) : res literal :=
  match l with
  | Syntax.LTrue => eret LTrue
  | Syntax.LFalse => eret LFalse
  | Syntax.LInt32 i s => eret (LInt32 i s)
  | Syntax.LInt64 i s => eret (LInt64 i s)
  | Syntax.LArray a ta ly =>
      do a' <- Res.mmap (typecheck_literal be) a;
      do t <- typecheck_array_lit a';
      if btyp_eq_dec ta t then eret (LArray a' t ly)
      else efail
  | Syntax.LRecord rc ub x =>
      do rc' <- MapList.map_err (typecheck_literal be) rc;
      do t <- Res.of_opt (TEnv.get_rdef be x);
      if typecheck_struct_lit rc' (MapList.map fst t) then eret (LRecord rc' ub x)
      else efailwith "Typing.typecheck_literal: record type mismatch"
  end.

Fixpoint zval_of_constr_rec (elems: list ident) (i: Z) (constr: ident) : res Z :=
  match elems with
  | nil => efail
  | ci :: elems' => 
      if Ident.eq_dec ci constr then eret i
      else zval_of_constr_rec elems' (Z.add i Z.one) constr
  end.

Definition zval_of_constr (be: benv) (tc: btyp) (constr: ident) : res Z :=
  match tc with
  | BEnum eid =>
      do elems <- Res.of_opt (TEnv.get_edef be eid);
      zval_of_constr_rec elems Z0 constr
  | _ => efail
  end.

Definition typecheck_pattern (be: benv) (te: btyp) (elems: list ident) (p: pattern) (unmatched: list ident) : res (list ident) :=
  if list_is_empty unmatched then
    efailwith "Typing.typecheck_pattern: redundant pattern"
  else
    match p with
    | PWildcard => eret nil
    | PIdent i z =>
        do tp <- typof_constr be i;
        if btyp_eq_dec te tp then
          if List.in_dec Ident.eq_dec i elems then
            if List.in_dec Ident.eq_dec i unmatched then
              do z2 <- zval_of_constr be te i;
              if Z.eq_dec z z2 then eret (List.remove Ident.eq_dec i unmatched)
              else efailwith "Typing.typecheck_pattern: wrong Z value of pattern"
            else
              efailwith "Typing.typecheck_pattern: redundant pattern"
          else
            efailwith "Typing.typecheck_pattern: pattern is not an enum element"        
        else efailwith "Typing.typecheck_pattern: pattern type mismatch"
  end.

Fixpoint typecheck_match_rec (be: benv) (te: btyp) (elems: list ident) (unmatched: list ident) (cases: list (pattern * btyp)) : res btyp :=
  match cases with
  | nil => efail
  | (x, tx) :: nil =>
      do unmatched' <- typecheck_pattern be te elems x unmatched;
      if list_is_empty unmatched' then eret tx
      else efailwith "Typing.typecheck_match_rec: non-exhaustive pattern-matching"
  | (x, tx) :: ((_ :: _) as cases') =>
      do unmatched' <- typecheck_pattern be te elems x unmatched;
      do tr <- typecheck_match_rec be te elems unmatched' cases';
      if btyp_eq_dec tx tr then eret tr
      else efailwith "Typing.typecheck_match_rec: type mismtach"
  end.

Definition typecheck_match (be: benv) (ty: btyp) (cases: list (pattern * btyp)) : res btyp :=
  match ty with
  | BEnum te =>
      do elems <- Res.of_opt (TEnv.get_edef be te);
      typecheck_match_rec be ty elems elems cases
  | _ => efailwith "Typing.typecheck_match: enum type expected"
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
    | UopPlus, TInt64 _ => eret ty
    | _, _ => efailwith "Typing.typecheck_unary_op: type mismatch"
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
                    then eret TBool
                    else efailwith "Typing.typecheck_binary_op: type mismatch"
    | BopEq
    | BopNeq => if same_num ty1 ty2 || (is_bool ty1 && is_bool ty2)
                then eret TBool
                else efailwith "Typing.typecheck_binary_op: integer signedness mismatch"
    | BopLt
    | BopLe
    | BopGt
    | BopGe => if same_num ty1 ty2
               then eret TBool
               else efailwith "Typing.typecheck_binary_op: type mismatch"
    | _ =>  if same_int ty1 ty2
            then eret ty1
            else efailwith "Typing.typecheck_binary_op: integer signedness mismatch"
  end.

End Typ.
