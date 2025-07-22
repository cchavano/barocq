From Coq Require Import List String ListDec PArith Bool.
From compcert Require Import Integers Maps Ctypes.
From BarocqComp Require Import Error MapList Utils Intop Barray Brecord Types Typing Syntax.
Import ListNotations.

(** * Abstract syntax *)

(** ** Expressions *)

Inductive expr : Type :=
  | ETrue : expr                                            (* true constant *)
  | EFalse : expr                                           (* false constant *)
  | EInt32 (i: int) (s: signedness) : expr                  (* 32-bit signed or unsigned integer *)
  | EInt64 (i: int64) (s: signedness) : expr                (* 64-bit signed orunsigned integer *)    
  | EVar (x: ident) : expr                                  (* variable *)
  | ECast (e: expr) (ty: btyp)                              (* e as ty *)
  | EUnaryOp (op: unary_op) (e: expr) : expr                (* op e *)
  | EBinaryOp (op: binary_op) (e1 e2 : expr) : expr         (* e1 op e2 *)
  | EArrayGet (a i: expr) : expr                            (* a[i] *)
  | EArraySet (a i e: expr) : expr                          (* a[i] <- e *)
  | ERecordProj (st: expr) (f: ident) : expr                (* st.f *)
  | ERecordUpdate (st: expr) (f: ident) (e: expr) : expr    (* st.f <- e *)
  | EDeepAccess (e: expr) (acs: list access) : expr         (* eX1X2....Xn where Xi = .fi or [ei] *)     
  | EApp (e: expr) (args: list expr) : expr                 (* e(args) *)
  | EIfThenElse (e1 e2 e3: expr) : expr                     (* if e1 then e2 else e3 *)
  | ELetIn (x: ident) (e1 e2: expr) : expr                  (* let x = e1 in e2 *)

with access : Type :=
  | AcRecordField : ident -> access
  | AcArrayIndex : expr -> access.

(** ** Functions *)

Definition function : Type := Syntax.function expr.

(** ** Global definitions *)

Inductive globdef : Type :=
  | DefType (tid: ident) (fields: list (ident * btyp)) : globdef                    (* type tid = { x1: t1; ...; xn: tn; } *)
  | DefConst (x: ident) (l: literal) (ty: btyp) : globdef                           (* defn x : ty = l *)
  | DefFun (x: ident) (f: function) : globdef                                       (* defn x (p1: t1, ..., pn: tn) : ty = e *)
  | DeclType (tid: ident) (tkind: struct_or_union) : globdef                        (* type tid of "tkind" *)
  | DeclConst (x: ident) (ty: btyp) : globdef                                       (* decl x : ty *)
  | DeclFun (x: ident) (tparams: list (param_attr * btyp)) (tret: btyp) : globdef.  (* decl x : tparams -> tret *)

(** We differentiate between "programs" that only contain definitions and 
    "interpretable programs" which also contains top-level expressions to be evaluated.
    Only definitions are compiled down to C. *)

Inductive command : Type :=
  | CmdDef (def: globdef) : command      (* top level definition *)
  | CmdExpr (e: expr) : command.         (* top level expression to be evaluated *)

(** ** Programs *)

Definition program : Type := list globdef.

Definition iprogram : Type := list command.

Definition iprog_to_prog (iprog: iprogram) : program :=
  List.fold_right
    (fun cmd acc =>
        match cmd with
        | CmdDef d => d :: acc
        | _ => acc
        end)
    nil
    iprog.

Module Typed.

  (** * Typed abstract syntax *)

  (** ** Expressions *)

  Inductive expr : Type :=
    | ETrue : btyp -> expr
    | EFalse : btyp -> expr
    | EInt32 : int -> btyp -> expr
    | EInt64 : int64 -> btyp -> expr
    | EVar : ident -> btyp -> expr
    | ECast : expr -> btyp -> expr
    | EUnaryOp : unary_op -> expr -> btyp -> expr
    | EBinaryOp : binary_op -> expr -> expr -> btyp -> expr
    | EArrayGet : expr -> expr -> btyp -> expr
    | EArraySet : expr -> expr -> expr -> btyp -> expr
    | ERecordProj : expr -> ident -> btyp -> expr
    | ERecordUpdate : expr -> ident -> expr -> btyp -> expr
    | EDeepAccess : expr -> list access -> btyp -> expr
    | EApp : expr -> list expr -> btyp -> expr
    | EIfThenElse : expr -> expr -> expr -> btyp -> expr
    | ELetIn : ident -> expr -> expr -> btyp -> expr

  (* An access is associated with a type.
     For every deep access e.X1X2...Xn, Xi has type ty
     iff the expression e.X1...X(i-1)Xi has type ty. *)
  with access : Type :=
    | AcRecordField : ident -> btyp -> access
    | AcArrayIndex : expr -> btyp -> access.

  (** ** Functions *)

  Definition function : Type := Syntax.function expr.

  (** ** Global definitions *)

  Inductive globdef : Type :=
    | DefType : ident -> list (ident * btyp) -> globdef
    | DefConst : ident -> literal -> btyp -> globdef
    | DefFun : ident -> function -> globdef
    | DeclType : ident -> struct_or_union -> globdef
    | DeclConst : ident -> btyp -> globdef
    | DeclFun : ident -> list (param_attr * btyp) -> btyp -> globdef.

  (** ** Programs *)

  Definition program := list globdef.

End Typed.

Module BarocqTyped := Barocq.Typed.

Module Typing.

  Import BarocqTyped.

  Section ARCHI.

    Variable arch : Target.archi.

  Definition typof_expr (e: expr) : btyp :=
    match e with
    | ETrue ty
    | EFalse ty
    | EInt32 _ ty
    | EInt64 _ ty
    | EVar _ ty
    | ECast _ ty
    | EUnaryOp _ _ ty
    | EBinaryOp _ _ _ ty
    | EArrayGet _ _ ty
    | EArraySet _ _ _ ty
    | ERecordProj _ _ ty
    | ERecordUpdate _ _ _ ty
    | EDeepAccess _ _ ty
    | EApp _ _ ty
    | EIfThenElse _ _ _ ty
    | ELetIn _ _ _ ty => ty
    end.

  Fixpoint typecheck_deep_access (typecheck_expr : renv -> gcontext -> lcontext -> Barocq.expr -> res BarocqTyped.expr)
    (re: renv) (gx: gcontext) (lx: lcontext) (ty: btyp) (acs: list Barocq.access) : res (btyp * list Barocq.Typed.access) :=
    match acs with
    | nil => ret (ty, nil)
    | ac :: acs' =>
        match ac with
        | Barocq.AcRecordField f =>
            let* ty' := typecheck_record_proj re ty f in
            let* (r, lr) := typecheck_deep_access typecheck_expr re gx lx ty' acs' in
            ret (r, (AcRecordField f ty') :: lr)
        | Barocq.AcArrayIndex ei =>
            let* ei' := typecheck_expr re gx lx ei in
            let* ty' := typecheck_array_get arch ty (typof_expr ei') in
            let* (r, lr) := typecheck_deep_access typecheck_expr re gx lx ty' acs' in
            ret (r, (AcArrayIndex ei' ty') :: lr)
        end
    end.

  Fixpoint typecheck_expr (re: renv) (gx: gcontext) (lx: lcontext) (e: Barocq.expr) : res BarocqTyped.expr :=
    match e with
    | Barocq.ETrue => ret (ETrue BBool)
    | Barocq.EFalse => ret (EFalse BBool)
    | Barocq.EInt32 i s => ret (EInt32 i (BInt32 s))
    | Barocq.EInt64 i s => ret (EInt64 i (BInt64 s))
    | Barocq.EVar x =>
        let* t := typof_var gx lx x in
        ret (EVar x t)
    | Barocq.ECast e1 ty =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* t := typecheck_cast (typof_expr e1') ty in
        ret (ECast e1' t)
    | Barocq.EUnaryOp op e1 =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* t := typecheck_unary_op op (typof_expr e1') in
        ret (EUnaryOp op e1' t)
    | Barocq.EBinaryOp op e1 e2 =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* e2' := typecheck_expr re gx lx e2 in
        let* t := typecheck_binary_op op (typof_expr e1') (typof_expr e2') in
        ret (EBinaryOp op e1' e2' t)
    | Barocq.EArrayGet e1 e2 =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* e2' := typecheck_expr re gx lx e2 in
        let* t := typecheck_array_get arch (typof_expr e1') (typof_expr e2') in
        ret (EArrayGet e1' e2' t)
    | Barocq.EArraySet e1 e2 e3 =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* e2' := typecheck_expr re gx lx e2 in
        let* e3' := typecheck_expr re gx lx e3 in
        let* t := typecheck_array_set arch (typof_expr e1') (typof_expr e2') (typof_expr e3') in
        ret (EArraySet e1' e2' e3' t)
    | Barocq.ERecordProj e1 x =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* t := typecheck_record_proj re (typof_expr e1') x in
        ret (ERecordProj e1' x t)
    | Barocq.ERecordUpdate e1 x e2 =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* e2' := typecheck_expr re gx lx e2 in
        let* t := typecheck_record_update re (typof_expr e1') (typof_expr e2') x in
        ret (ERecordUpdate e1' x e2' t)
    | Barocq.EDeepAccess e1 acs =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* (t, acs') := typecheck_deep_access typecheck_expr re gx lx (typof_expr e1') acs in
        ret (EDeepAccess e1' acs' t)
    | Barocq.EApp e1 args =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* args' := mmap (typecheck_expr re gx lx) args in
        let targs := map typof_expr args' in 
        let* t := typecheck_call (typof_expr e1') targs in
        ret (EApp e1' args' t)
    | Barocq.EIfThenElse e1 e2 e3 =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* e2' := typecheck_expr re gx lx e2 in
        let* e3' := typecheck_expr re gx lx e3 in
        let '(ty1, ty2, ty3) := (typof_expr e1', typof_expr e2', typof_expr e3') in
        match ty1 with
        | BBool =>
            if btyp_eq_dec ty2 ty3 then
              ret (EIfThenElse e1' e2' e3' ty2)
            else fail
        | _ => fail
        end
    | Barocq.ELetIn x e1 e2 =>
        let* e1' := typecheck_expr re gx lx e1 in
        let* lx' := lcontext_update lx x (typof_expr e1') in
        let* e2' := typecheck_expr re gx lx' e2 in
        ret (ELetIn x e1' e2' (typof_expr e2'))
    end.

  Definition typecheck_function (arch: Target.archi) (re: renv) (gx: gcontext) (f: Barocq.function) : res BarocqTyped.function :=
    let* lx :=
      fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        (fn_params f)
        (ret tempty)
    in
    let* body := typecheck_expr re gx lx (fn_body f) in
    if btyp_eq_dec (typof_expr body) (fn_return f) then
      ret {|
        fn_return := fn_return f;
        fn_params := fn_params f;
        fn_body := body
      |}
    else failwith "Barocq.Typing.typecheck_function: return type mismatch".

  Fixpoint typecheck_globdefs (re: renv) (gx: gcontext) (defs: list Barocq.globdef) : res (list BarocqTyped.globdef) :=
    match defs with
    | nil => ret nil
    | d :: defs' =>
      match d with
      | Barocq.DefType x fields =>
          let* re' := renv_update re x fields in
          let* rd := typecheck_globdefs re' gx defs' in
          ret ((DefType x fields) :: rd)
      | Barocq.DefConst x l ty =>
          let* l' := typecheck_literal re l in
          if btyp_eq_dec ty (Typing.typof_literal l') then
            let* gx' := gcontext_update gx x ty in
            let* rd := typecheck_globdefs re gx' defs' in
            ret (DefConst x l ty :: rd)
          else
            failwith "Barocq.Typing.typecheck_globdef: type mismatch in constant definition"
      | Barocq.DefFun x f =>
          let* f' := typecheck_function arch re gx f in
          let tf := mk_fun_btyp (fn_params f') (fn_return f') in
          let* gx' := gcontext_update gx x tf in
          let* rd := typecheck_globdefs re gx' defs' in
          ret (DefFun x f' :: rd)
      | Barocq.DeclType t tk =>
          let* rd := typecheck_globdefs re gx defs' in
          ret (DeclType t tk :: rd)
      | Barocq.DeclConst x ty =>
          let* gx' := gcontext_update gx x ty in
          let* rd := typecheck_globdefs re gx' defs' in
          ret (DeclConst x ty :: rd)
      | Barocq.DeclFun x tparams tret =>
          let tf := mk_fun_btyp tparams tret in
          let* gx' := gcontext_update gx x tf in
          let* rd := typecheck_globdefs re gx' defs' in
          ret (DeclFun x tparams tret :: rd)
      end
    end.

  Definition typecheck_program (prog: Barocq.program) : res BarocqTyped.program :=
    typecheck_globdefs tempty tempty prog.

  End ARCHI.

End Typing.

(** * Denotational semantics *)

Section DENOT.

  (** The denotational semantics lifts programs to evaluable Coq terms. *)

  Variable arch : Target.archi.

  Variable abs_typ_impl : PMap.t Type.

  Local Notation eval_typ := (Types.eval_typ abs_typ_impl).

  Inductive value : Type :=
    | Val (t: typ) (v: eval_typ t) : value.

  Inductive access_value : Type :=
   | AcvalRecordField : ident -> access_value
   | AcvalArrayIndex : value -> access_value.

  Definition genv := ptree value.

  Definition lenv := ptree value.

  Definition genv_get (ge: genv) (x: ident) : res value := err_of_opt (tget ge x).

  Definition genv_update (ge: genv) (x: ident) (v: value) : res genv :=
    match genv_get ge x with
    | OK _ => fail
    | Error _ => ret (tset ge x v)
    end.

  Definition lenv_get (le: lenv) (x: ident) : res value :=
    err_of_opt (tget le x).

  Definition lenv_update (le: lenv) (x: ident) (v: value) : lenv :=
    tset le x v.

  Definition eval_var (ge: genv) (le: lenv) (x: ident) : res value :=
    match (lenv_get le x) with
    | OK v => ret v
    | Error _ =>  genv_get ge x
    end.

  Definition eval_cast (v: value) (to: typ) : res value :=
    match v with
    | Val TBool b =>
        match to with
        | TBool => ret (Val TBool b)
        | TInt32 s =>
            let iv := if s then I32.of_bool b else U32.of_bool b in
            ret (Val (TInt32 s) iv)
        | TInt64 s =>
            let iv := if s then I64.of_bool b else U64.of_bool b in
            ret (Val (TInt64 s) iv)
        | _ => fail
        end
    | Val (TInt32 s) i =>
        match to with
        | TBool => 
            if s then ret (Val TBool (I32.to_bool i))
            else ret (Val TBool (U32.to_bool i))
        | TInt32 s' =>
            match s, s' with
            | Signed, Unsigned => ret (Val (TInt32 s') (U32.of_i32 i))
            | Unsigned, Signed => ret (Val (TInt32 s') (I32.of_u32 i))
            | _, _ => ret (Val (TInt32 s') i)
            end
        | TInt64 s' =>
            match s, s' with
            | Signed, Signed => ret (Val (TInt64 s') (I64.of_i32 i))
            | Signed, Unsigned => ret (Val (TInt64 s') (U64.of_i32 i))
            | Unsigned, Signed => ret (Val (TInt64 s') (I64.of_u32 i))
            | Unsigned, Unsigned => ret (Val (TInt64 s') (U64.of_u32 i))
            end
        | _ => fail
        end
    | Val (TInt64 s) i =>
        match to with
        | TBool => 
            if s then ret (Val TBool (I64.to_bool i))
            else ret (Val TBool (U64.to_bool i))
        | TInt32 s' =>
            match s, s' with
            | Signed, Signed => ret (Val (TInt32 s') (I32.of_i64 i))
            | Signed, Unsigned => ret (Val (TInt32 s') (U32.of_i64 i))
            | Unsigned, Signed => ret (Val (TInt32 s') (I32.of_u64 i))
            | Unsigned, Unsigned => ret (Val (TInt32 s') (U32.of_u64 i))
            end
        | TInt64 s' =>
            match s, s' with
            | Signed, Unsigned => ret (Val (TInt64 s') (U64.of_i64 i))
            | Unsigned, Signed => ret (Val (TInt64 s') (I64.of_u64 i))
            | _, _ => ret (Val (TInt64 s') i)
            end
        | _ => fail
        end
    | _ => fail
    end.

  Definition eval_unary_op (op: unary_op) (v: value) : res value :=
    match op, v with
    | UopNotbool, Val TBool b => ret (Val TBool (negb b))
    | UopNotint, Val (TInt32 s) i => ret (Val (TInt32 s) (Int.not i))
    | UopNeg, Val (TInt32 s) i => ret (Val (TInt32 s) (Int.neg i))
    | UopPlus, Val (TInt32 s) i => ret (Val (TInt32 s) i)
    | UopNotint, Val (TInt64 s) i => ret (Val (TInt64 s) (Int64.neg i))
    | UopNeg, Val (TInt64 s) i => ret (Val (TInt64 s) (Int64.not i))
    | UopPlus, Val (TInt64 s) i => ret (Val (TInt64 s) i)
    | _, _ => fail
    end.

  Definition eval_binary_op (op: binary_op) (v1 v2: value) : res value :=
    match op with
    | BopAndbool =>
        match v1, v2 with
        | Val TBool b1, Val TBool b2 => ret (Val TBool (andb b1 b2))
        | _, _ => fail
        end
    | BopOrbool =>
        match v1, v2 with
        | Val TBool b1, Val TBool b2 => ret (Val TBool (orb b1 b2))
        | _, _ => fail
        end
    | BopXorbool =>
        match v1, v2 with
        | Val TBool b1, Val TBool b2 => ret (Val TBool (xorb b1 b2))
        | _, _ => fail
        end
    | BopAdd =>
        match v1, v2 with
        | Val (TInt32 s1) i1, Val (TInt32 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt32 s1) (Int.add i1 i2))
            else fail
        | Val (TInt64 s1) i1, Val (TInt64 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt64 s1) (Int64.add i1 i2))
            else fail
        | _, _ => fail
        end
    | BopSub =>
        match v1, v2 with
        | Val (TInt32 s1) i1, Val (TInt32 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt32 s1) (Int.sub i1 i2))
            else fail
        | Val (TInt64 s1) i1, Val (TInt64 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt64 s1) (Int64.sub i1 i2))
            else fail
        | _, _ => fail
        end
    | BopMul =>
        match v1, v2 with
        | Val (TInt32 s1) i1, Val (TInt32 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt32 s1) (Int.mul i1 i2))
            else fail
        | Val (TInt64 s1) i1, Val (TInt64 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt64 s1) (Int64.mul i1 i2))
            else fail
        | _, _ => fail
        end
    | BopDiv =>
        match v1, v2 with
        | Val (TInt32 Signed) i1, Val (TInt32 Signed) i2 =>
            let* r := I32.div i1 i2 in
            ret (Val (TInt32 Signed) r)
        | Val (TInt32 Unsigned) i1, Val (TInt32 Unsigned) i2 =>
            let* r := U32.div i1 i2 in
            ret (Val (TInt32 Unsigned) r)
        | Val (TInt64 Signed) i1, Val (TInt64 Signed) i2 =>
            let* r := I64.div i1 i2 in
            ret (Val (TInt64 Signed) r)
        | Val (TInt64 Unsigned) i1, Val (TInt64 Unsigned) i2 =>
            let* r := U64.div i1 i2 in
            ret (Val (TInt64 Unsigned) r)
        | _, _ => fail
        end
    | BopMod =>
        match v1, v2 with
        | Val (TInt32 Signed) i1, Val (TInt32 Signed) i2 =>
            let* r := I32.mod i1 i2 in
            ret (Val (TInt32 Signed) r)
        | Val (TInt32 Unsigned) i1, Val (TInt32 Unsigned) i2 =>
            let* r := U32.mod i1 i2 in
            ret (Val (TInt32 Unsigned) (Int.modu i1 i2))
        | Val (TInt64 Signed) i1, Val (TInt64 Signed) i2 =>
            let* r := I64.mod i1 i2 in
            ret (Val (TInt64 Signed) (Int64.mods i1 i2))
        | Val (TInt64 Unsigned) i1, Val (TInt64 Unsigned) i2 =>
            let* r := U64.mod i1 i2 in
            ret (Val (TInt64 Unsigned) r)
        | _, _ => fail
        end
    | BopAndint =>
        match v1, v2 with
        | Val (TInt32 s1) i1, Val (TInt32 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt32 s1) (Int.and i1 i2))
            else fail
        | Val (TInt64 s1) i1, Val (TInt64 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt64 s1) (Int64.and i1 i2))
            else fail
        | _, _ => fail
        end
    | BopOrint =>
        match v1, v2 with
        | Val (TInt32 s1) i1, Val (TInt32 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt32 s1) (Int.or i1 i2))
            else fail
        | Val (TInt64 s1) i1, Val (TInt64 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt64 s1) (Int64.or i1 i2))
            else fail
        | _, _ => fail
        end
    | BopXorint =>
        match v1, v2 with
        | Val (TInt32 s1) i1, Val (TInt32 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt32 s1) (Int.xor i1 i2))
            else fail
        | Val (TInt64 s1) i1, Val (TInt64 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt64 s1) (Int64.xor i1 i2))
            else fail
        | _, _ => fail
        end
    | BopShl =>
        match v1, v2 with
        | Val (TInt32 s1) i1, Val (TInt32 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt32 s1) (Int.shl i1 i2))
            else fail
        | Val (TInt64 s1) i1, Val (TInt64 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val (TInt64 s1) (Int64.shl i1 i2))
            else fail
        | _, _ => fail
        end
    | BopShr =>
        match v1, v2 with
        | Val (TInt32 Signed) i1, Val (TInt32 Signed) i2 =>
            ret (Val (TInt32 Signed) (Int.shr i1 i2))
        | Val (TInt32 Unsigned) i1, Val (TInt32 Unsigned) i2 =>
            ret (Val (TInt32 Unsigned) (Int.shru i1 i2))
        | Val (TInt64 Signed) i1, Val (TInt64 Signed) i2 =>
            ret (Val (TInt64 Signed) (Int64.shr i1 i2))
        | Val (TInt64 Unsigned) i1, Val (TInt64 Unsigned) i2 =>
            ret (Val (TInt64 Unsigned) (Int64.shru i1 i2))
        | _, _ => fail
        end
    | BopEq =>
        match v1, v2 with
        | Val TBool b1, Val TBool b2 => ret (Val TBool (eqb b1 b2))
        | Val (TInt32 s1) i1, Val (TInt32 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val TBool (Int.eq i1 i2))
            else fail
        | Val (TInt64 s1) i1, Val (TInt64 s2) i2 =>
            if signedness_eq_dec s1 s2 then ret (Val TBool (Int64.eq i1 i2))
            else fail
        | _, _ => fail
        end
    | BopNeq =>
        match v1, v2 with
        | Val TBool b1, Val TBool b2 =>
            ret (Val TBool (negb (eqb b1 b2)))
        | Val (TInt32 Signed) i1, Val (TInt32 Signed) i2 =>
            ret (Val TBool (Int.cmp Cne i1 i2))
        | Val (TInt32 Unsigned) i1, Val (TInt32 Unsigned) i2 =>
            ret (Val TBool (Int.cmpu Cne i1 i2))
        | Val (TInt64 Signed) i1, Val (TInt64 Signed) i2 =>
            ret (Val TBool (Int64.cmp Cne i1 i2))
        | Val (TInt64 Unsigned) i1, Val (TInt64 Unsigned) i2 =>
            ret (Val TBool (Int64.cmpu Cne i1 i2))
        | _, _ => fail
        end
    | BopLt =>
        match v1, v2 with
        | Val (TInt32 Signed) i1, Val (TInt32 Signed) i2 =>
            ret (Val TBool (Int.lt i1 i2))
        | Val (TInt32 Unsigned) i1, Val (TInt32 Unsigned) i2 =>
            ret (Val TBool (Int.ltu i1 i2))
        | Val (TInt64 Signed) i1, Val (TInt64 Signed) i2 =>
            ret (Val TBool (Int64.lt i1 i2))
        | Val (TInt64 Unsigned) i1, Val (TInt64 Unsigned) i2 =>
            ret (Val TBool (Int64.ltu i1 i2))
        | _, _ => fail
        end
    | BopGt =>
        match v1, v2 with
        | Val (TInt32 Signed) i1, Val (TInt32 Signed) i2 =>
            ret (Val TBool (Int.cmp Cge i1 i2))
        | Val (TInt32 Unsigned) i1, Val (TInt32 Unsigned) i2 =>
            ret (Val TBool (Int.cmpu Cge i1 i2))
        | Val (TInt64 Signed) i1, Val (TInt64 Signed) i2 =>
            ret (Val TBool (Int64.cmp Cge i1 i2))
        | Val (TInt64 Unsigned) i1, Val (TInt64 Unsigned) i2 =>
            ret (Val TBool (Int64.cmpu Cge i1 i2))
        | _, _ => fail
        end
    | BopLe =>
        match v1, v2 with
        | Val (TInt32 Signed) i1, Val (TInt32 Signed) i2 =>
            ret (Val TBool (Int.cmp Cle i1 i2))
        | Val (TInt32 Unsigned) i1, Val (TInt32 Unsigned) i2 =>
            ret (Val TBool (Int.cmpu Cle i1 i2))
        | Val (TInt64 Signed) i1, Val (TInt64 Signed) i2 =>
            ret (Val TBool (Int64.cmp Cle i1 i2))
        | Val (TInt64 Unsigned) i1, Val (TInt64 Unsigned) i2 =>
            ret (Val TBool (Int64.cmpu Cle i1 i2))
        | _, _ => fail
        end
    | BopGe =>
        match v1, v2 with
        | Val (TInt32 Signed) i1, Val (TInt32 Signed) i2 =>
            ret (Val TBool (Int.cmp Cge i1 i2))
        | Val (TInt32 Unsigned) i1, Val (TInt32 Unsigned) i2 =>
            ret (Val TBool (Int.cmpu Cge i1 i2))
        | Val (TInt64 Signed) i1, Val (TInt64 Signed) i2 =>
            ret (Val TBool (Int64.cmp Cge i1 i2))
        | Val (TInt64 Unsigned) i1, Val (TInt64 Unsigned) i2 =>
            ret (Val TBool (Int64.cmpu Cge i1 i2))
        | _, _ => fail
        end
    end.

  Fixpoint eval_array_lit (a: array value) : res value :=
    match a with
    | nil => fail
    | Val tx x :: nil => ret (Val (TArray tx) (x :: nil))
    | Val tx x :: a' =>
        let* va := eval_array_lit a' in
        match va with
        | Val (TArray ta) xa =>
            match (typ_eq_dec tx ta) with
            | left eq =>
                ret (Val (TArray ta) ((typ_cast abs_typ_impl eq x) :: xa))
            | _ => fail
            end
        | _ => fail
        end
    end.

  Fixpoint eval_record_lit_rec (lv: list (ident * value)) (fields: list (ident * typ)) : res (eval_recordtyp eval_typ fields).
    destruct lv as [|[x [tv v]] lv'] eqn:Elv; destruct fields as [| [y t] fields'] eqn:Efields.
    - apply (ret tt).
    - apply fail.
    - apply fail.
    - destruct (Ident.eq_dec x y).
      + subst. destruct (typ_eq_dec tv t).
        * subst. destruct (eval_record_lit_rec lv' fields') as [rc |].
          -- unfold eval_recordtyp in *. simpl in *.
             apply (ret (Field y v, rc)).
          -- apply fail.
        * apply fail.
      + apply fail.
  Defined.

  Definition eval_record_lit (n: ident) (lv: list (ident * value)) (fields: list (ident * typ)) : res value.
    destruct lv as [|x lv'].
    - apply fail.
    - destruct (eval_record_lit_rec (x :: lv') fields) as [r |].
      * apply (ret (Val (TRecord n fields) r)).
      * apply fail.
  Defined.

  Definition eval_array_get (v1 v2: value) : res value.
    destruct v1 as [ta a]. destruct v2 as [t2 i].
    destruct ta.
    4:
    {
      destruct arch eqn:Earch.
        - destruct (typ_eq_dec t2 (TInt32 Unsigned)).
          + subst. simpl in i. simpl in a.
            destruct (Barray.get a (U64.of_u32 i)).
              * apply (ret (Val ta e)).
              * apply fail.
          + apply fail.
        - destruct (typ_eq_dec t2 (TInt64 Unsigned)).
          + subst. simpl in i. simpl in a. destruct (Barray.get a i).
            * apply (ret (Val ta e)).
            * apply fail. 
          + apply fail.
    }
    all: apply fail.
  Defined.

  Definition eval_array_set (v1 v2 v3: value) : res value.
    destruct v1 as [ta a]. destruct v2 as [t2 i]. destruct v3 as [t v].
    destruct ta.
    4 :
    {
      destruct arch eqn:Earch.
      - destruct (typ_eq_dec t2 (TInt32 Unsigned)).
        + destruct (typ_eq_dec ta t).
          * subst. simpl in i. simpl in a. destruct (Barray.set a (U64.of_u32 i) v).
            -- apply (ret (Val (TArray t) a0)).
            -- apply fail.
          * apply fail.
        + apply fail.
      - destruct (typ_eq_dec t2 (TInt64 Unsigned)).
        + destruct (typ_eq_dec ta t).
          * subst. simpl in i. simpl in a. destruct (Barray.set a i v).
            -- apply (ret (Val (TArray t) a0)).
            -- apply fail.
          * apply fail.
        + apply fail.
    }
    all: apply fail.
  Defined.

  Lemma typof_field_is_type :
    forall (fields: list (ident * typ)) k t,
    typof_field k fields = OK t ->
    eval_typ t = type_of_field k (eval_fields_typ eval_typ fields).
  Proof.
    induction fields as [| (x, t) fields']; intros.
    - simpl in H. discriminate.
    - unfold typof_field in *. unfold find_k_err in *.
      unfold type_of_field in *. unfold find_k in *.
      simpl. simpl in H. unfold Ident.eq_dec in H.
      unfold key_eq_dec. destruct (Pos.eq_dec x k).
      + inversion H. reflexivity.
      + apply (IHfields' k t0 H). 
  Defined.

  Definition eval_record_proj_aux (fields: list (ident * typ)) (rc: eval_recordtyp eval_typ fields) (k: ident) : res value.
    simpl in rc. destruct (proj rc k) as [v |].
    - destruct (typof_field k fields) as [t |] eqn:Etyp.
      + rewrite <- (typof_field_is_type fields k t Etyp) in v.
        apply (ret (Val t v)).
      + apply fail.
    - apply fail.
  Defined.

  Definition eval_record_proj (v: value) (k: ident) : res value :=
    match v with
    | Val (TRecord _ fields) st => eval_record_proj_aux fields st k
    | _ => fail
    end.

  Definition eval_record_update_aux (n: ident) (fields: list (ident * typ)) (rc: eval_typ (TRecord n fields)) (k: ident) (v: value) : res value.
    simpl in rc. destruct v as [tv v]. destruct (typof_field k fields) as [t |] eqn:Etyp.
    - destruct (typ_eq_dec tv t) as [Eqt |_].
      + apply (typof_field_is_type fields k t) in Etyp.
        rewrite Eqt in v. rewrite Etyp in v.
        destruct (update rc k v) as [rc' |].
        * apply (ret (Val (TRecord n fields) rc')).
        * apply fail.
      + apply fail.
    - apply fail.
  Defined.

  Definition eval_record_update (v1: value) (k: ident) (v2: value) : res value :=
    match v1 with
    | Val (TRecord n fields) st => eval_record_update_aux n fields st k v2
    | _ => fail
    end.

  Fixpoint eval_access_list (v: value) (acs: list access_value) {struct acs} : res value :=
    match acs with
    | nil => OK v
    | ac :: acs' =>
        match ac with
        | AcvalRecordField f =>
            let* v' := eval_record_proj v f in
            eval_access_list v' acs'
        | AcvalArrayIndex va =>
            let* v' := eval_array_get v va in
            eval_access_list v' acs'
        end
    end.
    
  Definition eval_ifthenelse (v1 v2 v3: value) : res value :=
    match v1 with
    | Val TBool b => ret (if b then v2 else v3)
    | _ => fail
    end.

  Fixpoint eval_app_rec (tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams tret) (args: list value) : res value.
    destruct tparams as [| t tparams']; destruct args as [| [tv v] args'].
    - simpl in f. destruct f as [v |].
      + apply (ret (Val tret v)).
      + apply (Error e).
    - apply fail.
    - apply fail.
    - simpl in f. destruct (typ_eq_dec tv t) as [Heqtv | _].
      + apply (eval_app_rec tparams' tret (f (typ_cast abs_typ_impl Heqtv v)) args').
      + apply fail.
  Defined.

  Definition eval_app (v: value) (args: list value) : res value.
    destruct v as [t vt]. destruct t as [ | | | | fields | tparams tret | t].
    - apply fail.
    - apply fail.
    - apply fail.
    - apply fail.
    - apply fail.
    - destruct tparams as [|t tparams'] eqn:Etparams; destruct args as [|a args'] eqn:Eargs.
      + simpl in vt. specialize (vt tt). destruct vt.
        -- apply (ret (Val tret e)).
        -- apply (Error e).
      + apply fail.
      + apply fail.
      + simpl in vt. apply (eval_app_rec (t :: tparams') tret vt (a :: args')).
    - apply fail. 
  Defined.

  Fixpoint eval_expr (te: tenv) (ge: genv) (le: lenv) (e: expr) : res value :=
    match e with
    | ETrue => ret (Val TBool true)
    | EFalse => ret (Val TBool false)
    | EInt32 i s => ret (Val (TInt32 s) i)
    | EInt64 i s => ret (Val (TInt64 s) i)
    | EVar x => eval_var ge le x
    | ECast e1 ty =>
        let* ty' := btyp_to_typ te ty in
        let* v1 := eval_expr te ge le e1 in
        eval_cast v1 ty'
    | EUnaryOp op e =>
        let* v := eval_expr te ge le e in
        eval_unary_op op v
    | EBinaryOp op e1 e2 =>
        let* v1 := eval_expr te ge le e1 in
        let* v2 := eval_expr te ge le e2 in
        eval_binary_op op v1 v2
    | EArrayGet e1 e2 =>
        let* v1 := eval_expr te ge le e1 in
        let* v2 := eval_expr te ge le e2 in
        eval_array_get v1 v2
    | EArraySet e1 e2 e3 =>
        let* v1 := eval_expr te ge le e1 in
        let* v2 := eval_expr te ge le e2 in
        let* v3 := eval_expr te ge le e3 in
        eval_array_set v1 v2 v3
    | ERecordProj e k =>
        let* v := eval_expr te ge le e in
        eval_record_proj v k
    | ERecordUpdate e1 k e2 =>
        let* v1 := eval_expr te ge le e1 in
        let* v2 := eval_expr te ge le e2 in
        eval_record_update v1 k v2
    | EDeepAccess e1 acs =>
        let* v1 := eval_expr te ge le e1 in
        let* vacs := mmap (eval_access_expr te ge le) acs in
        eval_access_list v1 vacs
    | EApp v args =>
        let* f := eval_expr te ge le v in
        let* vargs := mmap (eval_expr te le ge) args
        in eval_app f vargs
    | EIfThenElse e1 e2 e3 =>
        let* v1 := eval_expr te ge le e1 in
        let* v2 := eval_expr te ge le e2 in
        let* v3 := eval_expr te ge le e3 in
        eval_ifthenelse v1 v2 v2
    | ELetIn x e1 e2 =>
        let* v1 := eval_expr te ge le e1 in
        let '(Val tv v) := v1 in
        let le' := lenv_update le x v1 in
        eval_expr te ge le' e2
    end

  with eval_access_expr (te: tenv) (ge: genv) (le: lenv) (ac: access) : res access_value :=
    match ac with
    | AcRecordField f => ret (AcvalRecordField f)
    | AcArrayIndex e =>
        let* v := eval_expr te ge le e in
        ret (AcvalArrayIndex v)
    end.

  Fixpoint eval_literal (te: tenv) (l: literal) : res value :=
    match l with
    | LTrue => ret (Val TBool true)
    | LFalse => ret (Val TBool false)
    | LInt32 i s => ret (Val (TInt32 s) i)
    | LInt64 i s => ret (Val (TInt64 s) i)
    | LArray a =>
        let* av := mmap (eval_literal te) a in
        eval_array_lit av
    | LRecord rc x =>
        let* rcv := map_k_err (eval_literal te) rc in
        let* fields := tenv_get te x in
        eval_record_lit x rcv fields
    end.

  Fixpoint build_funval_rec_aux (te: tenv) (ge: genv) (le: lenv) (params: list (ident * typ)) (tret: typ) (e: expr) : eval_funtyp eval_typ (map (fun x => snd x) params) tret.
    destruct params as [| (x, tx) params'].
    - simpl. destruct (eval_expr te ge le e) as [[tv v]|].
      + destruct (typ_eq_dec tv tret).
        * apply (ret (typ_cast abs_typ_impl e0 v)).
        * apply fail.
      + apply (Error e0).
    - simpl. apply (fun (y: eval_typ tx) => build_funval_rec_aux te ge (lenv_update le x (Val tx y)) params' tret e).
  Defined.

  Definition build_funval_rec := Eval cbv delta [build_funval_rec_aux] zeta beta in build_funval_rec_aux.

  Definition build_funval (te: tenv) (ge: genv) (params: list (ident * typ)) (tret: typ) (e: expr) : eval_typ (TFun (map (fun x => snd x) params) tret).
    destruct params as [| p params'].
    - simpl. destruct (eval_expr te ge tempty e) as [[tv v] |].
      + destruct (typ_eq_dec tv tret).
        -- simpl. apply (fun (_: unit) => ret (typ_cast abs_typ_impl e0 v)).
        -- apply (fun (_: unit) => fail).
      + apply (fun (_: unit) => (Error e0)).
    - apply (build_funval_rec te ge tempty (p :: params') tret e).
  Defined.

  Definition build_fun_value (te: tenv) (ge: genv) (params: list (ident * btyp)) (tret: btyp) (e: expr) : res value :=
    if nodup_k Ident.eq_dec params then
      let* tret' := btyp_to_typ te tret in
      let* params' := map_k_err (btyp_to_typ te) params in
      ret (Val (TFun (map (fun x => snd x) params') tret') (build_funval te ge params' tret' e))
    else fail.

  Definition fields_btyp_to_typ (te: tenv) (fields: list (ident * btyp)) : res (list (ident * typ)) :=
    map_k_err (btyp_to_typ te) fields.

  Fixpoint interpret_rec (te: tenv) (ge: genv) (cmds: list Barocq.command) : res (list value) :=
    match cmds with
    | nil => ret nil
    | c :: xprog' =>
        match c with
        | CmdDef (DefType a fields) =>
            let* fields' := fields_btyp_to_typ te fields in
            let* te' := tenv_update te a fields' in
            interpret_rec te' ge xprog'
        | CmdDef (DefConst x l ty) =>
            let* vv := eval_literal te l in
            let '(Val tv v) := vv in
            let* ty' := btyp_to_typ te ty in
            if typ_eq_dec tv ty' then
              let* ge' := genv_update ge x vv in
              interpret_rec te ge' xprog'
            else fail
        | CmdDef (DefFun x f) =>
            let* fv := build_fun_value te ge (fn_params f) (fn_return f) (fn_body f) in
            let* ge' := genv_update ge x fv in
            interpret_rec te ge' xprog'
        | CmdDef (DeclType _ _) => failwith "the program contains abstract types"
        | CmdDef (DeclConst _ _)
        | CmdDef (DeclFun _ _ _) => failwith "the program contains abstract definitions"
        | CmdExpr e =>
            let* v := eval_expr te ge tempty e in
            let* l := interpret_rec te ge xprog' in
            ret (v :: l)
        end
    end.

  Definition interpret (iprog: iprogram) : res (list value) :=
    interpret_rec tempty tempty iprog.

  Fixpoint eval_def_rec (te: tenv) (ge: genv) (prog: Barocq.program) (x: ident) : res value :=
    match prog with
    | nil => fail
    | d :: prog' =>
        match d with
        | DefType a fields =>
            let* fields' := fields_btyp_to_typ te fields in
            let* te' := tenv_update te a fields' in
            eval_def_rec te' ge prog' x
        | DefConst y l ty =>
            let* vv := eval_literal te l in
            if Ident.eq_dec x y then ret vv
            else
              let '(Val tv v) := vv in
              let* ty' := btyp_to_typ te ty in
              if typ_eq_dec tv ty' then
                let* ge' := genv_update ge y vv in
                eval_def_rec te ge' prog' x
              else fail
        | DefFun y f =>
            let* fv := build_fun_value te ge (fn_params f) (fn_return f) (fn_body f) in
            if Ident.eq_dec x y then ret fv
            else
              let* ge' := genv_update ge y fv in
              eval_def_rec te ge' prog' x
        | DeclType _ _ => eval_def_rec te ge prog' x
        | DeclConst y _
        | DeclFun y _ _ =>
            if Ident.eq_dec x y then genv_get ge x
            else eval_def_rec te ge prog' x
        end
    end.

  Definition eval_value_err_typ (rv: res value) : Type :=
    match rv with
    | OK (Val tv v) => eval_typ tv
    | Error _ => unit
    end.

  Definition eval_def (impl: genv) (prog: program) (x: ident) : res value :=
    eval_def_rec tempty impl prog x.

End DENOT.
