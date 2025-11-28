From Coq Require Import List String ListDec PArith Bool.
From compcert Require Import Coqlib Integers Maps Ctypes.
From BarocqComp Require Import Error Maps2 Utils Intop Barray Brecord Benum Types Typing Syntax.
From BarocqComp Require  DList.
Import ListNotations.


(** * Abstract syntax *)

(** ** Expressions *)

Inductive expr : Type :=
  | ETrue : expr                                             (* true constant *)
  | EFalse : expr                                            (* false constant *)
  | EInt32 (i: int) (s: signedness) : expr                   (* 32-bit signed or unsigned integer *)
  | EInt64 (i: int64) (s: signedness) : expr                 (* 64-bit signed orunsigned integer *)
  | EConstr (x: ident) : expr                                (* enum constructor *)  
  | EVar (x: ident) : expr                                   (* variable *)
  | ECast (e: expr) (ty: btyp)                               (* e as ty *)
  | EUnaryOp (op: unary_op) (e: expr) : expr                 (* op e *)
  | EBinaryOp (op: binary_op) (e1 e2 : expr) : expr          (* e1 op e2 *)
  | EArrayGet (a i: expr) : expr                             (* a[i] *)
  | EArraySet (a i e: expr) : expr                           (* a[i] <- e *)
  | ERecordProj (st: expr) (f: ident) : expr                 (* st.f *)
  | ERecordUpdate (st: expr) (f: ident) (e: expr) : expr     (* st.f <- e *)
  (*| EDeepAccess (e: expr) (acs: list access) : expr        (* eX1X2....Xn where Xi = .fi or [ei] *) *)
  | EApp (e: expr) (args: list expr) : expr                  (* e(args) *)
  | EIfThenElse (e1 e2 e3: expr) : expr                      (* if e1 then e2 else e3 *)
  | EMatch (e: expr) (cases: list (pattern * expr)) : expr   (* match e with V1 -> e1 ... | Vn -> en end *)    
  | ELetIn (x: ident) (e1 e2: expr) : expr                   (* let x = e1 in e2 *)

with access : Type :=
  | AcRecordField : ident -> access
  | AcArrayIndex : expr -> access.

(** ** Functions *)

Definition function : Type := Syntax.function expr btyp.

(** ** Global definitions *)

Inductive globdef : Type :=
  | DefType (tid: ident) (td: type_def field_descr) : globdef                       (* type tid = ... *)
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
    | ETrue : expr
    | EFalse : expr
    | EInt32 : int -> signedness -> expr
    | EInt64 : int64 -> signedness -> expr
    | EConstr : ident -> btyp -> expr
    | EVar : ident -> btyp -> expr
    | ECast : expr -> btyp -> expr
    | EUnaryOp : unary_op -> expr -> btyp -> expr
    | EBinaryOp : binary_op -> expr -> expr -> btyp -> expr
    | EArrayGet : expr -> expr -> btyp -> expr
    | EArraySet : expr -> expr -> expr -> btyp -> expr
    | ERecordProj : expr -> ident -> btyp -> expr
    | ERecordUpdate : expr -> ident -> expr -> btyp -> expr
    (* | EDeepAccess : expr -> list access -> btyp -> expr *)
    | EApp : expr -> list expr -> btyp -> expr
    | EIfThenElse : expr -> expr -> expr -> btyp -> expr
    | EMatch : expr -> list (pattern * expr) -> btyp -> expr
    | ELetIn : ident -> expr -> expr -> btyp -> expr

  (* An access is associated with a type.
     For every deep access e.X1X2...Xn, Xi has type ty
     iff the expression e.X1...X(i-1)Xi has type ty. *)
  with access : Type :=
    | AcRecordField : ident -> btyp -> access
    | AcArrayIndex : expr -> btyp -> access.

  (** ** Functions *)

  Definition function : Type := Syntax.function expr btyp.

  (** ** Global definitions *)

  Inductive globdef : Type :=
    | DefType : ident -> type_def field_descr -> globdef
    | DefConst : ident -> literal -> btyp -> globdef
    | DefFun : ident -> function -> globdef
    | DeclType : ident -> struct_or_union -> globdef
    | DeclConst : ident -> btyp -> globdef
    | DeclFun : ident -> list (param_attr * btyp) -> btyp -> globdef.

  (** ** Programs *)

  Definition program := list globdef.

  Inductive command : Type :=
  | CmdDef (def: globdef) : command      (* top level definition *)
  | CmdExpr (ty:btyp) (e: expr) : command.         (* top level expression to be evaluated *)

  Definition iprogram := list command.

End Typed.

Module BarocqTyped := Barocq.Typed.

Module Typing.

  Import BarocqTyped.

  Section ARCHI.

  Variable arch : Target.archi.

  Definition typof_expr (e: expr) : btyp :=
    match e with
    | ETrue | EFalse => BBool
    | EInt32 _ s     => BInt32 s
    | EInt64 _ s     => BInt64 s
    | EConstr _ ty
    | EVar _ ty
    | ECast _ ty
    | EUnaryOp _ _ ty
    | EBinaryOp _ _ _ ty
    | EArrayGet _ _ ty
    | EArraySet _ _ _ ty
    | ERecordProj _ _ ty
    | ERecordUpdate _ _ _ ty
    (* | EDeepAccess _ _ ty *)
    | EMatch _ _ ty 
    | EApp _ _ ty
    | EIfThenElse _ _ _ ty
    | ELetIn _ _ _ ty => ty
    end.

  (* Fixpoint typecheck_deep_access (typecheck_expr : benv -> gcontext -> lcontext -> Barocq.expr -> res BarocqTyped.expr)
    (be: benv) (gx: gcontext) (lx: lcontext) (ty: btyp) (acs: list Barocq.access) : res (btyp * list Barocq.Typed.access) :=
    match acs with
    | nil => ret (ty, nil)
    | ac :: acs' =>
        match ac with
        | Barocq.AcRecordField f =>
            let* ty' := typecheck_record_proj be ty f in
            let* (r, lr) := typecheck_deep_access typecheck_expr be gx lx ty' acs' in
            ret (r, (AcRecordField f ty') :: lr)
        | Barocq.AcArrayIndex ei =>
            let* ei' := typecheck_expr be gx lx ei in
            let* ty' := typecheck_array_get arch ty (typof_expr ei') in
            let* (r, lr) := typecheck_deep_access typecheck_expr be gx lx ty' acs' in
            ret (r, (AcArrayIndex ei' ty') :: lr)
        end
    end. *)

  Fixpoint typecheck_expr (be: benv) (gx: gcontext) (lx: lcontext) (e: Barocq.expr) : res BarocqTyped.expr :=
    match e with
    | Barocq.ETrue => ret ETrue
    | Barocq.EFalse => ret EFalse
    | Barocq.EInt32 i s => ret (EInt32 i s)
    | Barocq.EInt64 i s => ret (EInt64 i s)
    | Barocq.EConstr x =>
        let* t := typof_constr be x in
        ret (EConstr x t)
    | Barocq.EVar x =>
        let* t := typof_var gx lx x in
        ret (EVar x t)
    | Barocq.ECast e1 ty =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* t := typecheck_cast (typof_expr e1') ty in
        ret (ECast e1' t)
    | Barocq.EUnaryOp op e1 =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* t := typecheck_unary_op op (typof_expr e1') in
        ret (EUnaryOp op e1' t)
    | Barocq.EBinaryOp op e1 e2 =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* e2' := typecheck_expr be gx lx e2 in
        let* t := typecheck_binary_op op (typof_expr e1') (typof_expr e2') in
        ret (EBinaryOp op e1' e2' t)
    | Barocq.EArrayGet e1 e2 =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* e2' := typecheck_expr be gx lx e2 in
        let* t := typecheck_array_get arch (typof_expr e1') (typof_expr e2') in
        ret (EArrayGet e1' e2' t)
    | Barocq.EArraySet e1 e2 e3 =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* e2' := typecheck_expr be gx lx e2 in
        let* e3' := typecheck_expr be gx lx e3 in
        let* t := typecheck_array_set arch (typof_expr e1') (typof_expr e2') (typof_expr e3') in
        ret (EArraySet e1' e2' e3' t)
    | Barocq.ERecordProj e1 x =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* t := typecheck_record_proj be (typof_expr e1') x in
        ret (ERecordProj e1' x t)
    | Barocq.ERecordUpdate e1 x e2 =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* e2' := typecheck_expr be gx lx e2 in
        let* t := typecheck_record_update be (typof_expr e1') (typof_expr e2') x in
        ret (ERecordUpdate e1' x e2' t)
    (* | Barocq.EDeepAccess e1 acs =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* (t, acs') := typecheck_deep_access typecheck_expr be gx lx (typof_expr e1') acs in
        ret (EDeepAccess e1' acs' t) *)
    | Barocq.EApp e1 args =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* args' := mmap (typecheck_expr be gx lx) args in
        let targs := List.map typof_expr args' in 
        let* t := typecheck_call (typof_expr e1') targs in
        ret (EApp e1' args' t)
    | Barocq.EIfThenElse e1 e2 e3 =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* e2' := typecheck_expr be gx lx e2 in
        let* e3' := typecheck_expr be gx lx e3 in
        let '(ty1, ty2, ty3) := (typof_expr e1', typof_expr e2', typof_expr e3') in
        match ty1 with
        | BBool =>
            if btyp_eq_dec ty2 ty3 then
              ret (EIfThenElse e1' e2' e3' ty2)
            else fail
        | _ => fail
        end
    | Barocq.EMatch e1 cases =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* cases' := MapList.map_err (typecheck_expr be gx lx) cases in
        let tcases' := MapList.map typof_expr cases' in
        let* t := typecheck_match be (typof_expr e1') tcases' in
        ret (EMatch e1' cases' t)
    | Barocq.ELetIn x e1 e2 =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* lx' := lcontext_update lx x (typof_expr e1') in
        let* e2' := typecheck_expr be gx lx' e2 in
        ret (ELetIn x e1' e2' (typof_expr e2'))
    end.

  Definition typecheck_function (arch: Target.archi) (be: benv) (gx: gcontext) (f: Barocq.function) : res BarocqTyped.function :=
    let* lx :=
      list_fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        (fn_params f)
        (ret STree.empty)
    in
    let* body := typecheck_expr be gx lx (fn_body f) in
    if btyp_eq_dec (typof_expr body) (fn_return f) then
      ret {|
        fn_return := fn_return f;
        fn_params := fn_params f;
        fn_body := body
      |}
    else failwith "Barocq.Typing.typecheck_function: return type mismatch".

  Definition typecheck_globdef (be:benv) (gx:gcontext) (d: Barocq.globdef) : res (benv * gcontext * BarocqTyped.globdef) :=
    match d with
    | Barocq.DefType x td =>
        let* be' := TEnv.update_defs be x td in
        ret (be', gx, (DefType x td))
    | Barocq.DefConst x l ty =>
        let* l' := typecheck_literal be l in
        if btyp_eq_dec ty (Typing.typof_literal l') then
          let* gx' := gcontext_update gx x ty in
          ret (be,gx',DefConst x l ty)
        else
          failwith "Barocq.Typing.typecheck_globdef: type mismatch in constant definition"
      | Barocq.DefFun x f =>
          let* f' := typecheck_function arch be gx f in
          let tf := mk_fun_btyp (fn_params f') (fn_return f') in
          let* gx' := gcontext_update gx x tf in
          ret (be,gx',DefFun x f')
      | Barocq.DeclType t tk =>
          ret (be,gx,DeclType t tk)
      | Barocq.DeclConst x ty =>
          let* gx' := gcontext_update gx x ty in
          ret (be,gx',DeclConst x ty)
      | Barocq.DeclFun x tparams tret =>
          let tf := mk_fun_btyp tparams tret in
          let* gx' := gcontext_update gx x tf in
          ret (be,gx',DeclFun x tparams tret)
    end.

  Fixpoint typecheck_globdefs (be: benv) (gx: gcontext) (defs: list Barocq.globdef) : res (list BarocqTyped.globdef) :=
    match defs with
    | nil => ret nil
    | d :: defs' =>
        let* gd := typecheck_globdef be gx d in
        let '(be',gx',d') := gd in
        let* rd :=typecheck_globdefs be' gx' defs' in
        ret (d':: rd)
    end.

  Definition typecheck_program (prog: Barocq.program) : res BarocqTyped.program :=
    typecheck_globdefs TEnv.empty STree.empty prog.

  Definition typecheck_command (be:benv) (gx: gcontext) (cmd : Barocq.command) : res (benv * gcontext * BarocqTyped.command) :=
    match  cmd with
    | Barocq.CmdDef gd => let* gd := typecheck_globdef be gx gd in
                   let '(be',gx',d') := gd in
                   OK (be',gx',CmdDef d')
    | Barocq.CmdExpr e =>
        let* e := typecheck_expr be gx STree.empty e in
        let bt := typof_expr e in
        OK(be,gx,CmdExpr bt e)
    end.

  Fixpoint typecheck_commands (be:benv) (gx:gcontext) (prog: Barocq.iprogram) : res BarocqTyped.iprogram :=
    match prog with
    | nil => ret nil
    | d :: defs' =>
        let* gd := typecheck_command be gx d in
        let '(be',gx',d') := gd in
        let* rd :=typecheck_commands be' gx' defs' in
        ret (d':: rd)
    end.

  Definition typecheck_iprogram (prog: Barocq.iprogram) : res BarocqTyped.iprogram :=
    typecheck_commands TEnv.empty STree.empty prog.

  Fixpoint program_of_iprogram (p: BarocqTyped.iprogram) : BarocqTyped.program :=
    match p with
    | nil => nil
    | CmdDef d::l => d :: program_of_iprogram l
    | CmdExpr e _ ::l => program_of_iprogram l
    end.

  End ARCHI.

End Typing.

(** * Denotational semantics *)

Section DENOT.
  Import Typed.
  (** The denotational semantics lifts programs to evaluable Coq terms. *)

  Variable arch : Target.archi.

  Variable abs_typ_impl : PMap.t Type.

  Local Notation eval_typ := (Types.eval_typ abs_typ_impl).

  Inductive value : Type :=
    | Val (t: typ) (v: eval_typ t) : value.

  Definition typof_index : typ :=
    match arch with
    | Target.Ptr32 => TInt32 Unsigned
    | Target.Ptr64 => TInt64 Unsigned
    end.

  Inductive access_value : Type :=
   | AcvalRecordField : ident -> access_value
   | AcvalArrayIndex : res (eval_typ typof_index) -> access_value.

  Definition genv := STree.t value.

  Definition lenv := STree.t value.

  Definition genv_get (ge: genv) (x: ident) : res value :=
    err_of_opt (STree.get x ge).

  Definition genv_update (ge: genv) (x: ident) (v: value) : res genv :=
    match genv_get ge x with
    | OK _ => fail
    | Error _ => ret (STree.set x v ge)
    end.

  Definition lenv_get (le: lenv) (x: ident) : res value :=
    err_of_opt (STree.get x le).

  Definition lenv_update (le: lenv) (x: ident) (v: value) : lenv :=
    STree.set x v le.

  Definition cast_typ  {t2:typ} (v: eval_typ t2) (t1:typ): res (eval_typ t1).
  Proof.
    destruct (typ_eq_dec t1 t2).
    subst. exact (OK v).
    apply fail.
  Defined.

  Definition ecast_typ  {t2:typ} (v: res (eval_typ t2)) (t1:typ): res (eval_typ t1).
  Proof.
    destruct (typ_eq_dec t1 t2).
    - subst. exact v.
    - apply fail.
  Defined.


  Definition cast_value  (v:value) (t1:typ) : res (eval_typ t1).
  Proof.
    destruct v.
    apply (cast_typ v t1).
  Defined.

  Definition eval_var  (ge: genv) (le: lenv) (x: ident) (ty:typ) : res (eval_typ ty) :=
    match (lenv_get le x) with
    | OK v => cast_value  v ty
    | Error _ => let* v := genv_get ge x in
                 cast_value v ty
    end.

  Definition eval_constr  (te: tenv) (x: ident) (ty:typ) : res (eval_typ ty) :=
    let* eid := TEnv.get_constr_typ te x in
    let* elems := TEnv.get_edef te eid in
    match (bool_dec (existsb (String.eqb x) elems) true) with
    | left EQ =>  @cast_typ (TEnum eid elems)   (mk_enum elems x EQ) ty
    | right _ => fail
    end.

  Definition partial {A B: Type} (F : A -> B) : A -> res B :=
    fun x => OK (F x).

  Definition partial2 {A B C: Type} (F : A -> B -> C) : A -> B -> res C :=
    fun x y => OK (F x y).


  Definition get_cast (ty:typ) (ty':typ) : res (eval_typ ty -> res (eval_typ ty')) :=
    match ty, ty' with
      (* TBool *)
    | TBool , TBool => OK (fun x => OK x)
    | TBool , TInt32 s => OK (partial (if s then I32.of_bool else U32.of_bool))
    | TBool , TInt64 s => OK (partial (if s then I64.of_bool else U64.of_bool))
    | TBool , TEnum eid elems => OK (fun x => Benum.of_i32 elems (I32.of_bool x))
       (* TInt32 *)
    | TInt32 s , TBool =>  OK (partial (if s then I32.to_bool else U32.to_bool))
    | TInt32 s , TInt32 s' => OK (partial (match s , s' with
                                              | Signed , Unsigned => U32.of_i32
                                              | Unsigned , Signed => I32.of_u32
                                              |  _       ,   _    => fun x => x
                                              end))
    | TInt32 s , TInt64 s' => OK (partial (match s, s' with
                                              | Signed, Signed => I64.of_i32
                                              | Signed, Unsigned => U64.of_i32
                                              | Unsigned, Signed => I64.of_u32
                                              | Unsigned, Unsigned => U64.of_u32
                                              end))
    | TInt32 s ,  TEnum eid elems => OK (fun x => Benum.of_i32 elems (if s then x else I32.of_u32 x))
                 (*  Tint64 *)
    | TInt64 s , TBool => OK (partial (if s then I64.to_bool else U64.to_bool))
    | TInt64 s , TInt32 s' => OK (partial (
                                      match s, s' with
                                      | Signed, Signed =>  I32.of_i64
                                      | Signed, Unsigned => U32.of_i64
                                      | Unsigned, Signed => I32.of_u64
                                      | Unsigned, Unsigned => U32.of_u64
                                      end))
    | TInt64 s ,  TInt64 s' => OK (partial (
                                       match s, s' with
                                       | Signed, Unsigned => U64.of_i64
                                       | Unsigned, Signed => I64.of_u64
                                       | _, _ => fun x => x
                                       end))
    | TInt64 s , TEnum eid elems => OK (fun x => Benum.of_i32 elems (if s then I32.of_i64 x else I32.of_u64 x))
            (* Tenum *)
    | TEnum tid elems , TBool  => OK (partial (fun x => I32.to_bool (Benum.to_i32 x)))
    | TEnum tid elems , TInt32 s => OK (partial (fun x => if s then Benum.to_i32 x else U32.of_i32 (Benum.to_i32 x)))
    | TEnum tid elems , TInt64 s => OK (partial (fun x => if s then I64.of_i32 (Benum.to_i32 x)
                                                          else  U64.of_i32 (Benum.to_i32 x)))
    | _ , _ => fail
    end.

  Definition eval_cast (ty:typ) (v1:eval_typ ty) (tr:typ) : res (eval_typ tr) :=
    let* f := get_cast ty tr in f  v1.

  Definition eval_unary_op (op: unary_op) (ty:typ) : forall (v: eval_typ ty) (tyr : typ), res (eval_typ tyr):=
    match op, ty with
    | UopNotbool, TBool    => (fun v tyr => @cast_typ TBool (negb v) tyr)
    | UopNotint,  TInt32 s => (fun v tyr => @cast_typ (TInt32 s) (Int.not v) tyr)
    | UopNeg,  TInt32 s    => (fun v tyr => @cast_typ (TInt32 s) (Int.neg v) tyr)
    | UopPlus, TInt32 s    => (fun v tyr => @cast_typ (TInt32 s) v tyr)
    | UopNotint, TInt64 s  => (fun v tyr => @cast_typ (TInt64 s) (Int64.not v) tyr)
    | UopNeg, TInt64 s     => (fun v tyr => @cast_typ (TInt64 s) (Int64.neg v) tyr)
    | UopPlus, TInt64 s    => (fun v tyr => cast_typ  v tyr)
    | _, _ => (fun _ _ => fail)
    end.

  Definition bool_bool_bool (t1 t2:typ) :=
    match t1 , t2 with
    | TBool , TBool => OK TBool
    |   _   ,   _    => fail
    end.

  Definition int_int_int (t1 t2:typ) :=
    match t1,t2 with
    | TInt32 Signed , TInt32 Signed => OK (TInt32 Signed)
    | TInt32 Unsigned , TInt32 Unsigned => OK (TInt32 Unsigned)
    | TInt64 Signed , TInt64 Signed   => OK (TInt64 Signed)
    | TInt64 Unsigned , TInt64 Unsigned   => OK (TInt64 Unsigned)
    |  _ , _ => fail
    end.

  Definition int_int_bool (t1 t2:typ) :=
    match t1,t2 with
    | TInt32 Signed , TInt32 Signed => OK TBool
    | TInt32 Unsigned , TInt32 Unsigned => OK TBool
    | TInt64 Signed , TInt64 Signed   => OK TBool
    | TInt64 Unsigned , TInt64 Unsigned   => OK TBool
    |  _ , _ => fail
    end.

  Definition eq_neq_bool (t1 t2:typ) :=
    match t1,t2 with
    | TBool , TBool => OK TBool
    | TInt32 Signed , TInt32 Signed => OK TBool
    | TInt32 Unsigned , TInt32 Unsigned => OK TBool
    | TInt64 Signed , TInt64 Signed   => OK TBool
    | TInt64 Unsigned , TInt64 Unsigned   => OK TBool
    | TEnum _ _ , TEnum _ _ => if typ_eq_dec t1 t2 then OK TBool else fail
    |  _ , _ => fail
    end.



  Definition typof_binary_op (op:binary_op)  :=
    match op with
    | BopAndbool => bool_bool_bool
    | BopOrbool => bool_bool_bool
    | BopXorbool => bool_bool_bool
    | BopAdd => int_int_int
    | BopSub => int_int_int
    | BopMul => int_int_int
    | BopDiv => int_int_int
    | BopMod => int_int_int
    | BopAndint => int_int_int
    | BopOrint => int_int_int
    | BopXorint => int_int_int
    | BopShl => int_int_int
    | BopShr => int_int_int
    | BopEq => eq_neq_bool
    | BopNeq => eq_neq_bool
    | BopLt => int_int_bool
    | BopGt => int_int_bool
    | BopLe => int_int_bool
    | BopGe => int_int_bool
    end.

  Definition bool_op (F : bool -> bool -> bool) (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
    match t1, t2 with
    | TBool , TBool => (fun v1 v2 tyr => @cast_typ TBool (F v1 v2) tyr)
    | _, _ =>   (fun _ _ _ => fail)
    end.


  Definition int_op (F32 : int -> int -> int) (F64 : int64 -> int64 -> int64)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
    match t1, t2 with
    | TInt32 s , TInt32 s' => if signedness_eq_dec s s' then
                                (fun v1 v2 tyr => @cast_typ (TInt32 s) (F32 v1 v2) tyr)
                              else (fun _ _ _ => fail)
    | TInt64 s , TInt64 s' => if signedness_eq_dec s s' then
                                (fun v1 v2 tyr => @cast_typ (TInt64 s) (F64 v1 v2) tyr)
                              else (fun _ _ _ => fail)
    | _, _ =>   (fun _ _ _ => fail)
    end.


  Definition int_op_s (F32s : int -> int -> res int) (F32u : int -> int -> res int)
    (F64s : int64 -> int64 -> res int64) (F64u : int64 -> int64 -> res int64)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
    match t1, t2 with
    | TInt32 s , TInt32 s'  =>
        match s , s' with
        | Signed , Signed => (fun v1 v2 tyr => @ecast_typ (TInt32 Signed) (F32s v1 v2) tyr)
        | Unsigned , Unsigned => (fun v1 v2 tyr => @ecast_typ (TInt32 Unsigned) (F32u v1 v2) tyr)
        | _   , _ => (fun _ _ _ => fail)
        end
    | TInt64 s , TInt64 s'  =>
        match s , s' with
        | Signed , Signed => (fun v1 v2 tyr => @ecast_typ (TInt64 Signed) (F64s v1 v2) tyr)
        | Unsigned , Unsigned => (fun v1 v2 tyr => @ecast_typ (TInt64 Unsigned) (F64u v1 v2) tyr)
        | _   , _ => (fun _ _ _ => fail)
        end
    | _, _ =>   (fun _ _ _ => fail)
    end.

  Definition int_eq_neq (equal:bool) (Fbool : bool -> bool -> bool)
    (F32 : int -> int -> bool) (F64 : int64 -> int64 -> bool) (Fenum : forall (elems : list ident), enum elems -> enum elems -> bool)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
    let map b := if equal then b else negb b in
    match t1, t2 with
    | TBool , TBool => (fun v1 v2 tyr => @cast_typ TBool (map (eqb v1 v2)) tyr)
    | TInt32 s , TInt32 s'  => (fun v1 v2 tyr => if signedness_eq_dec s s' then @cast_typ TBool (map (F32 v1 v2)) tyr else fail)
    | TInt64 s , TInt64 s'  => (fun v1 v2 tyr => if signedness_eq_dec s s' then @cast_typ TBool (map (F64 v1 v2)) tyr else fail)
    | ((TEnum n1 elems1) as t1) , ((TEnum n2 elems2) as t2) =>
        (fun v1 v2 tyr =>
           match typ_eq_dec t1 t2 with
           | left Eqt => @cast_typ TBool (map (Fenum elems2  (typ_cast abs_typ_impl Eqt v1) v2)) tyr
           |  _       => fail
           end
        )
    | _, _ =>   (fun _ _ _ => fail)
    end.

  Definition cmp_op (cmp32s : int -> int -> bool) (cmp32u:int -> int -> bool) (cmp64s : int64 -> int64 -> bool) (cmp64u : int64 -> int64 -> bool)
    (t1 t2:typ) : eval_typ t1 -> eval_typ t2 -> forall (tyr:typ),res (eval_typ tyr) :=
    match t1, t2 with
    | TInt32 s , TInt32 s'  =>
        match s , s' with
        | Signed , Signed => (fun v1 v2 tyr => @cast_typ TBool (cmp32s v1 v2) tyr)
        | Unsigned , Unsigned => (fun v1 v2 tyr => @cast_typ TBool (cmp32u v1 v2) tyr)
        |  _   , _ => (fun _ _ _ => fail)
        end
    | TInt64 s , TInt64 s' =>
        match s , s' with
        | Signed , Signed => (fun v1 v2 tyr => @cast_typ TBool (cmp64s v1 v2) tyr)
        | Unsigned , Unsigned => (fun v1 v2 tyr => @cast_typ TBool (cmp64u v1 v2) tyr)
        |  _   , _ => (fun _ _ _ => fail)
        end
    |  _ ,  _ => (fun _ _ _ => fail)
    end.


  Definition eval_binary_op (op: binary_op) : forall (t1:typ) (t2: typ)  (v1: eval_typ t1)  (v2: eval_typ t2) (tyr : typ), res (eval_typ tyr) :=
    match op with
    | BopAndbool => bool_op andb
    | BopOrbool  => bool_op orb
    | BopXorbool => bool_op xorb
    | BopAdd => int_op Int.add Int64.add
    | BopSub => int_op Int.sub Int64.sub
    | BopMul => int_op Int.mul Int64.mul
    | BopDiv => int_op_s I32.div U32.div I64.div U64.div
    | BopMod => int_op_s I32.mod U32.mod I64.mod U64.mod
    | BopAndint => int_op Int.and Int64.and
    | BopOrint => int_op Int.or Int64.or
    | BopXorint => int_op Int.xor Int64.xor
    | BopShl => int_op Int.shl Int64.shl
    | BopShr => int_op_s (partial2 Int.shr) (partial2 Int.shru) (partial2 Int64.shr)  (partial2 Int64.shru)
    | BopEq => int_eq_neq true eqb Int.eq Int64.eq  (fun elems v1 v2 =>
                                                  if enum_eq_dec v1 v2 then true else false)
    | BopNeq => int_eq_neq false eqb Int.eq Int64.eq  (fun elems v1 v2 =>
                                                  if enum_eq_dec v1 v2 then true else false)
    | BopLt => cmp_op Int.lt Int.ltu Int64.lt Int64.ltu
    | BopGt => cmp_op (Int.cmp Cgt) (Int.cmpu Cgt) (Int64.cmp Cgt) (Int64.cmpu Cgt)
    | BopLe => cmp_op (Int.cmp Cle) (Int.cmpu Cle) (Int64.cmp Cle) (Int64.cmpu Cle)
    | BopGe => cmp_op (Int.cmp Cge) (Int.cmpu Cge) (Int64.cmp Cge) (Int64.cmpu Cge)
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

  Fixpoint eval_record_lit_rec (lv: smaplist value) (fields: smaplist typ) : res (eval_recordtyp eval_typ fields).
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

  Definition eval_record_lit (n: ident) (lv: smaplist value) (fields: smaplist typ) : res value.
    destruct lv as [|x lv'].
    - apply fail.
    - destruct (eval_record_lit_rec (x :: lv') fields) as [r |].
      * apply (ret (Val (TRecord n fields) r)).
      * apply fail.
  Defined.

  Definition eval_array_get (ta:typ) (a: eval_typ ta) (t2:typ) (i: eval_typ t2) (tyr:typ): res (eval_typ tyr).
    destruct ta.
    4:
    {
      destruct arch eqn:Earch.
        - destruct (typ_eq_dec t2 (TInt32 Unsigned)).
          + subst. simpl in i. simpl in a.
            eapply ecast_typ.
            apply (Barray.get a (U64.of_u32 i)).
          + apply fail.
        - destruct (typ_eq_dec t2 (TInt64 Unsigned)).
          + subst. simpl in i. simpl in a.
            eapply ecast_typ.
            apply (Barray.get a i).
          + apply fail.
    }
    all: apply fail.
  Defined.

  Definition eval_array_set (ta: typ) (a : eval_typ ta) (t2:typ)
    (i : eval_typ t2) (t:typ) (v: eval_typ t) (tyr : typ): res (eval_typ tyr).
  Proof.
    destruct ta.
    4 :
    {
      destruct arch eqn:Earch.
      - destruct (typ_eq_dec t2 (TInt32 Unsigned)).
        + destruct (typ_eq_dec ta t).
          * subst. simpl in i. simpl in a.
            apply (@ecast_typ (TArray t) (Barray.set a (U64.of_u32 i) v)).
          * apply fail.
        + apply fail.
      - destruct (typ_eq_dec t2 (TInt64 Unsigned)).
        + destruct (typ_eq_dec ta t).
          * subst. simpl in i. simpl in a.
            apply (@ecast_typ (TArray t) (Barray.set a  i v)).
          * apply fail.
        + apply fail.
    }
    all: apply fail.
  Defined.

  Import MapList.

  Fixpoint exists_typeof_field (F: typ -> Type) (k:key) (fields : smaplist typ) :
    forall (GP : good_proj k  fields = true),
      { ty| typeof_field F k  fields GP = F ty}.
  Proof.
    destruct fields;simpl.
    - intros. discriminate.
    - destruct p.
      simpl.
      intros.
      destruct ((k=?s)%string).
      exists t0. reflexivity.
      apply exists_typeof_field.
  Defined.


  Definition cast_typof_field (k:key) (fields :smaplist typ):
    forall (GP :good_proj k  fields = true),
    typeof_field eval_typ k  fields GP ->
    value.
  Proof.
    intros.
    destruct (exists_typeof_field eval_typ _ _ GP) as (ty & EQ).
    apply (Val ty (cast EQ X)).
  Defined.

  Definition eval_record_project_aux (fields: smaplist typ) (rc: eval_recordtyp eval_typ fields) (k: ident) (ty:typ) : res (eval_typ ty).
    simpl in rc.
    unfold eval_recordtyp in rc.
    destruct (good_proj k fields) eqn:GP.
    - specialize (project eval_typ rc k GP).
      intro.
      destruct (exists_typeof_field eval_typ _ _ GP) as (ty1 & EQ).
      apply (cast EQ) in X.
      exact (cast_typ X ty).
    - exact fail.
  Defined.


  Definition eval_record_project (ty:typ) : forall (v: eval_typ ty) (k: ident) (tyr : typ), res (eval_typ tyr) :=
    match ty with
    | TRecord _ fields => fun v k tyr => eval_record_project_aux fields v k tyr
    | _ => fun _ _ _ => fail
    end.


  Definition typeof_value  (v : value ) :=
    match v with
    | Val t _ => t
    end.

  Definition typof_field_dec (k:ident) (fields: smaplist typ) : res {t : typ| typof_field k fields = OK t}.
  Proof.
    destruct (typof_field k fields) as [t |] eqn:Etyp.
    apply OK. exists t. reflexivity.
    apply fail.
  Defined.


Ltac change_good_proj :=
  match goal with
  | |- context[good_proj ?K ((?S,?V)::?L)] =>
      change (good_proj K ((S,V)::L)) with ((K=?S)%string || good_proj K L)
  end.

Fixpoint good_proj_map  (A B: Type) (F : A -> B) (k:key) (fields :smaplist A):
    good_proj k fields = good_proj k (map F fields).
Proof.
  destruct fields.
  - simpl. reflexivity.
  - destruct p; simpl.
    repeat change_good_proj.
    destruct (k =? s)%string.
    reflexivity.
    apply good_proj_map.
Defined.

Definition good_proj_map_app     {A B: Type} (F : A -> B) {k:key} {fields :smaplist A}:
  forall (GP : good_proj k fields = true), good_proj k (map F fields) = true.
Proof.
  intros.
  rewrite <- GP.
  symmetry. apply good_proj_map.
Defined.

Fixpoint typeof_field_typ (k:key) (fields : smaplist typ) (GK: good_proj k fields = true) :
  { ty : typ | find_type_of_field k fields = OK ty}.
Proof.
  destruct fields.
  - exfalso. apply (good_proj_nil GK).
  - destruct p.
    simpl.
    revert GK.
    simpl.
    repeat change_good_proj.
    destruct (k=? s)%string.
    + intro.
      exists t0;reflexivity.
    + simpl.
      intros.
      apply (typeof_field_typ k fields GK).
Defined.


Fixpoint no_TFun (t:typ) :=
  match t with
  | TFun _ _ => false
  | TArray t => no_TFun t
  | TRecord _ l => List.forallb (fun x => no_TFun (snd x)) l
  | _  => true
  end.

Definition fo_typ (t:typ) :=
  match t with
  | TFun l r => List.forallb no_TFun l && no_TFun r
  | TArray t => no_TFun t
  | TRecord _ l => List.forallb (fun x => no_TFun (snd x)) l
  |   _         => true
  end.

Definition cast_etyp {k:key} {fields : smaplist typ} {tv: typ} (v:  eval_typ tv)
  (EQ : find_type_of_field k fields = OK tv):
  type_of_field eval_typ k fields.
Proof.
  unfold type_of_field.
  rewrite EQ. apply  v.
Defined.


Definition eval_record_upd_aux  (fields: smaplist typ) (rc: eval_recordtyp eval_typ fields) (k: ident) (tv: typ) (v: eval_typ tv) :
  res (eval_recordtyp eval_typ fields) :=
  dyn_upd eval_typ typ_eq_dec rc k tv v.


(*
Lemma typof_field_is_type :
  forall (fields: smaplist typ) k t,
   typof_field k fields = OK t ->
   eval_typ t = type_of_field k (eval_fields_typ eval_typ fields).
   Proof.
   induction fields as [| (x, t) fields']; intros.
   - simpl in H. discriminate.
   - unfold typof_field in *. unfold MapList.find_err in *.
     unfold type_of_field in *. unfold MapList.find in *.
     simpl. unfold key_eq. destruct (Ident.eq_dec x k).
     + inversion H. reflexivity.
     + apply (IHfields' k t0 H).
   Defined.

  Definition eval_record_update_aux (n: ident) (fields: smaplist typ) (rc: eval_typ (TRecord n fields)) (k: ident) (v: value) : res value.
    simpl in rc. destruct v as [tv v]. destruct (typof_field k fields) as [t |] eqn:Etyp.
    - destruct (typ_eq_dec tv t) as [Eqt |_].
      + apply (typof_field_is_type fields k t) in Etyp.
        rewrite Eqt in v. rewrite Etyp in v.
        eapply bind.
        apply (update rc k v).
        intro rc'.
        apply (ret (Val (TRecord n fields) rc')).
      + apply fail.
    - apply fail.
  Defined.
*)

  Definition eval_record_update (t1:typ) : forall (v1: eval_typ t1) (k: ident) (tv : typ) (v: eval_typ tv) (tyr:typ), res (eval_typ tyr) :=
    match t1 with
    | TRecord n fields => fun st k tv v tyr =>
                            @ecast_typ (TRecord n fields) (eval_record_upd_aux fields st k tv v) tyr
    | _ => fun _ _ _ _ _ => fail
    end.

  Definition typof_record_project (ty:typ) (f:ident): res typ :=
    match ty with
    | TRecord _ l => find_err key_eq f l
    |    _      => fail
    end.

  Definition typof_array (ty:typ) : res typ :=
    match ty with
    | TArray e => OK e
    |    _      => fail
    end.


  (* Fixpoint eval_access_list (ty:typ) (v: res (eval_typ ty)) (acs: list access_value) (tyr : typ) {struct acs} : res (eval_typ tyr) :=
    match acs with
    | nil => ecast_typ v tyr
    | ac :: acs' =>
        match ac with
        | AcvalRecordField f =>
            let* tp := typof_record_project ty f in
            let* v  := v in
            let v' := eval_record_project ty v f tp in
            eval_access_list tp v' acs' tyr
        | AcvalArrayIndex va =>
            let* te := typof_array ty in
            let* v  := v  in
            let* i  := va in
            let v' := eval_array_get _ v typof_index i te in
            eval_access_list te v' acs' tyr
        end
    end. *)

  Definition res_eq_typ (v1 v2 : res value) : bool :=
    match v1 , v2 with
    | Error _ , _ | _ , Error _ => true
    | OK v1 , OK v2 => proj_sumbool (typ_eq_dec (typeof_value v1) (typeof_value v2))
    end.

  Definition eval_ifthenelse (c:bool) (t2: typ) (v2:res (eval_typ t2)) (t3: typ)  (v3: res (eval_typ t3)) (tr:typ) : res (eval_typ tr) :=
    if c then ecast_typ v2 tr else ecast_typ v3 tr.


  (* Fixpoint typecheck_match_branches (elems: list ident) (v: enum elems) (cases: list (pattern * value)) (tr: option typ) : res typ :=
    let check_val_typ (v: value) : res typ :=
      let '(Val tv v) := v in
      match tr with
      | None => ret tv
      | Some tr =>
          if typ_eq_dec tr tv then ret tv
          else fail
      end
    in
    match cases with
    | nil => fail
    | (x, vx) :: nil =>
        check_val_typ vx
    | (x, vx) :: ((_ :: _) as cases') =>
        let* t := check_val_typ vx in
        typecheck_match_branches elems v cases' (Some t)
    end. *)

  Definition eval_match (tv:typ) (v: eval_typ tv) (tr: typ) (cases: list (pattern * (res (eval_typ tr)))) : res (eval_typ tr) :=
    (match tv as t0 return (eval_typ t0 -> res (eval_typ tr)) with
    | TEnum _ elems => 
        (fun v0 => match_with_err v0 cases)
    | _ => (fun _ => fail)
    end) v.

  Fixpoint eval_app (tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams (eval_typ tret)) (args: DList.dlist eval_typ  tparams) :
    res (eval_typ tret).
  Proof.
    destruct args.
    - simpl in f. apply (f tt).
    - simpl in f.
      destruct l.
      +  apply (f e).
      + apply (eval_app _ _ (f e) args).
  Defined.



  Fixpoint eval_app_typ (tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams (eval_typ tret)) (args: DList.dlist eval_typ tparams) (ty:typ):
    res (eval_typ ty).
  Proof.
    destruct args.
    - simpl in f. apply (ecast_typ (f tt) ty).
    - simpl in f.
      destruct l.
      +  apply (ecast_typ (f e) ty).
      + apply (eval_app_typ _ _ (f e) args ty).
  Defined.


  Fixpoint eval_app_res (tparams: list typ) (tret: typ) (f: eval_funtyp eval_typ tparams (eval_typ tret))
    (args: DList.dlist (fun (ty:typ) => res (eval_typ ty)) tparams) (ty:typ):
    res (eval_typ ty).
  Proof.
    destruct args.
    - simpl in f. apply (ecast_typ (f tt) ty).
    - simpl in f.
      destruct l.
      + apply (let* e' := e in ecast_typ (f e') ty).
      + eapply bind. apply e.
      apply (fun x => eval_app_res _ _ (f x) args ty).
  Defined.



  Definition typof_expr (te:tenv) (e:expr) : res typ :=
    btyp_to_typ te (Typing.typof_expr e).

  Definition cast_int (t:typ) (i:int) : res (eval_typ t) :=
    match t with
    | TInt32 s => OK i
    |  _       => fail
    end.

  Definition cast_int64 (t:typ) (i:int64) : res (eval_typ t) :=
    match t with
    | TInt64 s => OK i
    |  _       => fail
    end.


  Fixpoint eval_expr (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr)  : res (eval_typ ty) :=
    match e with
    | ETrue  => @cast_typ TBool true ty
    | EFalse => @cast_typ TBool false ty
    | EInt32 i s => @cast_typ (TInt32 s) i ty
    | EInt64 i s => @cast_typ (TInt64 s) i ty
    | EConstr x _  => eval_constr te x ty
    | EVar x _ => eval_var ge le x ty
    | ECast e1 tr =>
        let* tr' := btyp_to_typ te tr in
        let* te1  := typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1  in
        ecast_typ  (eval_cast te1 v1 tr') ty
    | EUnaryOp op e bt =>
        let* tye := btyp_to_typ te bt in
        let* v := eval_expr te ge le tye e in
        eval_unary_op op tye v ty
    | EBinaryOp op e1 e2 bt =>
        let* tye1 := typof_expr te e1 in
        let* tye2  := typof_expr te e2 in
        let* v1 := eval_expr te ge le tye1 e1  in
        let* v2 := eval_expr te ge le tye2 e2  in
        eval_binary_op op tye1 tye2 v1 v2 ty
    | EArrayGet e1 e2 _ =>
        let* tye1 := typof_expr te e1 in
        let* tye2 := typof_expr te e2 in
        let* v1 := eval_expr te ge le tye1 e1  in
        let* v2 := eval_expr te ge le tye2 e2  in
        eval_array_get tye1 v1 tye2 v2 ty
    | EArraySet e1 e2 e3 _ =>
        let* tye1 := typof_expr te e1 in
        let* tye2 := typof_expr te e2 in
        let* tye3 := typof_expr te e3 in
        let* v1 := eval_expr te ge le tye1 e1 in
        let* v2 := eval_expr te ge le tye2 e2 in
        let* v3 := eval_expr te ge le tye3 e3 in
        eval_array_set tye1 v1 tye2 v2 tye3 v3 ty
    | ERecordProj e k _ =>
        let* tye := typof_expr te e in
        let* v := eval_expr te ge le tye e in
        eval_record_project tye v k ty
    | ERecordUpdate e1 k e2 _ =>
        let* te1 := typof_expr te e1 in
        let* te2 := typof_expr te e2 in
        let* v1 := eval_expr te ge le te1 e1 in
        let* v2 := eval_expr te ge le te2 e2 in
        eval_record_update te1 v1 k te2 v2 ty
    (* | EDeepAccess e1 acs _ =>
        let* tye1 := typof_expr te e1 in
        let v1 := eval_expr te ge le tye1 e1 in
        let vacs := List.map (eval_access_expr te ge le) acs in
        eval_access_list tye1 v1 vacs ty *)
    | EApp v args _ =>
        let* tyf := typof_expr te v in
        match tyf with
        | TFun tparams tret =>
            let* f := eval_expr te ge le  (TFun tparams tret) v in
            let* vargs := DList.map2 _ (eval_expr te ge le) args tparams in
            eval_app_res tparams tret f vargs ty
        |  _  => fail
        end
    | EIfThenElse e1 e2 e3 _ =>
        let* v1 := eval_expr te ge le TBool e1  in
        let* te2 := typof_expr te e2 in
        let* te3 := typof_expr te e3 in
        let v2 := eval_expr te ge le te2 e2 in
        let v3 := eval_expr te ge le te3 e3  in
        eval_ifthenelse  v1 te2 v2 te3 v3 ty
    | EMatch e1 cases _  =>
        let* te1:= typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1 in
        let vcases := MapList.map (eval_expr te ge le ty) cases in
        eval_match te1 v1 ty vcases
    | ELetIn x e1 e2 _ =>
        let* te1 := typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1 in
        let le' := lenv_update le x (Val te1 v1) in
        eval_expr te ge le' ty e2
    end.

  (* with eval_access_expr (te: tenv) (ge: genv) (le: lenv) (ac: access) : access_value :=
    match ac with
    | AcRecordField f _ => (AcvalRecordField f)
    | AcArrayIndex e _ =>
        let v := eval_expr te ge le typof_index e  in
        AcvalArrayIndex v
    end. *)


  Lemma eval_expr_rew : forall (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr),
      eval_expr te ge le ty e =
    match e with
    | ETrue  => @cast_typ TBool true ty
    | EFalse => @cast_typ TBool false ty
    | EInt32 i s => @cast_typ (TInt32 s) i ty
    | EInt64 i s => @cast_typ (TInt64 s) i ty
    | EConstr x _  => eval_constr te x ty
    | EVar x _ => eval_var ge le x ty
    | ECast e1 tr =>
        let* tr' := btyp_to_typ te tr in
        let* te1  := typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1  in
        ecast_typ  (eval_cast te1 v1 tr') ty
    | EUnaryOp op e bt =>
        let* tye := btyp_to_typ te bt in
        let* v := eval_expr te ge le tye e in
        eval_unary_op op tye v ty
    | EBinaryOp op e1 e2 bt =>
        let* tye1 := typof_expr te e1 in
        let* tye2  := typof_expr te e2 in
        let* v1 := eval_expr te ge le tye1 e1  in
        let* v2 := eval_expr te ge le tye2 e2  in
        eval_binary_op op tye1 tye2 v1 v2 ty
    | EArrayGet e1 e2 _ =>
        let* tye1 := typof_expr te e1 in
        let* tye2 := typof_expr te e2 in
        let* v1 := eval_expr te ge le tye1 e1  in
        let* v2 := eval_expr te ge le tye2 e2  in
        eval_array_get tye1 v1 tye2 v2 ty
    | EArraySet e1 e2 e3 _ =>
        let* tye1 := typof_expr te e1 in
        let* tye2 := typof_expr te e2 in
        let* tye3 := typof_expr te e3 in
        let* v1 := eval_expr te ge le tye1 e1 in
        let* v2 := eval_expr te ge le tye2 e2 in
        let* v3 := eval_expr te ge le tye3 e3 in
        eval_array_set tye1 v1 tye2 v2 tye3 v3 ty
    | ERecordProj e k _ =>
        let* tye := typof_expr te e in
        let* v := eval_expr te ge le tye e in
        eval_record_project tye v k ty
    | ERecordUpdate e1 k e2 _ =>
        let* te1 := typof_expr te e1 in
        let* te2 := typof_expr te e2 in
        let* v1 := eval_expr te ge le te1 e1 in
        let* v2 := eval_expr te ge le te2 e2 in
        eval_record_update te1 v1 k te2 v2 ty
    (* | EDeepAccess e1 acs _ =>
        let* tye1 := typof_expr te e1 in
        let v1 := eval_expr te ge le tye1 e1 in
        let vacs := List.map (eval_access_expr te ge le) acs in
        eval_access_list tye1 v1 vacs ty *)
    | EApp v args _ =>
        let* tyf := typof_expr te v in
        match tyf with
        | TFun tparams tret =>
            let* f := eval_expr te ge le  (TFun tparams tret) v in
            let* vargs := DList.map2 _ (eval_expr te ge le) args tparams in
            eval_app_res tparams tret f vargs ty
        |  _  => fail
        end
    | EIfThenElse e1 e2 e3 _ =>
        let* v1 := eval_expr te ge le TBool e1  in
        let* te2 := typof_expr te e2 in
        let* te3 := typof_expr te e3 in
        let v2 := eval_expr te ge le te2 e2 in
        let v3 := eval_expr te ge le te3 e3  in
        eval_ifthenelse  v1 te2 v2 te3 v3 ty
    | EMatch e1 cases _  =>
        let* te1:= typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1 in
        let vcases := MapList.map (eval_expr te ge le ty) cases in
        eval_match te1 v1 ty vcases
    | ELetIn x e1 e2 _ =>
        let* te1 := typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1 in
        let le' := lenv_update le x (Val te1 v1) in
        eval_expr te ge le' ty e2
    end.
  Proof.
    destruct e; reflexivity.
  Qed.

  Fixpoint eval_literal (te: tenv) (l: literal) : res value :=
    match l with
    | LTrue => ret (Val TBool true)
    | LFalse => ret (Val TBool false)
    | LInt32 i s => ret (Val (TInt32 s) i)
    | LInt64 i s => ret (Val (TInt64 s) i)
    | LArray a _ _ =>
        let* av := mmap (eval_literal te) a in
        eval_array_lit av
    | LRecord rc _ rid =>
        let* rcv := MapList.map_err (eval_literal te) rc in
        let* fields := TEnv.get_rdef te rid in
        eval_record_lit rid rcv fields
    end.

  Definition cast_typ_M (tret:typ) (v: value) : M (eval_typ tret) :=
    match v with
      | Val tv v =>
          match typ_eq_dec tv tret with
          | left e =>  (ret (typ_cast abs_typ_impl e v))
          |  _     => fail
          end
    end.

  Section MAP'.
    Context {A B: Type}.
    Variable F : A -> B.

  Fixpoint map'  (l:list A) : list B :=
    match l with
    | nil => nil
    | e:: nil => F e:: nil
    | e::l'   => F e :: map' l'
    end.

  End MAP'.

  Fixpoint build_funval_rec (te: tenv) (ge: genv) (le: lenv) (params: smaplist typ) (tret: typ) (e: expr) :
    eval_funtyp eval_typ (List.map snd  params) (eval_typ tret) :=
    match params  with
    | [] => fun _ : unit => eval_expr te ge le tret e
    | p :: l =>
        fun y : eval_typ (snd p) =>
          match
            l as l0
            return
            (eval_funtyp eval_typ (List.map (fun x : string * typ => snd x) l0) (eval_typ tret) ->
             let l1 := List.map snd l0 in
             match l1 with
             | [] => res (eval_typ tret)
             | _ :: _ => eval_funtyp eval_typ l1 (eval_typ tret)
           end)
      with
      | [] =>
          fun _ => eval_expr te ge (lenv_update le (fst p) (Val (snd p) y)) tret e
      | p0 :: l0 =>
          fun
            build_funval_rec  => build_funval_rec
      end (build_funval_rec te ge (lenv_update le (fst p) (Val (snd p) y)) l tret e)
  end.

  Lemma build_funval_rec_rw : forall (te: tenv) (ge: genv) (le: lenv) (params: smaplist typ) (tret: typ) (e: expr),
    build_funval_rec te ge le params tret e =
    match params  with
    | [] => fun _ : unit => eval_expr te ge le tret e
    | p :: l =>
        fun y : eval_typ (snd p) =>
          match
            l as l0
            return
            (eval_funtyp eval_typ (List.map (fun x : string * typ => snd x) l0) (eval_typ tret) ->
             match List.map snd l0 with
           | [] => res (eval_typ tret)
           | _ :: _ => eval_funtyp eval_typ (List.map (fun x : string * typ => snd x) l0) (eval_typ tret)
           end)
      with
      | [] =>
          fun _ => eval_expr te ge (lenv_update le (fst p) (Val (snd p) y)) tret e
      | p0 :: l0 =>
          fun
            build_funval_rec  => build_funval_rec
      end (build_funval_rec te ge (lenv_update le (fst p) (Val (snd p) y)) l tret e)
  end.
  Proof.
    destruct params;reflexivity.
  Qed.

  Definition build_funval (te: tenv) (ge: genv) (params: smaplist typ) (tret: typ) (e: expr) : eval_typ (TFun (List.map (fun x => snd x) params) tret).
    destruct params as [| p params'].
    - simpl.
      intro.
      apply (eval_expr te ge STree.empty tret e).
    - apply (build_funval_rec te ge STree.empty (p :: params') tret e).
  Defined.


  Definition build_fun_value (te: tenv) (ge: genv) (params: smaplist btyp) (tret: btyp) (e: expr) : res value :=
    if MapList.nodup Ident.eq_dec params then
      let* tret' := btyp_to_typ te tret in
      let* params' := MapList.map_err (btyp_to_typ te) params in
      ret (Val (TFun (List.map (fun x => snd x) params') tret') (build_funval te ge params' tret' e))
    else fail.

  Definition fields_btyp_to_typ (te: tenv) (fields: smaplist btyp) : res (smaplist typ) :=
    MapList.map_err (btyp_to_typ te) fields.

  Definition eval_def_type (te: tenv) (tid: ident) (td: type_def field_descr) : res tenv :=
    match td with
    | TdEnum elems =>
        TEnv.update_defs te tid (TdEnum elems)
    | TdRecord fields =>
        let* fields' := MapList.map_err (btyp_to_typ te) (MapList.map fst fields) in
        TEnv.update_defs te tid (TdRecord fields')
    end.

  Definition eval_def_const (te: tenv) (ge: genv) (x: ident) (l: literal) (ty: btyp) : res genv :=
    let* ty' := btyp_to_typ te ty in
    let* vv := eval_literal te l in
    let* v'  := cast_value vv ty' in
    genv_update ge x (Val ty' v').

  Definition eval_def_fun (te: tenv) (ge: genv) (x: ident) (f: function) : res genv :=
    let* fv := build_fun_value te ge (fn_params f) (fn_return f) (fn_body f) in
    genv_update ge x fv.

  Definition eval_decl_const (te: tenv) (ge : genv) (x:ident) (bt:btyp) :=
    let* ty :=  Typing.btyp_to_typ te bt  in
    let* v  := genv_get ge x in
    if typ_eq_dec ty (typeof_value v) then eret tt else fail.

  Definition eval_decl_fun (te:tenv) (ge : genv) (x:Syntax.ident) (params : list (Syntax.param_attr * btyp)) (tret:btyp) :=
    let* tparam := mmap (Typing.btyp_to_typ te) (List.map snd params) in
    let* tret   := Typing.btyp_to_typ te tret in
    let* v := genv_get ge x in
    if (typ_eq_dec (TFun tparam tret) (typeof_value v)) then eret tt else fail.


  (** Interpreter *)
  Fixpoint interpret_rec (te: tenv) (ge: genv) (cmds: list command) : res (list value) :=
    match cmds with
    | nil => ret nil
    | c :: xprog' =>
        match c with
        | CmdDef (DefType x td) =>
            let* te' := eval_def_type te x td in
            interpret_rec te' ge xprog'
        | CmdDef (DefConst x l ty) =>
            let* ge' := eval_def_const te ge x l ty in
            interpret_rec te ge' xprog'
        | CmdDef (DefFun x f) =>
            let* ge' := eval_def_fun te ge x f in
            interpret_rec te ge' xprog'
        | CmdDef (DeclType _ _) => failwith "the program contains abstract types"
        | CmdDef (DeclConst _ _)
        | CmdDef (DeclFun _ _ _) => failwith "the program contains abstract definitions"
        | CmdExpr bt e =>
            let* ty := typof_expr te e in
            let* v := eval_expr te ge STree.empty ty e in
            let* l := interpret_rec te ge xprog' in
            ret (Val ty v :: l)
        end
    end.

  Definition interpret (iprog: list command) : res (list value) :=
    interpret_rec TEnv.empty STree.empty iprog.

  (** Evaluation of a definition with dynamic environments *)

  Fixpoint eval_def_rec (te: tenv) (ge: genv) (prog: program) (x: ident) : res value :=
    match prog with
    | nil => fail
    | d :: prog' =>
        match d with
        | DefType y td =>
            let* te' := eval_def_type te x td in
            eval_def_rec te' ge prog' y
        | DefConst y l ty =>
            let* ge' := eval_def_const te ge y l ty in
            if Ident.eq_dec x y then genv_get ge' x
            else eval_def_rec te ge' prog' x
        | DefFun y f =>
            let* ge':= eval_def_fun te ge y f in
            if Ident.eq_dec x y then genv_get ge' x
            else eval_def_rec te ge' prog' x
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
    eval_def_rec TEnv.empty impl prog x.

  (** Evaluation of a whole program *)

  Fixpoint eval_prog_rec (te: tenv) (ge: genv) (prog: program) : res (tenv * genv) :=
    match prog with
    | nil => ret (te,ge)
    | d :: prog' =>
        match d with
        | DefType a td =>
            let* te' := eval_def_type te a td in
            eval_prog_rec te' ge prog'
        | DefConst x l ty =>
            let* ge' := eval_def_const te ge x l ty in
            eval_prog_rec te ge' prog'
        | DefFun x f =>
            let* ge' := eval_def_fun te ge x f in
            eval_prog_rec te ge' prog'
        | DeclType _ _ => eval_prog_rec te ge prog'
        | DeclConst y bt =>
            let* _ := eval_decl_const te ge y bt in
            eval_prog_rec te ge prog'
        | DeclFun y params tret =>
            let* _ := eval_decl_fun te ge y params tret in
            eval_prog_rec te ge prog'
        end
    end.

  Definition eval_prog (impl: genv) (prog: program) : res (tenv* genv) :=
    eval_prog_rec TEnv.empty impl prog.

  (** Redefinition of eval_def by computing the whole global environment first *)

  Definition eval_def2 (impl: genv) (prog: program) (x: ident) : res value :=
    let* (_, ge) := eval_prog impl prog in
    genv_get ge x.

End DENOT.
