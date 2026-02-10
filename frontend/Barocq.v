Set Universe Polymorphism.
From Coq Require Import List String ListDec PArith Bool.
From compcert Require Import Coqlib Integers Maps Ctypes.
From BarocqComp Require Import Error Maps2 Utils Intop Barray Brecord Benum Types Typing Syntax Pp Printer.
From BarocqComp Require Import Denot.
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
  | EApp (e: expr) (args: list expr) : expr                  (* e(args) *)
  | EIfThenElse (e1 e2 e3: expr) : expr                      (* if e1 then e2 else e3 *)
  | EMatch (e: expr) (cases: list (pattern * expr)) : expr   (* match e with V1 -> e1 ... | Vn -> en end *)    
  | ELetIn (x: ident) (e1 e2: expr) : expr                   (* let x = e1 in e2 *)
  | EAttr (x:ident) (e:expr).                                (* expression with a decoration  *)

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

Module Pp.

  Fixpoint pp_expr (e:expr) :=
    match e with
    | ETrue => Bstr "true"
    | EFalse => Bstr "false"
    | EInt32 i s => Printer.pp_sint s i
    | EInt64 i s => Printer.pp_sint64 s i
    | EConstr x  => Bstr x
    | EVar x     => Bstr x
    | ECast e ty => Pp.seq (Bstr "(" :: pp_btyp ty :: Bstr ")"
                              :: pp_expr e :: nil)
    | EUnaryOp o e => Pp.seq (Bstr (string_of_unary_op o) ::
                                   Bstr " " :: pp_expr e ::  nil)
    | EBinaryOp o e1 e2  =>
        Pp.seq
          (pp_expr e1 :: Bstr " " ::
             Bstr (string_of_binary_op o) :: Bstr " " ::
             pp_expr e2 ::  nil)
    | EArrayGet a i => Bcat (pp_expr a )
                         (array_index pp_expr i)
    | EArraySet a i v =>
        Pp.seq (pp_expr a :: Bstr "[" :: pp_expr i :: Bstr "] <- " :: pp_expr v :: nil)
    | ERecordProj a i => Bcat (pp_expr a)
                         (Bcat (Bstr ".") (Bstr i))
  | ERecordUpdate a fd v =>
      Pp.seq (pp_expr a :: Bstr "." :: Bstr fd :: Bstr " <- " :: pp_expr v :: nil)

    | EApp a l => Pp.seq (pp_expr a :: Bstr "(" :: pp_list (Bstr ", ") pp_expr l :: Bstr ")" :: nil)
    | EIfThenElse c t e => Bstack
                             (Bcat (Bstr "if ") (pp_expr c))
                             (Bstack (Bcat (Bstr "then ") (pp_expr t))
                                (Bcat (Bstr "else ") (pp_expr e)) Left) Left
    | EMatch e cases => Bstr "match ... "
    | ELetIn id e1 e2 => Bcat (Bstr "let ") (Bstack (Pp.seq (Bstr id :: Bstr " := " :: pp_expr e1 :: Bstr " in " :: nil))                                               (pp_expr e2) Left)
    | EAttr id e => Pp.seq (Bstr "#[ " :: Bstr id :: Bstr " ]"  :: pp_expr e :: nil)
    end.

  Definition pp_globdef (gd:globdef) : box :=
    match gd with
    | DefType id td => Bcat (Bstr "type") (Bstr id)
    | DefConst id lit _ => Pp.seq (Bstr "defn ":: Bstr id :: Bstr " := " :: Printer.pp_literal lit :: nil)
    | DefFun id f       => Printer.pp_function pp_expr pp_btyp id f
    | _                 => Bstr "decl ..."
    end.

  Definition pp_program (p:program) := pp_slist pp_globdef p.

End Pp.

Module Typed.

  (** * Typed abstract syntax *)

  (** ** Expressions *)

  Inductive expr : Type :=
    | ETrue : expr
    | EFalse : expr
    | EInt32 : int -> signedness -> expr
    | EInt64 : int64 -> signedness -> expr
    | EConstr : ident -> int -> btyp -> expr
    | EVar : ident -> btyp -> expr
    | ECast : expr -> btyp -> expr
    | EUnaryOp : unary_op -> expr -> btyp -> expr
    | EBinaryOp : binary_op -> expr -> expr -> btyp -> expr
    | EArrayGet : expr -> expr -> layout -> btyp -> expr
    | EArraySet : expr -> expr -> expr -> btyp -> expr
    | ERecordProj : expr -> ident -> layout -> btyp -> expr
    | ERecordUpdate : expr -> ident -> expr -> btyp -> expr
    | EApp : expr -> list expr -> btyp -> expr
    | EIfThenElse : expr -> expr -> expr -> btyp -> expr
    | EMatch : expr -> list (pattern * expr) -> btyp -> expr
    | ELetIn : ident -> expr -> expr -> btyp -> expr
    | EAttr : ident -> expr -> expr.

  Fixpoint typof_expr (e: expr) : btyp :=
    match e with
    | ETrue | EFalse => BBool
    | EInt32 _ s     => BInt32 s
    | EInt64 _ s     => BInt64 s
    | EConstr _ _ ty
    | EVar _ ty
    | ECast _ ty
    | EUnaryOp _ _ ty
    | EBinaryOp _ _ _ ty
    | EArrayGet _ _ _ ty
    | EArraySet _ _ _ ty
    | ERecordProj _ _ _ ty
    | ERecordUpdate _ _ _ ty
    | EMatch _ _ ty 
    | EApp _ _ ty
    | EIfThenElse _ _ _ ty
    | ELetIn _ _ _ ty => ty
    | EAttr _ e1 => typof_expr e1
    end.

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

 (* Module Pp.

    Fixpoint pp_expr (e:expr) : box :=
    match e with
      | ETrue  => Bstr "true"
      | EFalse => Bstr "false"
      | EInt32 i s => Printer.pp_sint s i
      | EInt64 i s => Printer.pp_sint64 s i
      | EConstr s  _ => Bstr s
      | EVar v _     => Bstr v
      | ECast e v    => Pp.seq (Bstr "(":: Printer.pp_btyp v :: Bstr ")" :: pp_expr e :: nil)
      | EUnaryOp o e1 _ => Bcat (Bstr (Printer.string_of_unary_op o)) (pp_expr e1)
      | EBinaryOp o e1 e2 => Pp.seq ((pp_expr e1):: (Bstr (Printer.string_of_binary_op o)) :: (pp_expr e2) :: nil)
      | EArrayGet e1 e2   => Pp.seq (pp_expr e1 :: Bstr "[" :: pp_expr e2  :: "]" :: nil)
      | EArraySet e i v   => Pp.seq (pp_expr e  :: Bstr "[" :: pp_expr i  :: "] <- " :: pp_expr v :: nil)
      | ERecordProj e id  => Pp.seq (pp_expr e1 :: Bstr "." :: Bstr id :: nil)
      | ERecordUpdate e id v _  =>  Pp.seq (pp_expr e1 :: Bstr "." :: Bstr id :: nil)
      end.

 End Pp. *)

  Section PURITY.

  Variable pure_funs: SSet.t.

  Fixpoint expr_is_pure (e: expr) : bool :=
    match e with
    | ETrue | EFalse | EInt32 _ _ | EInt64 _ _
    | EConstr _ _ _ | EVar _ _ => true
    | ECast e1 _
    | ERecordProj e1 _ _ _
    | EUnaryOp _ e1 _ => expr_is_pure e1
    | EBinaryOp _ e1 e2 _
    | EArrayGet e1 e2 _ _
    | ELetIn _ e1 e2 _ => (expr_is_pure e1) && (expr_is_pure e2)
    | EApp e1 args _ =>
        match e1 with
        | EVar f _ =>
            SSet.mem f pure_funs
            && (List.forallb expr_is_pure args)
        | _ => false
        end
    | EArraySet _ _ _ _
    | ERecordUpdate _ _ _ _ => false
    | EIfThenElse e1 e2 e3 _ =>
        (expr_is_pure e1)
        && (expr_is_pure e2)
        && (expr_is_pure e3)
    | EMatch e cases _ =>
        (expr_is_pure e) && List.forallb (fun '(_, ei) => expr_is_pure ei) cases
    | EAttr _ e => expr_is_pure e
    end.

  Definition func_is_pure (f: function) : bool :=
    btyp_is_prim (fn_return f) && expr_is_pure (fn_body f).

  End PURITY.

  Definition pure_functions (prog: program) : SSet.t :=
    List.fold_left
      (fun acc def =>
        match def with
        | DefFun x f =>
            if func_is_pure acc f then (SSet.add x acc)
            else acc
        | _ => acc
        end)
      prog
      SSet.empty.
  
End Typed.

Module BarocqTyped := Barocq.Typed.

Module Typing.

  Import BarocqTyped.

  Section ARCHI.

  Variable arch : Target.archi.

  Fixpoint typecheck_expr (be: benv) (gx: gcontext) (lx: lcontext) (e: Barocq.expr) : res BarocqTyped.expr :=
    match e with
    | Barocq.ETrue => ret ETrue
    | Barocq.EFalse => ret EFalse
    | Barocq.EInt32 i s => ret (EInt32 i s)
    | Barocq.EInt64 i s => ret (EInt64 i s)
    | Barocq.EConstr x =>
        let* t := typof_constr be x in
        let* z := zval_of_constr be t x in
        ret (EConstr x (Int.repr z) t)
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
        let* (t, ly) := typecheck_array_get2 arch (typof_expr e1') (typof_expr e2') in
        ret (EArrayGet e1' e2' ly t)
    | Barocq.EArraySet e1 e2 e3 =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* e2' := typecheck_expr be gx lx e2 in
        let* e3' := typecheck_expr be gx lx e3 in
        let* t := typecheck_array_set arch (typof_expr e1') (typof_expr e2') (typof_expr e3') in
        ret (EArraySet e1' e2' e3' t)
    | Barocq.ERecordProj e1 x =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* (t, ly) := typecheck_record_proj2 be (typof_expr e1') x in
        ret (ERecordProj e1' x ly t)
    | Barocq.ERecordUpdate e1 x e2 =>
        let* e1' := typecheck_expr be gx lx e1 in
        let* e2' := typecheck_expr be gx lx e2 in
        let* t := typecheck_record_update be (typof_expr e1') (typof_expr e2') x in
        ret (ERecordUpdate e1' x e2' t)
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
    | Barocq.EAttr _ e => typecheck_expr be gx lx e
    end.

  Definition typecheck_function (arch: Target.archi) (be: benv) (gx: gcontext) (f: Barocq.function) : res BarocqTyped.function :=
    let* lx :=
      list_fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        (fn_params f)
        ( STree.empty)
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
        if btyp_eq_dec ty (typof_literal l') then
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
  (** The denotational semantics lifts programs to evaluable Rocq terms. *)

  Variable arch : Target.archi.

  Variable tabs : PMap.t Type.

  Local Notation eval_typ := (Types.eval_typ tabs).

  Local Notation genv := (genv tabs).

  Local Notation lenv := (lenv tabs).

  Definition typof_expr (te:tenv) (e:expr) : res typ :=
    btyp_to_typ te (typof_expr e).

  Fixpoint eval_expr (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr)  : res (eval_typ ty) :=
    match e with
    | ETrue  => @cast_typ tabs TBool true ty
    | EFalse => @cast_typ tabs TBool false ty
    | EInt32 i s => @cast_typ tabs (TInt32 s) i ty
    | EInt64 i s => @cast_typ tabs (TInt64 s) i ty
    | EConstr x _ _  => eval_constr tabs te x ty
    | EVar x _ => eval_var tabs ge le x ty
    | ECast e1 tr =>
        let* tr' := btyp_to_typ te tr in
        let* te1  := typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1  in
        ecast_typ tabs (eval_cast tabs te1 v1 tr') ty
    | EUnaryOp op e bt =>
        let* tye := btyp_to_typ te bt in
        let* v := eval_expr te ge le tye e in
        eval_unary_op tabs op tye v ty
    | EBinaryOp op e1 e2 bt =>
        let* tye1 := typof_expr te e1 in
        let* tye2  := typof_expr te e2 in
        let* v1 := eval_expr te ge le tye1 e1  in
        let* v2 := eval_expr te ge le tye2 e2  in
        eval_binary_op tabs op tye1 tye2 v1 v2 ty
    | EArrayGet e1 e2 _ _ =>
        let* tye1 := typof_expr te e1 in
        let* tye2 := typof_expr te e2 in
        let* v1 := eval_expr te ge le tye1 e1  in
        let* v2 := eval_expr te ge le tye2 e2  in
        eval_array_get  arch tabs tye1 v1 tye2 v2 ty
    | EArraySet e1 e2 e3 _ =>
        let* tye1 := typof_expr te e1 in
        let* tye2 := typof_expr te e2 in
        let* tye3 := typof_expr te e3 in
        let* v1 := eval_expr te ge le tye1 e1 in
        let* v2 := eval_expr te ge le tye2 e2 in
        let* v3 := eval_expr te ge le tye3 e3 in
        eval_array_set arch tabs tye1 v1 tye2 v2 tye3 v3 ty
    | ERecordProj e k _ _ =>
        let* tye := typof_expr te e in
        let* v := eval_expr te ge le tye e in
        eval_record_project tabs tye v k ty
    | ERecordUpdate e1 k e2 _ =>
        let* te1 := typof_expr te e1 in
        let* te2 := typof_expr te e2 in
        let* v1 := eval_expr te ge le te1 e1 in
        let* v2 := eval_expr te ge le te2 e2 in
        eval_record_update tabs te1 v1 k te2 v2 ty
    | EApp v args _ =>
        let* tyf := typof_expr te v in
        match tyf with
        | TFun tparams tret =>
            let* f := eval_expr te ge le  (TFun tparams tret) v in
            let* vargs := DList.map2 _ (eval_expr te ge le) args tparams in
            eval_app_res tabs tparams tret f vargs ty
        |  _  => fail
        end
    | EIfThenElse e1 e2 e3 _ =>
        let* v1 := eval_expr te ge le TBool e1  in
        let* te2 := typof_expr te e2 in
        let* te3 := typof_expr te e3 in
        let v2 := eval_expr te ge le te2 e2 in
        let v3 := eval_expr te ge le te3 e3  in
        eval_ifthenelse  tabs v1 te2 v2 te3 v3 ty
    | EMatch e1 cases _  =>
        let* te1:= typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1 in
        let vcases := MapList.map (eval_expr te ge le ty) cases in
        eval_match tabs te1 v1 ty vcases
    | ELetIn x e1 e2 _ =>
        let* te1 := typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1 in
        let le' := lenv_update tabs le x (Val tabs te1 v1) in
        eval_expr te ge le' ty e2
    | EAttr _ e1 => eval_expr te ge le ty e1
    end.

  Lemma eval_expr_rew : forall (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr),
      eval_expr te ge le ty e =
    match e with
    | ETrue  => @cast_typ tabs TBool true ty
    | EFalse => @cast_typ tabs TBool false ty
    | EInt32 i s => @cast_typ tabs (TInt32 s) i ty
    | EInt64 i s => @cast_typ tabs (TInt64 s) i ty
    | EConstr x _ _  => eval_constr tabs te x ty
    | EVar x _ => eval_var tabs ge le x ty
    | ECast e1 tr =>
        let* tr' := btyp_to_typ te tr in
        let* te1  := typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1  in
        ecast_typ tabs (eval_cast tabs te1 v1 tr') ty
    | EUnaryOp op e bt =>
        let* tye := btyp_to_typ te bt in
        let* v := eval_expr te ge le tye e in
        eval_unary_op tabs op tye v ty
    | EBinaryOp op e1 e2 bt =>
        let* tye1 := typof_expr te e1 in
        let* tye2  := typof_expr te e2 in
        let* v1 := eval_expr te ge le tye1 e1  in
        let* v2 := eval_expr te ge le tye2 e2  in
        eval_binary_op tabs op tye1 tye2 v1 v2 ty
    | EArrayGet e1 e2 _ _ =>
        let* tye1 := typof_expr te e1 in
        let* tye2 := typof_expr te e2 in
        let* v1 := eval_expr te ge le tye1 e1  in
        let* v2 := eval_expr te ge le tye2 e2  in
        eval_array_get  arch tabs tye1 v1 tye2 v2 ty
    | EArraySet e1 e2 e3 _ =>
        let* tye1 := typof_expr te e1 in
        let* tye2 := typof_expr te e2 in
        let* tye3 := typof_expr te e3 in
        let* v1 := eval_expr te ge le tye1 e1 in
        let* v2 := eval_expr te ge le tye2 e2 in
        let* v3 := eval_expr te ge le tye3 e3 in
        eval_array_set arch tabs tye1 v1 tye2 v2 tye3 v3 ty
    | ERecordProj e k _ _ =>
        let* tye := typof_expr te e in
        let* v := eval_expr te ge le tye e in
        eval_record_project tabs tye v k ty
    | ERecordUpdate e1 k e2 _ =>
        let* te1 := typof_expr te e1 in
        let* te2 := typof_expr te e2 in
        let* v1 := eval_expr te ge le te1 e1 in
        let* v2 := eval_expr te ge le te2 e2 in
        eval_record_update tabs te1 v1 k te2 v2 ty
    | EApp v args _ =>
        let* tyf := typof_expr te v in
        match tyf with
        | TFun tparams tret =>
            let* f := eval_expr te ge le  (TFun tparams tret) v in
            let* vargs := DList.map2 _ (eval_expr te ge le) args tparams in
            eval_app_res tabs tparams tret f vargs ty
        |  _  => fail
        end
    | EIfThenElse e1 e2 e3 _ =>
        let* v1 := eval_expr te ge le TBool e1  in
        let* te2 := typof_expr te e2 in
        let* te3 := typof_expr te e3 in
        let v2 := eval_expr te ge le te2 e2 in
        let v3 := eval_expr te ge le te3 e3  in
        eval_ifthenelse  tabs v1 te2 v2 te3 v3 ty
    | EMatch e1 cases _  =>
        let* te1:= typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1 in
        let vcases := MapList.map (eval_expr te ge le ty) cases in
        eval_match tabs te1 v1 ty vcases
    | ELetIn x e1 e2 _ =>
        let* te1 := typof_expr te e1 in
        let* v1 := eval_expr te ge le te1 e1 in
        let le' := lenv_update tabs le x (Val tabs te1 v1) in
        eval_expr te ge le' ty e2
    | EAttr _ e1 => eval_expr te ge le ty e1
    end.
  Proof.
    destruct e; reflexivity.
  Qed.

  Fixpoint eval_literal (te: tenv) (l: literal) : res (value tabs) :=
    match l with
    | LTrue => ret (Val tabs TBool true)
    | LFalse => ret (Val tabs TBool false)
    | LInt32 i s => ret (Val tabs (TInt32 s) i)
    | LInt64 i s => ret (Val tabs (TInt64 s) i)
    | LArray a _ _ =>
        let* av := mmap (eval_literal te) a in
        eval_array_lit tabs av
    | LRecord rc _ rid =>
        let* rcv := MapList.map_err (eval_literal te) rc in
        let* fields := TEnv.get_rdef te rid in
        eval_record_lit tabs rid rcv fields
    end.

  Definition cast_typ_M (tret:typ) (v: value tabs ) : M (eval_typ tret) :=
    match v with
      | Val _ tv v =>
          match typ_eq_dec tv tret with
          | left e =>  (ret (typ_cast tabs e v))
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

  Fixpoint eval_fun_rec (te: tenv) (ge: genv) (le: lenv) (params: smaplist typ) (tret: typ) (e: expr) :
    eval_funtyp eval_typ (List.map snd params) (eval_typ tret) :=
    match params with
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
          fun _ => eval_expr te ge (lenv_update tabs le (fst p) (Val tabs (snd p) y)) tret e
      | p0 :: l0 =>
          fun
            eval_fun_rec  => eval_fun_rec
      end (eval_fun_rec te ge (lenv_update tabs le (fst p) (Val tabs (snd p) y)) l tret e)
  end.

  Lemma eval_fun_rec_rw : forall (te: tenv) (ge: genv) (le: lenv) (params: smaplist typ) (tret: typ) (e: expr),
    eval_fun_rec te ge le params tret e =
    match params with
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
          fun _ => eval_expr te ge (lenv_update tabs le (fst p) (Val tabs (snd p) y)) tret e
      | p0 :: l0 =>
          fun 
            eval_fun_rec  => eval_fun_rec
      end (eval_fun_rec te ge (lenv_update tabs le (fst p) (Val tabs (snd p) y)) l tret e)
  end.
  Proof.
    destruct params;reflexivity.
  Qed.

  Definition eval_fun (te: tenv) (ge: genv) (params: smaplist typ) (tret: typ) (e: expr) : eval_typ (TFun (List.map (fun x => snd x) params) tret).
    destruct params as [| p params'].
    - simpl.
      intro.
      apply (eval_expr te ge STree.empty tret e).
    - apply (eval_fun_rec te ge STree.empty (p :: params') tret e).
  Defined.


  Definition mk_fun_value (te: tenv) (ge: genv) (params: smaplist btyp) (tret: btyp) (e: expr) : res (value tabs) :=
    if MapList.nodup Ident.eq_dec params then
      let* tret' := btyp_to_typ te tret in
      let* params' := MapList.map_err (btyp_to_typ te) params in
      ret (Val tabs (TFun (List.map (fun x => snd x) params') tret') (eval_fun te ge params' tret' e))
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

  Definition eval_def_const (te: tenv) (ge: genv) (x: ident) (l: literal) (ty: btyp) : res (genv) :=
    let* ty' := btyp_to_typ te ty in
    let* vv := eval_literal te l in
    let* v'  := cast_value tabs vv ty' in
    genv_update tabs ge x (Val tabs ty' v').

  Definition eval_def_fun (te: tenv) (ge: genv) (x: ident) (f: function) : res (genv) :=
    let* fv := mk_fun_value te ge (fn_params f) (fn_return f) (fn_body f) in
    genv_update tabs ge x fv.

  Definition eval_decl_const (te: tenv) (ge : genv) (x:ident) (bt:btyp) :=
    let* ty :=  Typing.btyp_to_typ te bt  in
    let* v  := genv_get tabs ge x in
    if typ_eq_dec ty (typeof_value tabs v) then eret tt else fail.

  Definition eval_decl_fun (te:tenv) (ge : genv) (x:Syntax.ident) (params : list (Syntax.param_attr * btyp)) (tret:btyp) :=
    let* tparam := mmap (Typing.btyp_to_typ te) (List.map snd params) in
    let* tret   := Typing.btyp_to_typ te tret in
    let* v := genv_get tabs ge x in
    if (typ_eq_dec (TFun tparam tret) (typeof_value tabs v)) then eret tt else fail.


  (** Interpreter *)
  Fixpoint interpret_rec (te: tenv) (ge: genv) (cmds: list command) : res (list (value tabs)) :=
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
            ret (Val tabs ty v :: l)
        end
    end.

  Definition interpret (iprog: list command) : res (list (value tabs)) :=
    interpret_rec TEnv.empty STree.empty iprog.

  (** Evaluation of a definition with dynamic environments *)

  Fixpoint eval_def_rec (te: tenv) (ge: genv) (prog: program) (x: ident) : res (value tabs) :=
    match prog with
    | nil => fail
    | d :: prog' =>
        match d with
        | DefType y td =>
            let* te' := eval_def_type te x td in
            eval_def_rec te' ge prog' y
        | DefConst y l ty =>
            let* ge' := eval_def_const te ge y l ty in
            if Ident.eq_dec x y then genv_get tabs ge' x
            else eval_def_rec te ge' prog' x
        | DefFun y f =>
            let* ge':= eval_def_fun te ge y f in
            if Ident.eq_dec x y then genv_get tabs ge' x
            else eval_def_rec te ge' prog' x
        | DeclType _ _ => eval_def_rec te ge prog' x
        | DeclConst y _
        | DeclFun y _ _ =>
            if Ident.eq_dec x y then genv_get tabs ge x
            else eval_def_rec te ge prog' x
        end
    end.

  Definition eval_value_err_typ (rv: res (value tabs)) : Type :=
    match rv with
    | OK (Val _ tv v) => eval_typ tv
    | Error _ => unit
    end.

  Definition eval_def (impl: genv) (prog: program) (x: ident) : res (value tabs) :=
    eval_def_rec TEnv.empty impl prog x.

  (** Evaluation of a whole program *)

  Fixpoint eval_prog_rec (te: tenv) (ge: (genv)) (prog: program) : res (tenv * (genv)) :=
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

  Definition eval_prog (impl: genv) (prog: program) : res (tenv* (genv)) :=
    eval_prog_rec TEnv.empty impl prog.

  (** Redefinition of eval_def by computing the whole global environment first *)

  Definition eval_def2 (impl: genv) (prog: program) (x: ident) : res (value tabs) :=
    let* (_, ge) := eval_prog impl prog in
    genv_get tabs ge x.

End DENOT.
