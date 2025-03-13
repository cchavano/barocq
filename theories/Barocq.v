From Coq Require Import List String ListDec PArith Bool.
From compcert Require Import Integers.
From BarocqComp Require Import Error MapList Common Array Struct Types Typing Syntax.
Import ListNotations.

(** * Abstract syntax *)

(** ** Expressions *)

Inductive expr : Type :=
  | ETrue : expr                                            (* true constant *)
  | EFalse : expr                                           (* false constant *)
  | EInt32 (i: int) : expr                                  (* 32-bit integer *)
  | EInt64 (i: int64) : expr                                (* 64-bit integer *)    
  | EVar (x: ident) : expr                                  (* variable *)
  | EUnaryOp (op: unary_op) (e: expr) : expr                (* op e *)
  | EBinaryOp (op: binary_op) (e1 e2 : expr) : expr         (* e1 op e2 *)
  | EArrayGet (a i: expr) : expr                            (* a[i] *)
  | EArraySet (a i e: expr) : expr                          (* a[i] <- e *)
  | EStructProj (st: expr) (x: ident) : expr                (* st.x *)
  | EStructUpdate (st: expr) (x: ident) (e: expr) : expr    (* st.x <- e *)
  | EApp (e: expr) (args: list expr) : expr                 (* e (args) *)
  | EIfThenElse (e1 e2 e3: expr) : expr                     (* if e1 then e2 else e3 *)
  | ELetIn (x: ident) (e1 e2: expr) : expr.                 (* let x = e1 in e2 *)

(** ** Functions *)

Definition function : Type := Syntax.function expr.

(** ** Global definitions *)

Inductive globdef : Type :=
  | DefStruct (a: ident) (fields: list (ident * ctyp)) : globdef    (* struct a = { x1: t1; ...; xn: tn; } *)
  | DefConst (x: ident) (l: literal) (ty: ctyp) : globdef           (* def x : ty = l *)
  | DefFun (x: ident) (f: function) : globdef.                      (* def f (p1: t1, ..., pn: tn) : ty = e *)

(** ** Programs *)

(** We differentiate between "programs" that only contain definitions and 
    "executable (= interpretable) programs" which also contains top-level
    expressions to be evaluated. Only definitions are compiled down to C. *)

Definition program : Type := list globdef.

Inductive command : Type :=
  | CmdDef (def: globdef) : command      (* top level definition *)
  | CmdExpr (e: expr) : command.         (* top level expression to be evaluated *)

Definition xprogram : Type := list command.

Definition xprog_to_prog (xprog: xprogram) : program :=
  fold_right
    (fun cmd acc =>
      match cmd with
      | CmdDef def => def :: acc 
      | CmdExpr e => acc
      end)
    nil
    xprog.

Module Typed.

  (** * Typed abstract syntax *)

  (** ** Expressions *)

  Inductive expr : Type :=
    | ETrue : ctyp -> expr
    | EFalse : ctyp -> expr
    | EInt32 : int -> ctyp -> expr
    | EInt64 : int64 -> ctyp -> expr
    | EVar : ident -> ctyp -> expr
    | EUnaryOp : unary_op -> expr -> ctyp -> expr
    | EBinaryOp : binary_op -> expr -> expr -> ctyp -> expr
    | EArrayGet : expr -> expr -> ctyp -> expr
    | EArraySet : expr -> expr -> expr -> ctyp -> expr
    | EStructProj : expr -> ident -> ctyp -> expr
    | EStructUpdate : expr -> ident -> expr -> ctyp -> expr
    | EApp : expr -> list expr -> ctyp -> expr
    | EIfThenElse : expr -> expr -> expr -> ctyp -> expr
    | ELetIn : ident -> expr -> expr -> ctyp -> expr.

  (** ** Functions *)

  Definition function : Type := Syntax.function expr.

  (** ** Global definitions *)

  Inductive globdef : Type :=
    | DefStruct : ident -> list (ident * ctyp) -> globdef
    | DefConst : ident -> literal -> ctyp -> globdef
    | DefFun : ident -> function -> globdef.    

  (** ** Programs *)

  Definition program : Type := list globdef.

End Typed.

Module BarocqTyped := Barocq.Typed.

Module Typing.

  Import BarocqTyped.

  Definition typof_expr (e: expr) : ctyp :=
    match e with
    | ETrue ty
    | EFalse ty
    | EInt32 _ ty
    | EInt64 _ ty
    | EVar _ ty
    | EUnaryOp _ _ ty
    | EBinaryOp _ _ _ ty
    | EArrayGet _ _ ty
    | EArraySet _ _ _ ty
    | EStructProj _ _ ty
    | EStructUpdate _ _ _ ty
    | EApp _ _ ty
    | EIfThenElse _ _ _ ty
    | ELetIn _ _ _ ty => ty
    end.

  Fixpoint typecheck_expr (ts: types) (gx: gcontext) (lx: lcontext) (e: Barocq.expr) : res BarocqTyped.expr :=
    match e with
    | Barocq.ETrue => ret (ETrue CBool)
    | Barocq.EFalse => ret (EFalse CBool)
    | Barocq.EInt32 i => ret (EInt32 i CInt32)
    | Barocq.EInt64 i => ret (EInt64 i CInt64)
    | Barocq.EVar x =>
        let* t := typof_var gx lx x in
        ret (EVar x t)
    | Barocq.EUnaryOp op e1 =>
        let* e1' := typecheck_expr ts gx lx e1 in
        let* t := typecheck_unary_op op (typof_expr e1') in
        ret (EUnaryOp op e1' t)
    | Barocq.EBinaryOp op e1 e2 =>
        let* e1' := typecheck_expr ts gx lx e1 in
        let* e2' := typecheck_expr ts gx lx e2 in
        let* t := typecheck_binary_op op (typof_expr e1') (typof_expr e2') in
        ret (EBinaryOp op e1' e2' t)
    | Barocq.EArrayGet e1 e2 =>
        let* e1' := typecheck_expr ts gx lx e1 in
        let* e2' := typecheck_expr ts gx lx e2 in
        let* t := typecheck_array_get (typof_expr e1') (typof_expr e2') in
        ret (EArrayGet e1' e2' t)
    | Barocq.EArraySet e1 e2 e3 =>
        let* e1' := typecheck_expr ts gx lx e1 in
        let* e2' := typecheck_expr ts gx lx e2 in
        let* e3' := typecheck_expr ts gx lx e3 in
        let* t := typecheck_array_set (typof_expr e1') (typof_expr e2') (typof_expr e3') in
        ret (EArraySet e1' e2' e3' t)
    | Barocq.EStructProj e1 x =>
        let* e1' := typecheck_expr ts gx lx e1 in
        let* t := typecheck_struct_proj ts (typof_expr e1') x in
        ret (EStructProj e1' x t)
    | Barocq.EStructUpdate e1 x e2 =>
        let* e1' := typecheck_expr ts gx lx e1 in
        let* e2' := typecheck_expr ts gx lx e2 in
        let* t := typecheck_struct_update ts (typof_expr e1') (typof_expr e2') x in
        ret (EStructUpdate e1' x e2' t)
    | Barocq.EApp e1 args =>
        let* e1' := typecheck_expr ts gx lx e1 in
        let* args' := mmap (typecheck_expr ts gx lx) args in
        let targs := map typof_expr args' in 
        let* t := typecheck_call (typof_expr e1') targs in
        ret (EApp e1' args' t)
    | Barocq.EIfThenElse e1 e2 e3 =>
        let* e1' := typecheck_expr ts gx lx e1 in
        let* e2' := typecheck_expr ts gx lx e2 in
        let* e3' := typecheck_expr ts gx lx e3 in
        let '(ty1, ty2, ty3) := (typof_expr e1', typof_expr e2', typof_expr e3') in
        match ty1 with
        | CBool =>
            if ctyp_eq_dec ty2 ty3 then
              ret (EIfThenElse e1' e2' e3' ty2)
            else fail
        | _ => fail
        end
    | Barocq.ELetIn x e1 e2 =>
        let* e1' := typecheck_expr ts gx lx e1 in
        let* lx' := lcontext_update lx x (typof_expr e1') in
        let* e2' := typecheck_expr ts gx lx' e2 in
        ret (ELetIn x e1' e2' (typof_expr e2'))
    end.

  Definition typecheck_function (ts: types) (gx: gcontext) (f: Barocq.function) : res BarocqTyped.function :=
    let* lx :=
      fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        (fn_params f)
        (ret tempty)
    in
    let* body := typecheck_expr ts gx lx (fn_body f) in
    if ctyp_eq_dec (typof_expr body) (fn_return f) then
      ret {|
        fn_return := fn_return f;
        fn_params := fn_params f;
        fn_body := body
      |}
    else failwith "Barocq.Typing.typecheck_function: return type mismatch".

  Fixpoint typecheck_globdefs (ts: types) (gx: gcontext) (defs: list Barocq.globdef) : res (list BarocqTyped.globdef) :=
    match defs with
    | nil => ret nil
    | Barocq.DefStruct x fields :: defs' =>
        let* ts' := types_update ts x fields in
        let* rd := typecheck_globdefs ts' gx defs' in
        ret ((DefStruct x fields) :: rd)
    | Barocq.DefConst x l ty :: defs' =>
        let* l' := typecheck_literal ts l in
        if ctyp_eq_dec ty (Typing.typof_literal l') then
          let* gx' := gcontext_update gx x ty in
          let* rd := typecheck_globdefs ts gx' defs' in
          ret (DefConst x l ty :: rd)
        else
          failwith "Barocq.Typing.typecheck_globdef: type mismatch in constant definition"
    | Barocq.DefFun x f :: defs' =>
        let* f' := typecheck_function ts gx f in
        let tf := cfun_typ (fn_params f') (fn_return f') in
        let* gx' := gcontext_update gx x tf in
        let* rd := typecheck_globdefs ts gx' defs' in
        ret (DefFun x f' :: rd)
    end.

  Definition typecheck_program (prog: Barocq.program) : res BarocqTyped.program :=
    typecheck_globdefs tempty tempty prog.

End Typing.

(** * Denotational semantics *)

Section DENOT.

  (** The denotational semantics lifts programs to evaluable Coq terms. *)

  Inductive value : Type :=
    | Val (t: typ) (v: eval_typ t) : value.

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

  Definition eval_unary_op (op: unary_op) (v: value) : res value :=
    match op, v with
    | UopNotbool, Val TBool b => ret (Val TBool (negb b))
    | UopNotint, Val TInt32 i => ret (Val TInt32 (Int.not i))
    | UopNeg, Val TInt32 i => ret (Val TInt32 (Int.neg i))
    | UopNotint, Val TInt64 i => ret (Val TInt64 (Int64.neg i))
    | UopNeg, Val TInt64 i => ret (Val TInt64 (Int64.not i))
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
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.add i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.add i1 i2))
        | _, _ => fail
        end
    | BopSub =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.sub i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.sub i1 i2))
        | _, _ => fail
        end
    | BopMul =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.mul i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.mul i1 i2))
        | _, _ => fail
        end
    | BopDiv =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.divs i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.divs i1 i2))
        | _, _ => fail
        end
    | BopMod =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.mods i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.mods i1 i2))
        | _, _ => fail
        end
    | BopAndint =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.and i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.and i1 i2))
        | _, _ => fail
        end
    | BopOrint =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.or i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.or i1 i2))
        | _, _ => fail
        end
    | BopXorint =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.xor i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.xor i1 i2))
        | _, _ => fail
        end
    | BopShl =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.shl i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.shl i1 i2))
        | _, _ => fail
        end
    | BopShr =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TInt32 (Int.shr i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TInt64 (Int64.shr i1 i2))
        | _, _ => fail
        end
    | BopEq =>
        match v1, v2 with
        | Val TBool b1, Val TBool b2 => ret (Val TBool (eqb b1 b2))
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TBool (Int.eq i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TBool (Int64.eq i1 i2))
        | _, _ => fail
        end
    | BopNeq =>
        match v1, v2 with
        | Val TBool b1, Val TBool b2 => ret (Val TBool (negb (eqb b1 b2)))
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TBool (Int.cmp Cne i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TBool (Int64.cmp Cne i1 i2))
        | _, _ => fail
        end
    | BopLt =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TBool (Int.lt i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TBool (Int64.lt i1 i2))
        | _, _ => fail
        end
    | BopGt =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TBool (Int.cmp Cgt i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TBool (Int64.cmp Cgt i1 i2))
        | _, _ => fail
        end
    | BopLe =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TBool (Int.cmp Cle i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TBool (Int64.cmp Cle i1 i2))
        | _, _ => fail
        end
    | BopGe =>
        match v1, v2 with
        | Val TInt32 i1, Val TInt32 i2 => ret (Val TBool (Int.cmp Cge i1 i2))
        | Val TInt64 i1, Val TInt64 i2 => ret (Val TBool (Int64.cmp Cge i1 i2))
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
                ret (Val (TArray ta) ((typ_cast eq x) :: xa))
            | _ => fail
            end
        | _ => fail
        end
    end.

  Fixpoint eval_struct_lit_rec (lv: list (ident * value)) (fields: list (ident * typ)) : res (eval_structtyp eval_typ fields).
    destruct lv as [|[x [tv v]] lv'] eqn:Elv; destruct fields as [| [y t] fields'] eqn:Efields.
    - apply (ret tt).
    - apply fail.
    - apply fail.
    - destruct (ident_eq_dec x y).
      + subst. destruct (typ_eq_dec tv t).
        * subst. destruct (eval_struct_lit_rec lv' fields') as [st |].
          -- unfold eval_structtyp in *. simpl in *.
             apply (ret (Field y v, st)).
          -- apply fail.
        * apply fail.
      + apply fail.
  Defined.  

  Definition eval_struct_lit (n: ident) (lv: list (ident * value)) (fields: list (ident * typ)) : res value.
    destruct lv as [|x lv'].
    - apply fail.
    - destruct (eval_struct_lit_rec (x :: lv') fields) as [r |].
      * apply (ret (Val (TStruct n fields) r)).
      * apply fail.
  Defined.

  Definition eval_array_get (v1 v2: value) : res value :=
    match v1, v2 with
    | Val (TArray t) a, Val TInt32 i=>
        let* v := Array.get a i in
        ret (Val t v)
    | _, _ => fail
    end.

  Definition eval_array_set (v1 v2 v3: value) : res value :=
    match v1, v2, v3 with
    | Val (TArray ta) a, Val TInt32 i, Val t v =>
        match (typ_eq_dec t ta) with
        | left eq =>
            let* a' := Array.set a i (typ_cast eq v) in
            ret (Val (TArray ta) a')
        | _ => fail
        end
    | _, _, _ => fail
    end.

  Lemma typof_field_is_type :
    forall (fields: list (ident * typ)) k t,
    typof_field k fields = OK t ->
    eval_typ t = type_of_field k (eval_fields_typ eval_typ fields).
  Proof.
    induction fields as [| (x, t) fields']; intros.
    - simpl in H. discriminate.
    - unfold typof_field in *. unfold find_k_err in *.
      unfold type_of_field in *. unfold find_k in *.
      simpl. simpl in H. unfold ident_eq_dec in H.
      unfold key_eq_dec. destruct (Pos.eq_dec x k).
      + inversion H. reflexivity.
      + apply (IHfields' k t0 H). 
  Defined.

  Definition eval_struct_proj_aux (fields: list (ident * typ)) (st: eval_structtyp eval_typ fields) (k: ident) : res value.
    simpl in st. destruct (proj st k) as [v |].
    - destruct (typof_field k fields) as [t |] eqn:Etyp.
      + rewrite <- (typof_field_is_type fields k t Etyp) in v.
        apply (ret (Val t v)).
      + apply fail.
    - apply fail.
  Defined.

  Definition eval_struct_proj (v: value) (k: ident) : res value :=
    match v with
    | Val (TStruct _ fields) st => eval_struct_proj_aux fields st k
    | _ => fail
    end.

  Definition eval_struct_update_aux (n: ident) (fields: list (ident * typ)) (st: eval_typ (TStruct n fields)) (k: ident) (v: value) : res value.
    simpl in st. destruct v as [tv v]. destruct (typof_field k fields) as [t |] eqn:Etyp.
    - destruct (typ_eq_dec tv t) as [Eqt |_].
      + apply (typof_field_is_type fields k t) in Etyp.
        rewrite Eqt in v. rewrite Etyp in v.
        destruct (update st k v) as [st' |].
        * apply (ret (Val (TStruct n fields) st')).
        * apply fail.
      + apply fail.
    - apply fail.
  Defined.

  Definition eval_struct_update (v1: value) (k: ident) (v2: value) : res value :=
    match v1 with
    | Val (TStruct n fields) st => eval_struct_update_aux n fields st k v2
    | _ => fail
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
      + apply (eval_app_rec tparams' tret (f (typ_cast Heqtv v)) args').
      + apply fail.
  Defined.

  Definition eval_app (v: value) (args: list value) : res value.
    destruct v as [t vt]. destruct t as [ | | | | fields | tparams tret].
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
  Defined.

  Fixpoint eval_expr (te: tenv) (ge: genv) (le: lenv) (e: expr) : res value :=
    match e with
    | ETrue => ret (Val TBool true)
    | EFalse => ret (Val TBool false)
    | EInt32 i => ret (Val TInt32 i)
    | EInt64 i => ret (Val TInt64 i)
    | EVar x => eval_var ge le x
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
    | EStructProj e k =>
        let* v := eval_expr te ge le e in
        eval_struct_proj v k
    | EStructUpdate e1 k e2 =>
        let* v1 := eval_expr te ge le e1 in
        let* v2 := eval_expr te ge le e2 in
        eval_struct_update v1 k v2
    | EApp v args =>
        let* f := eval_expr te ge le v in
        let* vargs :=
          mmap
            (fun e => eval_expr te ge le e)
            args
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
    end.

  Fixpoint eval_literal (te: tenv) (l: literal) : res value :=
    match l with
    | LTrue => ret (Val TBool true)
    | LFalse => ret (Val TBool false)
    | LInt32 i => ret (Val TInt32 i)
    | LInt64 i => ret (Val TInt64 i)
    | LArray a =>
        let* av := mmap (eval_literal te) a in
        eval_array_lit av
    | LStruct st x =>
        let* stv := map_k_err (eval_literal te) st in
        let* fields := tenv_get te x in
        eval_struct_lit x stv fields
    end.

  Fixpoint build_funval_rec_aux (te: tenv) (ge: genv) (le: lenv) (params: list (ident * typ)) (tret: typ) (e: expr) : eval_funtyp eval_typ (map (fun x => snd x) params) tret.
    destruct params as [| (x, tx) params'].
    - simpl. destruct (eval_expr te ge le e) as [[tv v]|].
      + destruct (typ_eq_dec tv tret).
        * apply (ret (typ_cast e0 v)).
        * apply fail.
      + apply (Error e0).
    - simpl. apply (fun (y: eval_typ tx) => build_funval_rec_aux te ge (lenv_update le x (Val tx y)) params' tret e).
  Defined.

  Definition build_funval_rec := Eval cbv delta [build_funval_rec_aux] zeta beta in build_funval_rec_aux.

  Definition build_funval (te: tenv) (ge: genv) (params: list (ident * typ)) (tret: typ) (e: expr) : eval_typ (TFun (map (fun x => snd x) params) tret).
    destruct params as [| p params'].
    - simpl. destruct (eval_expr te ge tempty e) as [[tv v] |].
      + destruct (typ_eq_dec tv tret).
        -- apply (fun (_: unit) => ret (typ_cast e0 v)).
        -- apply (fun (_: unit) => fail).
      + apply (fun (_: unit) => (Error e0)).
    - apply (build_funval_rec te ge tempty (p :: params') tret e).
  Defined.

  Definition build_fun_value (te: tenv) (ge: genv) (params: list (ident * ctyp)) (tret: ctyp) (e: expr) : res value :=
    if nodup_k ident_eq_dec params then
      let* tret' := ctyp_to_typ te tret in
      let* params' := map_k_err (ctyp_to_typ te) params in
      ret (Val (TFun (map (fun x => snd x) params') tret') (build_funval te ge params' tret' e))
    else fail.

  Definition fields_ctyp_to_typ (te: tenv) (fields: list (ident * ctyp)) : res (list (ident * typ)) :=
    map_k_err (ctyp_to_typ te) fields.

  Fixpoint interpret_rec (te: tenv) (ge: genv) (xprog: xprogram) : res (list value) :=
    match xprog with
    | nil => ret nil
    | c :: xprog' =>
        match c with
        | CmdDef (DefStruct a fields) =>
            let* fields' := fields_ctyp_to_typ te fields in
            let* te' := tenv_update te a fields' in
            interpret_rec te' ge xprog'
        | CmdDef (DefConst x l ty) =>
            let* vv := eval_literal te l in
            let '(Val tv v) := vv in
            let* ty' := ctyp_to_typ te ty in
            if typ_eq_dec tv ty' then
              let* ge' := genv_update ge x vv in
              interpret_rec te ge' xprog'
            else fail
        | CmdDef (DefFun x f) =>
            let* fv := build_fun_value te ge (fn_params f) (fn_return f) (fn_body f) in
            let* ge' := genv_update ge x fv in
            interpret_rec te ge' xprog'
        | CmdExpr e =>
            let* v := eval_expr te ge tempty e in
            let* l := interpret_rec te ge xprog' in
            ret (v :: l)
        end
    end.

  Definition interpret (xprog: xprogram) : res (list value) :=
    interpret_rec tempty tempty xprog.

  Fixpoint eval_def_rec (te: tenv) (ge: genv) (prog: program) (x: ident) : res value :=
    match prog with
    | nil => fail
    | DefStruct a fields :: prog' =>
        let* fields' := fields_ctyp_to_typ te fields in
        let* te' := tenv_update te a fields' in
        eval_def_rec te' ge prog' x
    | DefConst y l ty :: prog' =>
        let* vv := eval_literal te l in
        if ident_eq_dec x y then ret vv
        else
          let '(Val tv v) := vv in
          let* ty' := ctyp_to_typ te ty in
          if typ_eq_dec tv ty' then
            let* ge' := genv_update ge y vv in
            eval_def_rec te ge' prog' x
          else fail
    | DefFun y f :: prog' =>
        let* fv := build_fun_value te ge (fn_params f) (fn_return f) (fn_body f) in
        if ident_eq_dec x y then ret fv
        else
          let* ge' := genv_update ge y fv in
          eval_def_rec te ge' prog' x
    end.

  Definition eval_value_err_typ (rv: res value) : Type :=
    match rv with
    | OK (Val tv v) => eval_typ tv
    | Error _ => unit
    end.

  Definition eval_def_aux (prog: program) (x: ident) : res value :=
    eval_def_rec tempty tempty prog x.

  Definition eval_def (prog: program) (x: ident) : eval_value_err_typ (eval_def_aux prog x).
    destruct (eval_def_aux prog x) as [[tv v]|].
    - simpl. apply v.
    - simpl. apply tt.
  Defined.

  Fixpoint eval_struct_ctyp_rec (te: tenv) (prog: program) (t: ident) : res typ :=
    match prog with
    | nil => fail
    | DefStruct a fields :: prog' =>
        let* fields' := fields_ctyp_to_typ te fields in
        if ident_eq_dec a t then ret (TStruct a fields')
        else
          let* te' := tenv_update te a fields' in
          eval_struct_ctyp_rec te' prog' t
    | _ :: prog' =>
        eval_struct_ctyp_rec te prog' t
    end.

  Definition eval_struct_ctyp (prog: program) (t: ident) : Type :=
    match (eval_struct_ctyp_rec tempty prog t) with
    | OK t' => eval_typ t'
    | Error _ => unit
    end.

End DENOT.