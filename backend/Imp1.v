From Coq Require Import Bool List String PArith Lia.
From compcert Require Import Integers Maps.
From BarocqComp Require Import  Barocq Benum Barray Brecord Error Maps2 Utils Syntax Types Typing Pp Denot.
From BarocqComp Require Printer.

(** * Abstract syntax *)

(** ** Statements *)
 
Inductive statement : Type :=
  | StSet : ident -> comp -> statement
  | StIfThenElse : atom -> statement -> statement -> statement
  | StSwitch : atom -> list (pattern * statement) -> statement
  | StSequence : statement -> statement -> statement
  | StReturn : atom -> statement
  | StAttr   : ident -> statement -> statement.

(** ** Functions *)

Definition function : Type := Syntax.function statement btyp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef statement btyp literal.

(** ** Programs *)

Definition program : Type := Syntax.program statement btyp literal.

(** * Pretty-printing *)

Module Pp.
  Import String.
  Import ListNotations.

  Fixpoint pp_statement (s:statement) :=
    match s with
    | StSet i c => Bcat (Bstr i) (Bcat (Bstr "=") (Printer.pp_comp c))
    | StIfThenElse a s1 s2 =>
        let s1 := Bcat (Bstr " then ") (pp_statement s1) in
        let s2 := Bcat (Bstr " else ") (pp_statement s2) in
        let c  := Printer.pp_atom a in
        let cd := Bcat (Bstr "if ") c in
        Bstack cd (Bstack s1 s2 Left) Left
    | StSwitch a l => Bstr "case..."
    | StSequence s1 s2 =>
        let s1 := pp_statement s1 in
        let s2 := pp_statement s2 in
        Bstack (Bcat s1 (Bstr ";"))
               s2 Left
    | StReturn a => Bcat (Bstr "return ") (Printer.pp_atom a)
    | StAttr a s => Bcat (Bstr "[#") (Bcat (Bstr a) (Bcat (Bstr "]") (pp_statement s)))
    end.

  Definition pp_program (p:program) := Printer.pp_program  Printer.pp_btyp pp_statement p.

End Pp.

Section TRANSF.
  Variable trans_statement : statement -> res statement.

  Definition trans_function (f:function) :=
    let* b := trans_statement (fn_body f) in
    OK {| fn_return := fn_return f;
          fn_params := fn_params f;
          fn_body   := b
      |}.

  Definition trans_globdef (gd : globdef) : res globdef :=
    match gd with
    | DefFun id f    => let* f' := trans_function f in
                        OK (DefFun id f')
    | _ => OK gd
    end.

  Definition trans_program (p:program) : res program :=
    let* gd' :=  mmap trans_globdef (prog_defs p) in
    OK {|
      prog_defs := gd';
      prog_types := prog_types p;
      prog_tabs := prog_tabs p;
    |}.

End TRANSF.

(** * Denotational functional semantics *)

Section DENOT.

  Variable arch : Target.archi.

  Variable tabs : PMap.t Type.

  Notation genv := (@Denot.genv tabs).

  Notation lenv := (@Denot.lenv tabs).

  Notation value := (@Denot.value tabs).

  Notation eval_typ := (@Types.eval_typ tabs).

  Notation eval_atom := (@Denot.eval_atom arch tabs).

  Notation eval_comp := (@Denot.eval_comp arch tabs).

  Definition typ_of_statement (ty: option typ) : Type :=
    match ty with
    | Some ty => eval_typ ty
    | None => lenv
    end.

  Definition eval_match (tv:typ) (v: eval_typ tv) (tr: option typ) (cases: list (pattern * res (typ_of_statement tr))) : res (typ_of_statement tr) :=
    (match tv as t0 return (eval_typ t0 -> res (typ_of_statement tr)) with
    | TEnum _ elems => 
        (fun v0 => match_with_err v0 cases)
    | _ => (fun _ => fail)
    end) v.

  Fixpoint eval_statement_rec (te: tenv) (ge: genv) (le: lenv) (ty: option typ) (s: statement) : res (typ_of_statement ty) :=
    match s with
    | StSet x c =>
        match ty with
        | None =>
            let* tyc := btyp_to_typ te (typof_comp c) in
            let* vc := eval_comp te ge le tyc c in
            ret (lenv_update tabs le x (Val tabs tyc vc))
        | _ => fail
        end
    | StIfThenElse a s1 s2 =>
        let* va := eval_atom te ge le TBool a in
        if va then eval_statement_rec te ge le ty s1
        else eval_statement_rec te ge le ty s2
    | StSwitch a cases =>
        let* ta := typof_atom te a in
        let* va := eval_atom te ge le ta a in
        let vcases := MapList.map (eval_statement_rec te ge le ty) cases in
        eval_match ta va ty vcases
    | StSequence s1 s2 =>
        let* le1 := eval_statement_rec te ge le None s1 in
        eval_statement_rec te ge le1 ty s2
    | StReturn a =>
        match ty with
        | Some ty =>
            let* ta := typof_atom te a in
            ecast_typ tabs (eval_atom te ge le ta a) ty
        | None => fail
        end
    | StAttr _ s1 => eval_statement_rec te ge le ty s1
    end.

  Definition eval_statement (te: tenv) (ge: genv) (le: lenv) (tr: typ) (body: statement) : res (eval_typ tr) :=
    ignore_err (eval_statement_rec te ge le (Some tr) body).

  Definition eval_prog (impl: genv) (prog: program) : res (tenv * genv) :=
    eval_prog tabs statement eval_statement impl prog.

End DENOT.

Module Typing.

  Import ListNotations.

  Section ARCHI.

  Variable arch : Target.archi.

  Fixpoint typecheck_atom (be: benv) (gx: gcontext) (lx: lcontext) (a: atom) : res atom :=
    match a with
    | Syntax.ATrue => ret ATrue
    | Syntax.AFalse => ret AFalse
    | Syntax.AInt32 i s => ret (AInt32 i s)
    | Syntax.AInt64 i s => ret (AInt64 i s)
    | Syntax.AConstr x i1 ty =>
        let* t := typof_constr be x in
        let* z := zval_of_constr be t x in
        ret (AConstr x (Int.repr z) t)
    | Syntax.AVar x _ =>
        let* t := typof_var gx lx x in
        ret (AVar x t)
    | Syntax.ACast a1 ty =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* t := typecheck_cast (Syntax.typof_atom a1') ty in
        ret (ACast a1' t)
    | Syntax.AUnaryOp op a1 _ =>
        let* a1' := typecheck_atom be gx lx a1 in
        let ty1 := Syntax.typof_atom a1' in
        let* t := typecheck_unary_op op ty1 in
        ret (AUnaryOp op a1' t)
    | Syntax.ABinaryOp op a1 a2 _ =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let ty1 := Syntax.typof_atom a1' in
        let ty2 := Syntax.typof_atom a2' in
        let* t := typecheck_binary_op op ty1 ty2 in
        ret (ABinaryOp op a1' a2' t)
    | Syntax.AArrayGet a i _ _ =>
        let* a' := typecheck_atom be gx lx a in
        let* i' := typecheck_atom be gx lx i in
        let ta := Syntax.typof_atom a' in
        let ti := Syntax.typof_atom i' in
        let* (ty, ly) := typecheck_array_get2 arch ta ti in
        ret (AArrayGet a' i' ly ty)
    | Syntax.ARecordProj a f _ _ =>
        let* a' := typecheck_atom be gx lx a in
        let ta := Syntax.typof_atom a' in
        let* (ty, ly) := typecheck_record_proj2 be ta f in
        ret (ARecordProj a' f ly ty)
    | Syntax.APureCall f _ args _ =>
        let* tf := typof_var gx lx f in
        let* args' := mmap (typecheck_atom be gx lx) args in
        let targs := map Syntax.typof_atom args' in
        let* ty := typecheck_call tf targs in
        ret (APureCall f tf args' ty)
    end.

  Definition typecheck_comp (be: benv) (gx: gcontext) (lx: lcontext) (c: comp) : res comp :=
    match c with
    | Syntax.CpAtom a =>
        let* a' := typecheck_atom be gx lx a in
        ret (CpAtom a')
    | Syntax.CpArraySet a1 a2 a3 _ =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let* a3' := typecheck_atom be gx lx a3 in
        let ty1 := Syntax.typof_atom a1' in
        let ty2 := Syntax.typof_atom a2' in
        let ty3 := Syntax.typof_atom a3' in
        let* ty := typecheck_array_set arch ty1 ty2 ty3 in
        ret (CpArraySet a1' a2' a3' ty)
    | Syntax.CpRecordUpdate a1 x a2 _ =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let ty1 := Syntax.typof_atom a1' in
        let ty2 := Syntax.typof_atom a2' in
        let* ty := typecheck_record_update be ty1 ty2 x in
        ret (CpRecordUpdate a1' x a2' ty)
    | Syntax.CpCall f _ args _ =>
        let* tf := typof_var gx lx f in
        let* args' := mmap (typecheck_atom be gx lx) args in
        let targs := map Syntax.typof_atom args' in
        let* ty := typecheck_call tf targs in
        ret (CpCall f tf args' ty)
    end.

  (* Should be checked if the contexts contains the same set of set variables. ? *)
  Definition merge_contexts (lx1 lx2: lcontext) : res lcontext :=
    STree.fold
      (fun acc k v =>
        let* acc := acc in
        lcontext_update acc k v)
      lx2
      (ret lx1).

  Fixpoint typecheck_statement (be: benv) (gx: gcontext) (lx: lcontext) (tret: btyp) (s: statement) : res (statement * lcontext) :=
    let fix typecheck_match_rec (be: benv) (gx: gcontext) (lx: lcontext) (te: btyp) (tret: btyp) (elems: list ident) (unmatched: list ident)
      (cases: list (Benum.pattern * statement)) : res (list (pattern * statement) * lcontext) :=
      match cases with
      | nil => fail
      | (x, sx) :: nil =>
          let* unmatched' := typecheck_pattern be te elems x unmatched in
          if list_is_empty unmatched' then
            let* (sx', lx') := typecheck_statement be gx lx tret sx in
            ret (((x, sx') :: nil), lx')
          else
            failwith "Imp1.Typing.typecheck_match_rec: non-exhaustive pattern-matching"
      | (x, sx) :: ((_ :: _) as cases') =>
          let* unmatched' := typecheck_pattern be te elems x unmatched in
          let* (sx', lx') := typecheck_statement be gx lx tret sx in
          let* (cases_typed, lxr) := typecheck_match_rec be gx lx te tret elems unmatched' cases' in
          let* lxm := merge_contexts lx' lxr in
          ret (((x, sx') :: cases_typed), lxm)
      end
    in
    let typecheck_match (be: benv) (gx: gcontext) (lx: lcontext) (tret: btyp) (ty: btyp)
      (cases: list (Benum.pattern * statement)) : res (list (pattern * statement) * lcontext) :=
      match ty with
      | BEnum te =>
          let* elems := TEnv.get_edef be te in
          typecheck_match_rec be gx lx ty tret elems elems cases
      | _ => failwith "Imp1.Typing.typecheck_match: enum type expected"
      end
    in
    match s with
    | Imp1.StSet x c =>
        let* c' := typecheck_comp be gx lx c in
        let* lx' := lcontext_update lx x (typof_comp c') in
        ret (StSet x c', lx')
    | Imp1.StIfThenElse a s1 s2 =>
        let* (s1', lx1) := typecheck_statement be gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement be gx lx tret s2 in
        let* a' := typecheck_atom be gx lx a in
        match Syntax.typof_atom a' with
        | BBool =>
            let* lx' := merge_contexts lx1 lx2 in
            ret (StIfThenElse a' s1' s2', lx')
        | _ => failwith "Imp1.Typing.typecheck_statement: atom of type bool expected"
        end
    | Imp1.StSwitch a cases =>
        let* a' := typecheck_atom be gx lx a in
        let* (cases_typed, lx') := typecheck_match be gx lx tret (Syntax.typof_atom a') cases in
        ret (StSwitch a' cases_typed, lx')
    | Imp1.StSequence s1 s2 =>
        let* (s1', lx1) := typecheck_statement be gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement be gx lx1 tret s2 in
        ret (StSequence s1' s2', lx2)
    | Imp1.StReturn a =>
        let* a' := typecheck_atom be gx lx a in
        let ty := Syntax.typof_atom a' in
        if btyp_eq_dec ty tret then
          ret (StReturn a', lx)
        else
          failwith "Imp1.Typing.typecheck_statement: return type mismatch"
    | Imp1.StAttr a s =>
        let* (s',lx') := typecheck_statement be gx lx tret s in
        ret (StAttr a s',lx')
    end.

  Definition typecheck_function (be: benv) (gx: gcontext) (f: function) : res function :=
    let* lx :=
      list_fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        (fn_params f)
        (ret STree.empty)
    in
    let* (body, _) := typecheck_statement be gx lx (fn_return f) (fn_body f) in
    ret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}.
  
  Fixpoint typecheck_globdefs_rec (be: benv) (gx: gcontext) (defs: list globdef) : res (list globdef) :=
    match defs with
    | nil => ret nil
    | d :: defs' =>
        match d with
        | DefConst x l ty =>
            let* l' := typecheck_literal be l in
            if btyp_eq_dec ty (typof_literal l') then
              let* gx := gcontext_update gx x ty in
              let* rd := typecheck_globdefs_rec be gx defs' in
              ret (DefConst x l' ty :: rd)
            else
              failwith "Imp1.Typing.typecheck_globdefs: type mismatch in constant definition"
        | DefFun x f =>
            let* f' := typecheck_function be gx f in
            let* gx := gcontext_update gx x (mk_fun_btyp (fn_params f') (fn_return f')) in
            let* rd := typecheck_globdefs_rec be gx defs' in
            ret (DefFun x f' :: rd)
        | DeclConst x ty =>
            let* gx := gcontext_update gx x ty in
            let* rd := typecheck_globdefs_rec be gx defs' in
            ret (DeclConst x ty :: rd)
        | DeclFun x tparams tret =>
            let* gx := gcontext_update gx x (mk_fun_btyp tparams tret) in
            let* rd := typecheck_globdefs_rec be gx defs' in
            ret (DeclFun x tparams tret :: rd)
        end
    end.

  Definition typecheck_globdefs (be: benv) (defs: list globdef) : res (list globdef) :=
    typecheck_globdefs_rec be STree.empty defs.

  Definition typecheck_program (prog: program) : res program :=
    let* be := TEnv.build (prog_types prog) in
    let* defs := typecheck_globdefs be (prog_defs prog) in
    ret {|
      prog_defs := defs;
      prog_types := prog_types prog;
      prog_tabs := prog_tabs prog;
    |}.

  End ARCHI.

End Typing.

Module Imp1Typing := Imp1.Typing.
