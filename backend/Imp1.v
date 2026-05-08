From Stdlib Require Import Bool List String PArith Lia.
From compcert Require Import Integers Maps.
From BarocqComp Require Import  Barocq Benum Barray Brecord Option Res Maps2 Utils Syntax Types Typing Pp Denot.
From BarocqComp Require Printer.

Local Open Scope error_monad_scope.

(** * Abstract syntax *)

(** ** Statements *)
 
Inductive statement : Type :=
| StSkip
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
  Import Printer.

  Fixpoint pp_statement (s:statement) :=
    match s with
    | StSkip    => Bstr "skip"
    | StSet i c => Bcat (Bstr i) (Bcat (Bstr " := ") (Printer.pp_comp c))
    | StIfThenElse a s1 s2 =>
        let s1 := Bcat (Bstr "then ") (pp_statement s1) in
        let s2 := Bcat (Bstr "else ") (pp_statement s2) in
        let c  := Printer.pp_atom a in
        let cd := Bcat (Bstr "if ") c in
        Bstack cd (Bstack s1 s2 Left) Left
    | StSwitch a l => pp_match pp_atom pp_statement  "match " a l
    | StSequence s1 s2 =>
        let s1 := pp_statement s1 in
        let s2 := pp_statement s2 in
        Bstack (suffix_nocat s1 ";") s2 Left
    | StReturn a => Bcat (Bstr "return ") (Printer.pp_atom a)
    | StAttr a s => Bcat (Bstr "[#") (Bcat (Bstr a) (Bcat (Bstr "]") (pp_statement s)))
    end.

  Definition pp_program (p:program) := Printer.pp_program  Printer.pp_btyp Printer.pp_literal pp_statement p.

End Pp.

Section TRANSF.

  Variable trans_statement : statement -> res statement.

  Definition trans_function (f:function) :=
    do b <- trans_statement (fn_body f);
    OK {| fn_return := fn_return f;
          fn_params := fn_params f;
          fn_body   := b
      |}.

  Definition trans_globdef (gd : globdef) : res globdef :=
    match gd with
    | DefFun id f    => do f' <- trans_function f;
                        OK (DefFun id f')
    | _ => OK gd
    end.

  Definition trans_program (p:program) : res program :=
    do gd' <-  mmap trans_globdef (prog_defs p);
    OK {|
      prog_defs := gd';
      prog_types := prog_types p;
      prog_tabs := prog_tabs p;
    |}.

End TRANSF.


Module Typing.
  Import Res.

  Import ListNotations.

  Fixpoint typecheck_atom (be: benv) (gx: gcontext) (lx: lcontext) (a: atom) : res atom :=
    match a with
    | Syntax.ATrue => eret ATrue
    | Syntax.AFalse => eret AFalse
    | Syntax.AInt32 i s => eret (AInt32 i s)
    | Syntax.AInt64 i s => eret (AInt64 i s)
    | Syntax.AConstr x i1 ty =>
        do t <- typof_constr be x;
        do z <- zval_of_constr be t x;
        eret (AConstr x (Int.repr z) t)
    | Syntax.AVar x _ =>
        do t <- typof_var gx lx x;
        eret (AVar x t)
    | Syntax.ACast a1 ty =>
        do a1' <- typecheck_atom be gx lx a1;
        do t <- Res.of_opt (typecheck_cast (btypof_atom a1') ty);
        eret (ACast a1' t)
    | Syntax.AUnaryOp op a1 _ =>
        do a1' <- typecheck_atom be gx lx a1;
        let ty1 := btypof_atom a1' in
        do t <- typecheck_unary_op op ty1;
        eret (AUnaryOp op a1' t)
    | Syntax.ABinaryOp op a1 a2 _ =>
        do a1' <- typecheck_atom be gx lx a1;
        do a2' <- typecheck_atom be gx lx a2;
        let ty1 := btypof_atom a1' in
        let ty2 := btypof_atom a2' in
        do t <- typecheck_binary_op op ty1 ty2;
        eret (ABinaryOp op a1' a2' t)
    | Syntax.AArrayGet a i _ _ =>
        do a' <- typecheck_atom be gx lx a;
        do i' <- typecheck_atom be gx lx i;
        let ta := btypof_atom a' in
        let ti := btypof_atom i' in
        do (ty, ly) <- typecheck_array_get2 ta ti;
        eret (AArrayGet a' i' ly ty)
    | Syntax.ARecordProj a f _ _ =>
        do a' <- typecheck_atom be gx lx a;
        let ta := btypof_atom a' in
        do (ty, ly) <- typecheck_record_proj2 be ta f;
        eret (ARecordProj a' f ly ty)
    | Syntax.APureCall f _ args _ =>
        do tf <- typof_var gx lx f;
        do args' <- mmap (typecheck_atom be gx lx) args;
        let targs := map btypof_atom args' in
        do ty <- typecheck_call tf targs;
        eret (APureCall f tf args' ty)
    end.

  Definition typecheck_comp (be: benv) (gx: gcontext) (lx: lcontext) (c: comp) : res comp :=
    match c with
    | Syntax.CpAtom a =>
        do a' <- typecheck_atom be gx lx a;
        eret (CpAtom a')
    | Syntax.CpArraySet a1 a2 a3 _ =>
        do a1' <- typecheck_atom be gx lx a1;
        do a2' <- typecheck_atom be gx lx a2;
        do a3' <- typecheck_atom be gx lx a3;
        let ty1 := btypof_atom a1' in
        let ty2 := btypof_atom a2' in
        let ty3 := btypof_atom a3' in
        do ty <- typecheck_array_set ty1 ty2 ty3;
        eret (CpArraySet a1' a2' a3' ty)
    | Syntax.CpRecordUpdate a1 x a2 _ =>
        do a1' <- typecheck_atom be gx lx a1;
        do a2' <- typecheck_atom be gx lx a2;
        let ty1 := btypof_atom a1' in
        let ty2 := btypof_atom a2' in
        do ty <- typecheck_record_update be ty1 ty2 x;
        eret (CpRecordUpdate a1' x a2' ty)
    | Syntax.CpCall f _ args _ =>
        do tf <- typof_var gx lx f;
        do args' <- mmap (typecheck_atom be gx lx) args;
        let targs := map btypof_atom args' in
        do ty <- typecheck_call tf targs;
        eret (CpCall f tf args' ty)
    end.

  (* Should be checked if the contexts contains the same set of set variables. ? *)
  Definition merge_contexts (lx1 lx2: lcontext) : res lcontext :=
    STree.fold
      (fun acc k v =>
        do acc <- acc;
        lcontext_update_imp acc k v)
      lx2
      (eret lx1).

  Fixpoint typecheck_statement (be: benv) (gx: gcontext) (lx: lcontext) (tret: btyp) (s: statement) : res (statement * lcontext) :=
    let fix typecheck_match_rec (be: benv) (gx: gcontext) (lx: lcontext) (te: btyp) (tret: btyp) (elems: list ident) (unmatched: list ident)
      (cases: list (Benum.pattern * statement)) : res (list (pattern * statement) * lcontext) :=
      match cases with
      | nil => efail
      | (x, sx) :: nil =>
          do unmatched' <- typecheck_pattern be te elems x unmatched;
          if list_is_empty unmatched' then
            do (sx', lx') <- typecheck_statement be gx lx tret sx;
            eret (((x, sx') :: nil), lx')
          else
            efailwith "Imp1.Typing.typecheck_match_rec: non-exhaustive pattern-matching"
      | (x, sx) :: ((_ :: _) as cases') =>
          do unmatched' <- typecheck_pattern be te elems x unmatched;
          do (sx', lx') <- typecheck_statement be gx lx tret sx;
          do (cases_typed, lxr) <- typecheck_match_rec be gx lx te tret elems unmatched' cases';
          do lxm <- merge_contexts lx' lxr;
          eret (((x, sx') :: cases_typed), lxm)
      end
    in
    let typecheck_match (be: benv) (gx: gcontext) (lx: lcontext) (tret: btyp) (ty: btyp)
      (cases: list (Benum.pattern * statement)) : res (list (pattern * statement) * lcontext) :=
      match ty with
      | BEnum te =>
          do elems <- Res.of_opt (TEnv.get_edef be te);
          typecheck_match_rec be gx lx ty tret elems elems cases
      | _ => efailwith "Imp1.Typing.typecheck_match: enum type expected"
      end
    in
    match s with
    | Imp1.StSkip    => eret (StSkip,lx)
    | Imp1.StSet x c =>
        do c' <- typecheck_comp be gx lx c;
        do lx' <- lcontext_update_imp lx x (btypof_comp c');
        eret (StSet x c', lx')
    | Imp1.StIfThenElse a s1 s2 =>
        do (s1', lx1) <- typecheck_statement be gx lx tret s1;
        do (s2', lx2) <- typecheck_statement be gx lx tret s2;
        do a' <- typecheck_atom be gx lx a;
        match btypof_atom a' with
        | BBool =>
            do lx' <- merge_contexts lx1 lx2;
            eret (StIfThenElse a' s1' s2', lx')
        | _ => efailwith "Imp1.Typing.typecheck_statement: atom of type bool expected"
        end
    | Imp1.StSwitch a cases =>
        do a' <- typecheck_atom be gx lx a;
        do (cases_typed, lx') <- typecheck_match be gx lx tret (btypof_atom a') cases;
        eret (StSwitch a' cases_typed, lx')
    | Imp1.StSequence s1 s2 =>
        do (s1', lx1) <- typecheck_statement be gx lx tret s1;
        do (s2', lx2) <- typecheck_statement be gx lx1 tret s2;
        eret (StSequence s1' s2', lx2)
    | Imp1.StReturn a =>
        do a' <- typecheck_atom be gx lx a;
        let ty := btypof_atom a' in
        if btyp_eq_dec ty tret then
          eret (StReturn a', lx)
        else
          efailwith "Imp1.Typing.typecheck_statement: return type mismatch"
    | Imp1.StAttr a s =>
        do (s',lx') <- typecheck_statement be gx lx tret s;
        eret (StAttr a s',lx')
    end.

  Definition typecheck_function (be: benv) (gx: gcontext) (f: function) : res function :=
    do lx <-
      list_fold_left_err
        (fun acc '(x, tx) => lcontext_update_imp acc x tx)
        (fn_params f)
        STree.empty;
    do (body, _) <- typecheck_statement be gx lx (fn_return f) (fn_body f);
    eret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}.
  
  Fixpoint typecheck_globdefs_rec (be: benv) (gx: gcontext) (defs: list globdef) : res (list globdef) :=
    match defs with
    | nil => eret nil
    | d :: defs' =>
        match d with
        | DefConst x l ty =>
            do l' <- typecheck_literal be l;
            if btyp_eq_dec ty (btypof_literal l') then
              do gx <- gcontext_update gx x ty;
              do rd <- typecheck_globdefs_rec be gx defs';
              eret (DefConst x l' ty :: rd)
            else
              efailwith "Imp1.Typing.typecheck_globdefs: type mismatch in constant definition"
        | DefFun x f =>
            do f' <- typecheck_function be gx f;
            do gx <- gcontext_update gx x (mk_fun_btyp (fn_params f') (fn_return f'));
            do rd <- typecheck_globdefs_rec be gx defs';
            eret (DefFun x f' :: rd)
        | DeclConst x ty =>
            do gx <- gcontext_update gx x ty;
            do rd <- typecheck_globdefs_rec be gx defs';
            eret (DeclConst x ty :: rd)
        | DeclFun x tparams tret =>
            do gx <- gcontext_update gx x (mk_fun_btyp tparams tret);
            do rd <- typecheck_globdefs_rec be gx defs';
            eret (DeclFun x tparams tret :: rd)
        end
    end.

  Definition typecheck_globdefs (be: benv) (defs: list globdef) : res (list globdef) :=
    typecheck_globdefs_rec be STree.empty defs.

  Definition typecheck_program (prog: program) : res program :=
    do be <- Res.of_opt (TEnv.build (prog_types prog));
    do defs <- typecheck_globdefs be (prog_defs prog);
    eret {|
      prog_defs := defs;
      prog_types := prog_types prog;
      prog_tabs := prog_tabs prog;
    |}.

End Typing.

Module Imp1Typing := Imp1.Typing.
