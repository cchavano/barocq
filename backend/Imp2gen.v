From Coq Require Import List String.
From compcert Require Import Maps.
From BarocqComp Require Import Monads MapList Utils Array Syntax Types Typing Imp1.
Import ListNotations.
Import Syntax.Typed.
Import Imp1Typed.
Import Imp1Typing.
From BarocqComp Require Import Imp2.
Import MonCounter.

Fixpoint transl_statement (s: Imp1Typed.statement) : Imp2.statement :=
  match s with
  | Imp1Typed.StSet x (CpAtom a ty) =>
      StSetExpr x (EAtom a ty)
  | Imp1Typed.StSet x (CpArrayGet a1 a2 ty) =>
      StSetExpr x (EArrayGet a1 a2 ty)
  | Imp1Typed.StSet x (CpStructProj a1 f ty) =>
      StSetExpr x (EStructProj a1 f ty)
  | Imp1Typed.StSet x (CpDeepAccess a acs ty) =>
      StSetExpr x (EDeepAccess a acs ty)
  | Imp1Typed.StSet x (CpArraySet a1 a2 a3 _) =>
      StSetEcomp x (EcArraySet a1 a2 a3)
  | Imp1Typed.StSet x (CpStructUpdate a1 f a2 _) =>
      StSetEcomp x (EcStructUpdate a1 f a2)
  | Imp1Typed.StSet x (CpCall a args _) => StCall x a args
  | Imp1Typed.StIfThenElse a s1 s2 =>
      StIfThenElse a (transl_statement s1) (transl_statement s2)
  | Imp1Typed.StSequence s1 s2 =>
      StSequence (transl_statement s1) (transl_statement s2)
  | Imp1Typed.StReturn a => StReturn a
  end.

Fixpoint all_vars (s: Imp1Typed.statement) : list (ident * ctyp) :=
  match s with
  | Imp1Typed.StReturn _ => nil
  | Imp1Typed.StSet x c => (x, typof_comp c) :: nil
  | Imp1Typed.StIfThenElse _ s1 s2
  | Imp1Typed.StSequence s1 s2 => merge_k Ident.eq_dec (all_vars s1) (all_vars s2)
  end.

Definition transl_function (f: Imp1Typed.function) : Imp2.function :=
  {|
    fn_return := Syntax.fn_return f;
    fn_params := Syntax.fn_params f;
    fn_vars := all_vars (Syntax.fn_body f);
    fn_body := transl_statement (Syntax.fn_body f)
  |}.

Local Open Scope state_monad_scope.

Section LITTRANSL.

  Variable transl_literal : Imp1Typed.literal -> list (ident * Imp2.literal) -> cmon (Imp2.literal_base * list (ident * Imp2.literal)).

  Fixpoint transl_array_lit (a: array Imp1Typed.literal) (defs: list (ident * Imp2.literal)) : cmon (array Imp2.literal_base * list (ident * Imp2.literal)) :=
    match a with
    | nil => ret (nil, defs)
    | lx :: a' =>
        let* (lx', defs1) := transl_literal lx defs in
        let* (r, defs2) := transl_array_lit a' defs1 in
        ret (lx' :: r, defs2)
    end.

  Fixpoint transl_struct_lit (st: list (ident * Imp1Typed.literal)) (defs: list (ident * Imp2.literal)) : cmon (list (ident * Imp2.literal_base) * list (ident * Imp2.literal)) :=
    match st with
    | nil => ret (nil, defs)
    | (i, lx) :: st' =>
        let* (lx', defs1) := transl_literal lx defs in
        let* (r, defs2) := transl_struct_lit st' defs1 in
        ret ((i, lx') :: r, defs2)
    end.

End LITTRANSL.

Definition fresh_var : cmon ident := Utils.fresh_var "g".

Fixpoint transl_literal_rec (l: Imp1Typed.literal) (defs: list (ident * Imp2.literal)) : cmon (Imp2.literal_base * list (ident * Imp2.literal)) :=
  match l with
  | Syntax.Typed.LTrue ty => ret (LbTrue, defs)
  | Syntax.Typed.LFalse ty => ret (LbFalse, defs)
  | Syntax.Typed.LInt32 i ty => ret (LbInt32 i, defs)
  | Syntax.Typed.LInt64 i ty => ret (LbInt64 i, defs)
  | Syntax.Typed.LArray a ty =>
      let* (a', defs) := transl_array_lit transl_literal_rec a defs in
      let* x := fresh_var in
      ret (LbVar x, (x, LArray a' ty) :: defs)
  | Syntax.Typed.LStruct st ty =>
      let* (st', defs) := transl_struct_lit transl_literal_rec st defs in
      let* x := fresh_var in
      ret (LbVar x, (x, LStruct st' ty) :: defs)
  end.

Definition transl_literal (l: Imp1Typed.literal) : cmon (Imp2.literal * list (ident * Imp2.literal)) :=
  let* (l', defs) :=
    match l with
    | Syntax.Typed.LArray a ty =>
        let* (a', defs) := transl_array_lit transl_literal_rec a nil in
        ret (LArray a' ty, defs)
    | _ =>
        let* (stb, defs) := transl_literal_rec l nil in
        ret (LBase stb (typof_literal l), defs)
    end
  in ret (l', rev' defs).

Definition typof_literal (l: Imp2.literal) : ctyp :=
  match l with
  | LBase _ ty => ty
  | LStruct _ ty => ty
  | LArray _ ty => ty
  end.

Fixpoint transl_globdefs_rec (defs: list Imp1Typed.globdef) : cmon (list Imp2.globdef) :=
  match defs with
  | nil => ret nil
  | DefFun x f :: defs' =>
      let* dr := transl_globdefs_rec defs' in
      ret (DefFun x (transl_function f) :: dr)
  | DefConst x l ty :: defs' =>
      let* (l', d1) := transl_literal l in
      let defs1 := map (fun '(x, lx) => DefConst x lx (typof_literal lx)) d1 in
      let* dr := transl_globdefs_rec defs' in
      ret (defs1 ++ ((DefConst x l' ty) :: dr))
  end.

Definition transl_globdefs (defs: list Imp1Typed.globdef) : list Imp2.globdef :=
  fst (transl_globdefs_rec defs 0).

Definition transl_program (prog: Imp1Typed.program) : Imp2.program :=
  {|
    prog_defs := transl_globdefs (prog_defs prog);
    prog_types := prog_types prog;
  |}.