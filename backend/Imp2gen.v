From Coq Require Import List String.
From compcert Require Import Maps.
From BarocqComp Require Import Monads Maps2 Utils Barray Syntax Types Typing Imp1.
Import ListNotations.
Import Syntax.Typed.
Import Imp1Typed.
Import Imp1Typing.
From BarocqComp Require Import Imp2.
Import MonCounter.

Fixpoint transl_btyp (ty: btyp) : typ2 :=
  match ty with
  | BBool => TBool
  | BInt32 s => TInt32 s
  | BInt64 s => TInt64 s
  | BArray ta => TArray (transl_btyp ta)
  | BEnum eid => TEnum eid
  | BRecord rid => TRecord rid 
  | BFun tparams tret => TFun (List.map transl_btyp tparams) (transl_btyp tret)
  | BAbs t => TAbs t
  end.

Fixpoint transl_atom (a: Imp1.Typed.atom) : atom :=
  match a with
  | Syntax.Typed.ATrue _ => ATrue
  | Syntax.Typed.AFalse _ => AFalse
  | Syntax.Typed.AInt32 i ty => AInt32 i (transl_btyp ty)
  | Syntax.Typed.AInt64 i ty => AInt64 i (transl_btyp ty)
  | Syntax.Typed.AConstr cid ty => AConstr cid (transl_btyp ty)
  | Syntax.Typed.AVar x ty => AVar x (transl_btyp ty)
  | Syntax.Typed.ACast a ty => ACast (transl_atom a) (transl_btyp ty)
  | Syntax.Typed.AUnaryOp op a ty =>
      AUnaryOp op (transl_atom a) (transl_btyp ty)
  | Syntax.Typed.ABinaryOp op a1 a2 ty =>
      ABinaryOp op (transl_atom a1) (transl_atom a2) (transl_btyp ty)
  end.

Definition transl_access (ac: Syntax.Typed.access) : Imp2.access :=
  match ac with
  | Syntax.Typed.AcRecordField f ty =>
      AcRecordField f (transl_btyp ty)
  | Syntax.Typed.AcArrayIndex a ty =>
      AcArrayIndex (transl_atom a) (transl_btyp ty)
  end.

Definition typof_atom (a: atom) : typ2 :=
  match a with
  | ATrue
  | AFalse => TBool
  | AInt32 _ ty
  | AInt64 _ ty
  | AConstr _ ty
  | AVar _ ty
  | ACast _ ty
  | AUnaryOp _ _ ty
  | ABinaryOp _ _ _ ty => ty
  end.

Fixpoint transl_statement (s: Imp1Typed.statement) : Imp2.statement :=
  match s with
  | Imp1Typed.StSet x (CpAtom a ty) =>
      StSetExpr x (EAtom (transl_atom a) (transl_btyp ty))
  | Imp1Typed.StSet x (CpArrayGet a1 a2 ty) =>
      let a1' := transl_atom a1 in
      let a2' := transl_atom a2 in
      StSetExpr x (EArrayGet a1' a2' (transl_btyp ty))
  | Imp1Typed.StSet x (CpRecordProj a1 f ty) =>
      StSetExpr x (ERecordProj (transl_atom a1) f (transl_btyp ty))
  | Imp1Typed.StSet x (CpDeepAccess a acs ty) =>
      let a' := transl_atom a in
      let acs' := List.map transl_access acs in
      StSetExpr x (EDeepAccess a' acs' (transl_btyp ty))
  | Imp1Typed.StSet x (CpArraySet a1 a2 a3 _) =>
      let a1' := transl_atom a1 in
      let a2' := transl_atom a2 in
      let a3' := transl_atom a3 in
      StSequence (StEcomp (EcArraySet a1' a2' a3')) (StSetExpr x (EAtom a1' (typof_atom a1')))
  | Imp1Typed.StSet x (CpRecordUpdate a1 f a2 _) =>
      let a1' := transl_atom a1 in
      let a2' := transl_atom a2 in
      StSequence (StEcomp (EcRecordUpdate a1' f a2')) (StSetExpr x (EAtom a1' (typof_atom a1')))
  | Imp1Typed.StSet x (CpCall a args ty) =>
      let a' := transl_atom a in
      let args' := List.map transl_atom args in
      StCall (Some x) a' args' (transl_btyp ty)
  | Imp1Typed.StIfThenElse a s1 s2 =>
      StIfThenElse (transl_atom a) (transl_statement s1) (transl_statement s2)
  | Imp1Typed.StSwitch a cases =>
      let cases' := MapList.map transl_statement cases in
      StSwitch (transl_atom a) cases'
  | Imp1Typed.StSequence s1 s2 =>
      StSequence (transl_statement s1) (transl_statement s2)
  | Imp1Typed.StReturn a => StReturn (Some (transl_atom a))
  end.

Fixpoint all_vars (s: Imp1Typed.statement) : smaplist btyp :=
  match s with
  | Imp1Typed.StReturn _ => MapList.empty
  | Imp1Typed.StSet x c => MapList.add Ident.eq_dec x (typof_comp c) MapList.empty
  | Imp1Typed.StIfThenElse _ s1 s2
  | Imp1Typed.StSequence s1 s2 => MapList.merge Ident.eq_dec (all_vars s1) (all_vars s2)
  | Imp1Typed.StSwitch _ cases =>
      MapList.fold_left
        (fun acc _ si => MapList.merge Ident.eq_dec (all_vars si) acc)
        cases
        MapList.empty
  end.

Definition transl_function (f: Imp1Typed.function) : Imp2.function :=
  {|
    fn_return := transl_btyp (Syntax.fn_return f);
    fn_params := MapList.map transl_btyp (Syntax.fn_params f);
    fn_vars := MapList.map transl_btyp (all_vars (Syntax.fn_body f));
    fn_body := transl_statement (Syntax.fn_body f)
  |}.

Local Open Scope state_monad_scope.

Section LITTRANSL.

  Variable transl_literal : Imp1Typed.literal -> smaplist Imp2.literal -> cmon (Imp2.literal_base * (smaplist Imp2.literal)).

  Fixpoint transl_array_lit (a: array Imp1Typed.literal) (defs: smaplist Imp2.literal) : cmon (array Imp2.literal_base * smaplist Imp2.literal) :=
    match a with
    | nil => ret (nil, defs)
    | lx :: a' =>
        let* (lx', defs1) := transl_literal lx defs in
        let* (r, defs2) := transl_array_lit a' defs1 in
        ret (lx' :: r, defs2)
    end.

  Fixpoint transl_record_lit (rc: smaplist Imp1Typed.literal) (defs: smaplist Imp2.literal) : cmon ((smaplist Imp2.literal_base) * smaplist Imp2.literal) :=
    match rc with
    | nil => ret (nil, defs)
    | (i, lx) :: rc' =>
        let* (lx', defs1) := transl_literal lx defs in
        let* (r, defs2) := transl_record_lit rc' defs1 in
        ret ((i, lx') :: r, defs2)
    end.

End LITTRANSL.

Definition fresh_var : cmon ident := Utils.fresh_var "g".

Fixpoint transl_literal_rec (l: Imp1Typed.literal) (defs: smaplist Imp2.literal) : cmon (Imp2.literal_base * smaplist Imp2.literal) :=
  match l with
  | Syntax.Typed.LTrue ty => ret (LbTrue, defs)
  | Syntax.Typed.LFalse ty => ret (LbFalse, defs)
  | Syntax.Typed.LInt32 i ty => ret (LbInt32 i, defs)
  | Syntax.Typed.LInt64 i ty => ret (LbInt64 i, defs)
  | Syntax.Typed.LArray a ty =>
      let* (a', defs) := transl_array_lit transl_literal_rec a defs in
      let* x := fresh_var in
      ret (LbVar x, (x, LArray a' (transl_btyp ty)) :: defs)
  | Syntax.Typed.LRecord rc ty =>
      let* (rc', defs) := transl_record_lit transl_literal_rec rc defs in
      let* x := fresh_var in
      ret (LbVar x, (x, LRecord rc' (transl_btyp ty)) :: defs)
  end.

Definition transl_literal (l: Imp1Typed.literal) : cmon (Imp2.literal * smaplist Imp2.literal) :=
  let* (l', defs) :=
    match l with
    | Syntax.Typed.LArray a ty =>
        let* (a', defs) := transl_array_lit transl_literal_rec a nil in
        ret (LArray a' (transl_btyp ty), defs)
    | _ =>
        let* (stb, defs) := transl_literal_rec l nil in
        ret (LBase stb (transl_btyp (typof_literal l)), defs)
    end
  in ret (l', rev' defs).

Definition typof_literal (l: Imp2.literal) : typ2 :=
  match l with
  | LBase _ ty => ty
  | LRecord _ ty => ty
  | LArray _ ty => ty
  end.

Fixpoint transl_globdefs_rec (defs: list Imp1Typed.globdef) : cmon (list Imp2.globdef) :=
  match defs with
  | nil => ret nil
  | d :: defs' =>
      match d with
      | DefFun x f =>
          let* dr := transl_globdefs_rec defs' in
          ret (DefFun x (transl_function f) :: dr)
      | DefConst x l ty =>
          let* (l', d1) := transl_literal l in
          let defs1 := List.map (fun '(x, lx) => DefConst x lx (typof_literal lx)) d1 in
          let* dr := transl_globdefs_rec defs' in
          ret (defs1 ++ ((DefConst x l' (transl_btyp ty)) :: dr))
      | DeclConst x ty =>
          let* dr := transl_globdefs_rec defs' in
          ret (DeclConst x (transl_btyp ty) :: dr)
      | DeclFun f tparams tret =>
          let* dr := transl_globdefs_rec defs' in
          ret (DeclFun f (MapList.map transl_btyp tparams) (transl_btyp tret) :: dr)
      end
  end.

Definition transl_globdefs (defs: list Imp1Typed.globdef) : list Imp2.globdef :=
  fst (transl_globdefs_rec defs 0).

Definition transl_type_def (td: type_def btyp) : type_def typ2 :=
  match td with
  | TdEnum ed => TdEnum ed
  | TdRecord rd =>
     TdRecord {| rd_name := rd_name rd; rd_fields := MapList.map transl_btyp (rd_fields rd) |}
  | TdAbstract tid su => TdAbstract tid su
  end.

Definition transl_program (prog: Imp1Typed.program) : Imp2.program :=
  {|
    prog_defs := transl_globdefs (prog_defs prog);
    prog_types := List.map transl_type_def (prog_types prog);
  |}.