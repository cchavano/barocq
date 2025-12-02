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
  | BEnum eid => TEnum eid
  | BArray ta ly => TArray (transl_btyp ta) ly
  | BRecord rid _ => TRecord rid
  | BFun tparams tret => TFun (List.map transl_btyp tparams) (transl_btyp tret)
  | BAbs t => TAbs t
  end.

Fixpoint transl_atom (a: Imp1.Typed.atom) : atom :=
  match a with
  | Syntax.Typed.ATrue => ATrue
  | Syntax.Typed.AFalse => AFalse
  | Syntax.Typed.AInt32 i s => AInt32 i s
  | Syntax.Typed.AInt64 i s => AInt64 i s
  | Syntax.Typed.AConstr cid i ty => AConstr cid i (transl_btyp ty)
  | Syntax.Typed.AVar x ty => AVar x (transl_btyp ty)
  | Syntax.Typed.ACast a ty => ACast (transl_atom a) (transl_btyp ty)
  | Syntax.Typed.AUnaryOp op a ty =>
      AUnaryOp op (transl_atom a) (transl_btyp ty)
  | Syntax.Typed.ABinaryOp op a1 a2 ty =>
      ABinaryOp op (transl_atom a1) (transl_atom a2) (transl_btyp ty)
  | Syntax.Typed.AArrayGet a i ly ty =>
      AArrayGet (transl_atom a) (transl_atom i) ly (transl_btyp ty)
  | Syntax.Typed.ARecordProj a f ly ty =>
      ARecordProj (transl_atom a) f ly (transl_btyp ty)
  | Syntax.Typed.APureCall f tf args tr =>
      APureCall f (transl_btyp tf) (List.map transl_atom args) (transl_btyp tr)
  end.

(* Definition transl_access (ac: Syntax.Typed.access) : Imp2.access :=
  match ac with
  | Syntax.Typed.AcRecordField f ty ly =>
      AcRecordField f (transl_btyp ty) ly
  | Syntax.Typed.AcArrayIndex i ty ly =>
      AcArrayIndex (transl_atom i) (transl_btyp ty) ly
  end. *)

Definition set_or_skip (x: ident) (a: atom) : Imp2.statement :=
  match a with
  | AVar y ty =>
      if Ident.eq_dec x y then StSkip
      else StSet x a
  | _ => StSet x a
  end.

Fixpoint transl_statement (s: Imp1Typed.statement) : Imp2.statement :=
  match s with
  | Imp1Typed.StSet x (CpAtom a ty) =>
      set_or_skip x (transl_atom a)
  (* | Imp1Typed.StSet x (CpArrayGet a1 a2 ty ly) =>
      let a1' := transl_atom a1 in
      let a2' := transl_atom a2 in
      StSetExpr x (EArrayGet a1' a2' (transl_btyp ty) ly) *)
  (* | Imp1Typed.StSet x (CpRecordProj a1 f ty ly) =>
      StSetExpr x (ERecordProj (transl_atom a1) f (transl_btyp ty) ly)
  | Imp1Typed.StSet x (CpDeepAccess a acs ty) =>
      let a' := transl_atom a in
      let acs' := List.map transl_access acs in
      StSetExpr x (EDeepAccess a' acs' (transl_btyp ty)) *)
  | Imp1Typed.StSet x (CpArraySet a1 a2 a3 _) =>
      let a1' := transl_atom a1 in
      let a2' := transl_atom a2 in
      let a3' := transl_atom a3 in
      StSequence (StEcomp (EcArraySet a1' a2' a3')) (set_or_skip x a1')
  | Imp1Typed.StSet x (CpRecordUpdate a1 f a2 _) =>
      let a1' := transl_atom a1 in
      let a2' := transl_atom a2 in
      StSequence (StEcomp (EcRecordUpdate a1' f a2')) (set_or_skip x a1')
  | Imp1Typed.StSet x (CpCall f tf args ty) =>
      let args' := List.map transl_atom args in
      StCall (Some x) f (transl_btyp tf) args' (transl_btyp ty)
  | Imp1Typed.StIfThenElse a s1 s2 =>
      StIfThenElse (transl_atom a) (transl_statement s1) (transl_statement s2)
  | Imp1Typed.StSwitch a cases =>
      let cases' := MapList.map transl_statement cases in
      StSwitch (transl_atom a) cases'
  | Imp1Typed.StSequence s1 s2 =>
      StSequence (transl_statement s1) (transl_statement s2)
  | Imp1Typed.StReturn a => StReturn (Some (transl_atom a))
  | Imp1Typed.StAttr a s => transl_statement s
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
  | Imp1Typed.StAttr _ s => all_vars s
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

  Variable transl_literal : bool -> Imp1Typed.literal -> smaplist Imp2.literal -> cmon (Imp2.literal * (smaplist Imp2.literal)).

  Fixpoint transl_array_lit (ly: bool) (a: array Imp1Typed.literal) (defs: smaplist Imp2.literal) : cmon (array Imp2.literal * smaplist Imp2.literal) :=
    match a with
    | nil => ret (nil, defs)
    | lx :: a' =>
        let* (lx', defs1) := transl_literal ly lx defs in
        let* (r, defs2) := transl_array_lit ly a' defs1 in
        ret (lx' :: r, defs2)
    end.

  Fixpoint transl_record_lit (rc: smaplist Imp1Typed.literal) (ub: list ident) (defs: smaplist Imp2.literal) : cmon ((smaplist Imp2.literal) * smaplist Imp2.literal) :=
    match rc with
    | nil => ret (nil, defs)
    | (i, lx) :: rc' =>
        let ly := negb (list_mem Ident.eq_dec i ub) in
        let* (lx', defs1) := transl_literal ly lx defs in
        let* (r, defs2) := transl_record_lit rc' ub defs1 in
        ret ((i, lx') :: r, defs2)
    end.

End LITTRANSL.

Definition fresh_var : cmon ident := Utils.fresh_var "g".

Fixpoint transl_literal_rec (ly: bool) (l: Imp1Typed.literal) (defs: smaplist Imp2.literal) : cmon (Imp2.literal * smaplist Imp2.literal) :=
  match l with
  | Syntax.LTrue => ret (LTrue, defs)
  | Syntax.LFalse => ret (LFalse, defs)
  | Syntax.LInt32 i s => ret (LInt32 i s, defs)
  | Syntax.LInt64 i s => ret (LInt64 i s, defs)
  | Syntax.LArray a ta ba =>
      let bba := if layout_eq_dec ba LyBoxed then true else false in
      let* (a', defs) := transl_array_lit transl_literal_rec bba a defs in
      let ta' := transl_btyp ta in
      if ly then
        let* x := fresh_var in
        ret (LVar x (TArray ta' ba), (x, LArray a' ta' ba) :: defs)
      else
        ret (LArray a' ta' ba, defs)
  | Syntax.LRecord rc ub rid =>
      let* (rc', defs) := transl_record_lit transl_literal_rec rc ub defs in
      if ly then
        let* x := fresh_var in
        ret (LVar x (TRecord rid), (x, LRecord rc' ub rid) :: defs)
      else
        ret (LRecord rc' ub rid, defs)
  end.

Definition transl_literal (l: Imp1Typed.literal) : cmon (Imp2.literal * smaplist Imp2.literal) :=
  let* (l', defs) :=
    match l with
    | Syntax.LArray _ _ _ => transl_literal_rec false l nil
    | _ => transl_literal_rec true l nil
    end
  in ret (l', rev' defs).

Definition typof_literal (l: literal) : typ2 :=
  match l with
  | LTrue
  | LFalse => TBool
  | LInt32 _ s => TInt32 s
  | LInt64 _ s => TInt64 s
  | LVar _ ty => ty
  | LArray _ ta ly => TArray ta ly
  | LRecord _ _ rid => TRecord rid
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

Definition transl_type_def (td: type_def field_descr) : type_def (typ2 * layout) :=
  match td with
  | TdEnum elems => TdEnum elems
  | TdRecord fields =>
    let fields' := MapList.map (fun '(ty, ly) => (transl_btyp ty, ly)) fields in
    TdRecord fields'
  end.

Definition transl_program (prog: Imp1Typed.program) : Imp2.program :=
  {|
    prog_defs := transl_globdefs (prog_defs prog);
    prog_types := MapList.map transl_type_def (prog_types prog);
    prog_tabs := prog_tabs prog;
  |}.
