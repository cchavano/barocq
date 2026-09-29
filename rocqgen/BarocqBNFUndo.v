(** Decompile BarocqBNF into Barocq.
    This is useful to reuse the generation of the shallow embedding. *)

From BarocqComp Require Import Syntax Barocq Maps2.
From BarocqComp Require Import BarocqBNF.
From Stdlib Require Import List.

Fixpoint decompile_atom (e:Syntax.atom) : Barocq.expr:=
  match e with
  | ATrue => Barocq.ETrue
  | AFalse => Barocq.EFalse
  | AInt32 i s => Barocq.EInt32 i s
  | AInt64 i s => Barocq.EInt64 i s
  | AConstr c i b => Barocq.EConstr c
  | AVar v bt => Barocq.EVar v
  | ACast a bt => Barocq.ECast (decompile_atom a) bt
  | AUnaryOp o a bt => Barocq.EUnaryOp o (decompile_atom a)
  | ABinaryOp o a1 a2 bt => Barocq.EBinaryOp o (decompile_atom a1) (decompile_atom a2)
  | AArrayGet a1 a2 ly bt => Barocq.EArrayGet (decompile_atom a1) (decompile_atom a2)
  | ARecordProj a1 fd ly bt => Barocq.ERecordProj (decompile_atom a1) fd
  | APureCall f btf args bt  => Barocq.EApp (EVar f) (List.map decompile_atom args)
  end.

Fixpoint decompile_expr (e:BarocqBNF.expr) : Barocq.expr :=
  match e with
  | EAtom a => decompile_atom a
  | EArraySet a i v bt => Barocq.EArraySet (decompile_atom a) (decompile_atom i) (decompile_atom v)
  | ERecordUpdate r id v bt => Barocq.ERecordUpdate (decompile_atom r) id (decompile_atom v)
  | EApp f args bt => Barocq.EApp (decompile_atom f) (List.map decompile_atom args)
  | EIfThenElse c t e bt => Barocq.EIfThenElse (decompile_atom c) (decompile_expr t) (decompile_expr e)
  | EMatch c m bt => Barocq.EMatch (decompile_atom c) (List.map (fun p => (fst p, decompile_expr (snd p))) m)
  | ELetIn x e1 e2 bt => Barocq.ELetIn x (decompile_expr e1) (decompile_expr e2)
  | EActR ar bt       => Barocq.EActR (MapList.map decompile_atom ar)
  | EAttr s e => Barocq.EAttr s (decompile_expr e)
  | ELetW l cond variant body e _ => Barocq.ELetW (MapList.map decompile_expr l) (decompile_atom cond) (decompile_atom variant)
                                              (decompile_expr body) (decompile_expr e)
  end.

Definition decompile_fun (f:function) : Barocq.function :=
  match f with
  | {| fn_return := fret; fn_params := fparams; fn_body := bdy |} =>
      {| fn_return := fret ; fn_params := fparams ; fn_body := decompile_expr bdy |}
  end.


Definition decompile_gd (gd: globdef) : Barocq.globdef :=
  match gd with
  | Syntax.DefConst id l bt => Barocq.DefConst id l bt
  | Syntax.DefFun f fct => Barocq.DefFun f (decompile_fun fct)
  | Syntax.DeclConst c bt => Barocq.DeclConst c bt
  | Syntax.DeclFun f args bt => Barocq.DeclFun f args bt
  end.

Definition decompile_tabs (l : Maps2.smaplist struct_or_union) : list Barocq.globdef :=
  List.map (fun sd => DeclType (fst sd) (snd sd)) l.

Definition decompile_types (l: Maps2.smaplist (type_def (Types.btyp * Types.layout))) : list Barocq.globdef :=
  List.map (fun sd => DefType (fst sd) (snd sd)) l.

Definition decompile_program  (p:program) : Barocq.program :=
  (decompile_tabs (prog_tabs p)) ++ (decompile_types (prog_types p)) ++ (List.map decompile_gd (prog_defs p)).
