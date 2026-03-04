From Coq Require Import List.
From compcert Require Import Maps.
From BarocqComp Require Import Maps2 Types Syntax Benum OptionMonad Typing Denot.
From BarocqComp Require Pp Printer.
Open Scope option_monad_scope.

  (** * Abstract syntax *)

  (** ** Expressions *)
Inductive expr : Type :=
  | EAtom : atom -> expr
  | EArraySet : atom -> atom -> atom -> btyp -> expr
  | ERecordUpdate : atom -> ident -> atom -> btyp -> expr
  | EApp : atom -> list atom -> btyp -> expr
  | EIfThenElse : atom -> expr -> expr -> btyp -> expr
  | EMatch : atom -> list (pattern * expr) -> btyp -> expr
  | ELetIn : ident -> expr -> expr -> btyp -> expr
  | EAttr : ident -> expr -> expr.

Fixpoint btypof_expr (e: expr) : btyp :=
  match e with
  | EAtom a => btypof_atom a
  | EArraySet _ _ _ ty
  | ERecordUpdate _ _ _ ty
  | EApp _ _ ty
  | EIfThenElse _ _ _ ty
  | EMatch _ _ ty
  | ELetIn _ _ _ ty => ty
  | EAttr _ e1 => btypof_expr e1
  end.
  
(** ** Functions *)

Definition function : Type := Syntax.function expr btyp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef expr btyp literal.

Definition prog_types_t := smaplist (type_def (btyp * layout)).

Definition prog_tabs_t := smaplist struct_or_union.


(** ** Programs *)

Definition program : Type := Syntax.program expr btyp literal.

(** * Expression well-formdness *)

(** An expression [e] is well-formed w.r.t. a set of global and local symbols [globs] and [locals]
    if all of the following conditions are met:
    - Bindings in [e] don't shadow identifiers in [globs] and [locals];
    - There is no variable shadowing in [e];
    - [e] is closed. *)

Section WF.
  
  Variable globs: SSet.t.

  Definition var_defined (locals: SSet.t) (x: ident) : bool :=
    (SSet.mem x locals) || (SSet.mem x globs).

  Fixpoint wf_atom (locals: SSet.t) (a: atom) : bool :=
    match a with
    | ATrue | AFalse
    | AInt32 _ _ | AInt64 _ _
    | AConstr _ _ _ => true
    | AVar x _ => var_defined locals x
    | ACast a1 _
    | AUnaryOp _ a1 _
    | ARecordProj a1 _ _ _ => wf_atom locals a1
    | ABinaryOp _ a1 a2 _
    | AArrayGet a1 a2 _ _ =>
        (wf_atom locals a1) && (wf_atom locals a2)
    | APureCall f _ args _ =>
        (var_defined locals f) && (List.forallb (wf_atom locals) args)
  end.

  Fixpoint wf_expr (locals: SSet.t) (e: expr) : bool :=
    match e with
    | EAtom a => wf_atom locals a
    | EArraySet a1 a2 a3 _ =>
        (wf_atom locals a1) && (wf_atom locals a2) && (wf_atom locals a3)
    | ERecordUpdate a1 _ a2 _ =>
        (wf_atom locals a1) && (wf_atom locals a2)
    | EApp f args _ =>
        (wf_atom locals f) && (List.forallb (wf_atom locals) args)
    | EIfThenElse a e1 e2 _ =>
        (wf_atom locals a) && (wf_expr locals e1) && (wf_expr locals e2)
    | EMatch a cases _ =>
        (wf_atom locals a) && List.forallb (fun '(_, ei) => (wf_expr locals) ei) cases
    | ELetIn x e1 e2 _ =>
        negb (SSet.mem x globs)
        && negb (SSet.mem x locals)
        && (wf_expr locals e1)
        && (wf_expr (SSet.add x locals) e2)
    | EAttr _ e1 => wf_expr locals e1
    end.

End WF.

(** * Pretty-printing *)

Module Pp.
  Import Pp.
  Import String.

  Fixpoint pp_expr (e:expr) : box :=
    match e with
    | EAtom a => Printer.pp_atom a
    | EArraySet a i v _ => Pp.seq (Printer.pp_atom a :: Bstr "[" :: Printer.pp_atom i :: Bstr "] <- " :: Printer.pp_atom v :: nil)
    | ERecordUpdate a fd v _ => Pp.seq (Printer.pp_atom a :: Bstr "." :: Bstr fd :: Bstr " <- " :: Printer.pp_atom v :: nil)
    | EApp a l _ => Pp.seq (Printer.pp_atom a :: Bstr "(" :: pp_list (Bstr ", ") Printer.pp_atom l :: Bstr ")" :: nil)
    | EMatch a l _ => Bstr "match ... "
    | EIfThenElse c t e _ => Bstack
                             (Bcat (Bstr "if ") (Printer.pp_atom c))
                             (Bstack (Bcat (Bstr "then ") (pp_expr t))
                                     (Bcat (Bstr "else ") (pp_expr e)) Left) Left
    | ELetIn id e1 e2 _ => Bcat (Bstr "let ") (Bstack (Pp.seq (Bstr id :: Bstr " := " :: pp_expr e1 :: Bstr " in " :: nil))
                                              (pp_expr e2) Left)
    | EAttr id e => Pp.seq (Bstr "#[ " :: Bstr id :: Bstr " ]"  :: pp_expr e :: nil)
    end.

  Definition pp_program (p:program) : box :=
    Printer.pp_program Printer.pp_btyp  Printer.pp_literal pp_expr p.

End Pp.

(** * Denotational semantics *)

Section DENOT.

  Variable arch : Target.archi.

  Variable tabs : PMap.t Type.

  Notation genv := (@Denot.genv tabs).

  Notation lenv := (@Denot.lenv tabs).

  Notation value := (@Denot.value tabs).

  Notation eval_typ := (eval_typ tabs).

  Notation eval_atom := (@Denot.eval_atom arch tabs).

  Definition typof_expr (te:tenv) (e:expr) : option typ :=
    btyp_to_typ te (btypof_expr e).



  Fixpoint eval_expr_rec (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr) : option (eval_typ ty) :=
    match e with
    | EAtom a =>
        let* ta := typof_atom te a in
        ecast_typ tabs (eval_atom te ge le ta a) ty
    | EArraySet a1 a2 a3 bt =>
        let* t := btyp_to_typ te bt in
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* ta3 := typof_atom te a3 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        let* v3 := eval_atom te ge le ta3 a3 in
        ecast_typ tabs (eval_array_set arch tabs ta1 v1 ta2 v2 ta3 v3 t) ty
    | ERecordUpdate a1 k a2 bt =>
        let* t := btyp_to_typ te bt in
        let* ta1 := typof_atom te a1 in
        let* ta2 := typof_atom te a2 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let* v2 := eval_atom te ge le ta2 a2 in
        ecast_typ tabs (eval_record_update tabs ta1 v1 k ta2 v2 t) ty
    | EApp f args btr =>
        let* tr := btyp_to_typ te btr in
        let* tf := typof_atom te f in
        match tf with
        | TFun tparams tret =>
            let* f := eval_atom te ge le  (TFun tparams tret) f in
            let* vargs := DList.map2 _ (eval_atom te ge le) args tparams in
            ecast_typ tabs (eval_app_option tabs tparams tret f vargs tr) ty
            (*let* vargs := DList.mmap _ (eval_atom te ge le) args tparams in
            eval_app tabs tparams tret f vargs ty *)
        |  _  => fail
        end
    | EIfThenElse a1 e2 e3 _ =>
        let* v1 := eval_atom te ge le TBool a1  in
        if v1 then eval_expr_rec te ge le ty e2
        else eval_expr_rec te ge le ty e3
    | EMatch a1 cases _  =>
        let* ta1:= typof_atom te a1 in
        let* v1 := eval_atom te ge le ta1 a1 in
        let vcases := MapList.map (eval_expr_rec te ge le ty) cases in
        eval_match tabs ta1 v1 ty vcases
    | ELetIn x e1 e2 _ =>
        let* te1 := typof_expr te e1 in
        let* v1 := eval_expr_rec te ge le te1 e1 in
        let le' := lenv_update tabs le x (Val tabs te1 v1) in
        eval_expr_rec te ge le' ty e2
    | EAttr _ e1 => eval_expr_rec te ge le ty e1
    end.

  Definition eval_expr (te: tenv) (ge: genv) (le: lenv) (ty:typ) (e: expr) : option (eval_typ ty) :=
    (eval_expr_rec te ge le ty e).

  Definition eval_fun (te: tenv) (ge:genv) (params : smaplist typ) (tret:typ) (e:expr): Types.eval_typ tabs (TFun (map (fun x : String.string * typ => snd x) params) tret) := eval_fun tabs eval_expr te ge params tret e.


  Definition eval_def_fun := eval_def_fun tabs eval_expr.


  Fixpoint eval_def_rec (te: tenv) (ge: genv) (defs: list globdef) (x: ident) : option value :=
    match defs with
    | nil => fail
    | d :: defs' =>
        match d with
        | DefConst y l ty =>
            let* ge' := eval_def_const tabs te ge y l ty in
            if Ident.eq_dec x y then genv_get tabs ge' x
            else eval_def_rec te ge' defs' x
        | DefFun y f =>
            let* ge':= eval_def_fun  te ge y f in
            if Ident.eq_dec x y then genv_get tabs ge' x
            else eval_def_rec te ge' defs' x
        | DeclConst y _
        | DeclFun y _ _ =>
            if Ident.eq_dec x y then genv_get tabs ge x
            else eval_def_rec te ge defs' x
        end
    end.



  Definition eval_value_err_typ (rv: option value) : Type :=
    match rv with
    | Some (Val _ tv _) => eval_typ tv
    | None => unit
    end.

  Definition eval_def (impl: genv) (prog: program) (x: ident) : option value :=
    let* te := tenv_of_type_defs (prog_types prog) in
    eval_def_rec te impl (prog_defs prog) x.

  (** Evaluation of a whole program *)

  Definition eval_prog (impl: genv) (prog: program) : option (tenv * genv) :=
    Denot.eval_prog tabs  eval_expr impl prog.

  Definition eval_prog_rec (te:tenv) (impl: genv) (ge:genv) (prog: list globdef) : option genv :=
    Denot.eval_prog_rec tabs  eval_expr te impl ge prog.


  (** Redefinition of eval_def by computing the whole global environment first *)

  Definition eval_def2 (impl: genv) (prog: program) (x: ident) : option value :=
    let* (_, ge) := eval_prog impl prog in
    genv_get tabs ge x.

End DENOT.
