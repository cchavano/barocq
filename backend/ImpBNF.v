From Coq Require Import List.
From compcert Require Import Maps.
From BarocqComp Require Import Error Maps2 Types Benum Syntax Typing Denot.

(** * Abstract syntax *)

(** ** Tail computations *)

Inductive tailcomp : Type :=
  | TcBegin : statement -> tailcomp -> btyp -> tailcomp
  | TcComp : comp -> btyp -> tailcomp
  | TcIfThenElse : atom -> tailcomp -> tailcomp -> btyp -> tailcomp
  | TcSwitch : atom -> list (pattern * tailcomp) -> btyp -> tailcomp
  | TcAttr : ident -> tailcomp -> tailcomp

(** ** Statements *)

with statement : Type :=
  | StSetTailcomp : ident -> tailcomp -> statement.

(** ** Functions *)

Definition function : Type := Syntax.function tailcomp btyp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef tailcomp btyp literal.

(** ** Programs *)

Definition program : Type := Syntax.program tailcomp btyp literal.

(** * Denotational semantics *)

Section DENOT.

  Variable arch : Target.archi.

  Variable tabs : PMap.t Type.

  Notation genv := (@Denot.genv tabs).

  Notation lenv := (@Denot.lenv tabs).

  Notation value := (@Denot.value tabs).

  Notation eval_typ := (@Types.eval_typ tabs).

  Notation eval_atom := (@Denot.eval_atom arch tabs).

  Notation eval_comp := (@Denot.eval_comp arch tabs).

  Definition typof_tailcomp (te: tenv) (tc: tailcomp) : res typ :=
    let fix get_typ tc :=
      match tc with
      | TcBegin _ _ ty
      | TcComp _ ty
      | TcIfThenElse _ _ _ ty
      | TcSwitch _ _ ty => ty
      | TcAttr _ tc => get_typ tc
      end
    in
    btyp_to_typ te (get_typ tc).

  Definition eval_match (tv:typ) (v: eval_typ tv) (tr: typ) (cases: list (pattern * res (eval_typ tr * lenv))) : res (eval_typ tr * lenv) :=
    (match tv as t0 return (eval_typ t0 -> res (eval_typ tr * lenv)) with
    | TEnum _ elems => 
        (fun v0 => match_with_err v0 cases)
    | _ => (fun _ => fail)
    end) v.

  Fixpoint eval_tailcomp_rec (te: tenv) (ge: genv) (le: lenv) (ty: typ) (tc: tailcomp) : res (eval_typ ty * lenv) :=
    match tc with
    | TcBegin s tc1 _ =>
        let* le' := eval_statement te ge le s in
        eval_tailcomp_rec te ge le' ty tc1
    | TcComp c _ =>
        let* vc := eval_comp te ge le ty c in
        ret (vc, le)
    | TcIfThenElse a tc1 tc _ =>
        let* va := eval_atom te ge le TBool a in
        if va then eval_tailcomp_rec te ge le ty tc1
        else eval_tailcomp_rec te ge le ty tc
    | TcSwitch a cases _ =>
        let* ta := typof_atom te a in
        let* va := eval_atom te ge le ta a in
        let vcases := MapList.map (eval_tailcomp_rec te ge le ty) cases in
        eval_match ta va ty vcases
    | TcAttr _ tc1 => eval_tailcomp_rec te ge le ty tc1
    end
  
  with eval_statement (te: tenv) (ge: genv) (le: lenv) (s: statement) : res lenv :=
    match s with
    | StSetTailcomp x tc =>
        let* ttc := typof_tailcomp te tc in
        let* (v, lec) := eval_tailcomp_rec te ge le ttc tc in
        ret (lenv_update tabs lec x (Val tabs ttc v))
    end.

  Definition eval_tailcomp (te: tenv) (ge: genv) (le: lenv) (tr: typ) (tc: tailcomp) : res (eval_typ tr) :=
    let* (v, _) := eval_tailcomp_rec te ge le tr tc in
    ret v.

  Definition eval_prog (impl: genv) (prog: program) : res (tenv * genv) :=
    Denot.eval_prog tabs tailcomp eval_tailcomp impl prog.

End DENOT.

