From BarocqComp Require Import Option While Benum Maps2 Syntax Types Typing Imp1 Denot.

Local Open Scope option_monad_scope.

(* Denotational pure semantics of Imp1 *)

Section DENOT.

  Variable tabs : Maps.PMap.t Type.

  Notation genv := (@Denot.genv tabs).

  Notation lenv := (@Denot.lenv tabs).

  Notation value := (@Denot.value tabs).

  Notation eval_typ := (@Types.eval_typ tabs).

  Notation eval_atom := (@Denot.eval_atom tabs).

  Notation eval_comp := (@Denot.eval_comp tabs).

  Definition typ_of_statement (ty: typ) : Type :=
    option (option (eval_typ  ty) * lenv).

  Definition eval_match (tv:typ) (v: eval_typ tv) (tr: typ) (cases: list (pattern * typ_of_statement tr)) : typ_of_statement tr :=
    (match tv as t0 return (eval_typ t0 -> typ_of_statement tr) with
    | TEnum _ elems => 
        (fun v0 => ematch_with v0 cases)
    | _ => (fun _ => fail)
    end) v.

  Definition null (ty:typ) : option (eval_typ ty) :=
    match ty with
    | TUnit => Some tt
    |  _    => None
    end.

  Fixpoint eval_statement_rec (te: tenv) (ge: genv) (le: lenv) (ty: typ) (s: statement) : typ_of_statement ty :=
    match s with
    | StSkip    => Some (null ty,le)
    | StSet x c =>
        let* tyc := typof_comp te c in
        let* vc := eval_comp te ge le tyc c in
        ret (null ty, lenv_update tabs le x (Val tabs tyc vc))
    | StIfThenElse a s1 s2 =>
        let* va := eval_atom te ge le TBool a in
        eval_statement_rec te ge le ty (if va then s1 else s2)
    | StSwitch a cases =>
        let* ta := typof_atom te a in
        let* va := eval_atom te ge le ta a in
        let vcases := MapList.map (eval_statement_rec te ge le ty) cases in
        eval_match ta va ty vcases
    | StSequence s1 s2 =>
        let* (_,le1) := eval_statement_rec te ge le TUnit s1 in
        eval_statement_rec te ge le1 ty s2
    | StWhile cond variant body =>
        let* tyd := (typof_atom te variant) in
        let* m := eval_atom te ge le tyd variant in
        let* n := nat_of_val _ m in
        let C := fun le => eval_atom te ge le TBool cond in
        let B := (fun le => let* (_,leb) := eval_statement_rec te ge le TUnit body in Some leb) in
        let* w := while C B n le in
        Some(null ty,w)
    | StReturn a =>
        let* ta := typof_atom te a in
        let*  v := eval_atom te ge le ta a in
        Some(cast_typ tabs v ty,le)
    | StAttr _ s1 => eval_statement_rec te ge le ty s1
    end.

  Definition eval_statement (te: tenv) (ge: genv) (le: lenv) (tr: typ) (s: statement) : option (eval_typ tr) :=
    let* (v,_) := eval_statement_rec te ge le tr s in v.

  Definition eval_prog (impl: genv) (prog: program) : option (tenv * genv) :=
    eval_prog tabs eval_statement impl prog.

End DENOT.
