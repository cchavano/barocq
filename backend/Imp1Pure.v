From BarocqComp Require Import Option Benum Maps2 Syntax Types Typing Imp1 Denot.

Local Open Scope option_monad_scope.

(* Denotational pure semantics of Imp1 *)

Section DENOT.

  Variable arch : Target.archi.
  Variable tabs : Maps.PMap.t Type.

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

  Definition eval_match (tv:typ) (v: eval_typ tv) (tr: option typ) (cases: list (pattern * option (typ_of_statement tr))) : option (typ_of_statement tr) :=
    (match tv as t0 return (eval_typ t0 -> option (typ_of_statement tr)) with
    | TEnum _ elems => 
        (fun v0 => match_with_err v0 cases)
    | _ => (fun _ => fail)
    end) v.

  Fixpoint eval_statement_rec (te: tenv) (ge: genv) (le: lenv) (ty: option typ) (s: statement) : option (typ_of_statement ty) :=
    match s with
    | StSkip    => match ty with
                   | None => Some le
                   | Some _ => fail
                   end

    | StSet x c =>
        match ty with
        | None =>
            let* tyc := typof_comp te c in
            let* vc := eval_comp te ge le tyc c in
            ret (lenv_update tabs le x (Val tabs tyc vc))
        | _ => fail
        end
    | StIfThenElse a s1 s2 =>
        let* va := eval_atom te ge le TBool a in
        eval_statement_rec te ge le ty (if va then s1 else s2)
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

  Definition eval_statement (te: tenv) (ge: genv) (le: lenv) (tr: typ) (s: statement) : option (eval_typ tr) :=
     eval_statement_rec te ge le (Some tr) s.

  Definition eval_prog (impl: genv) (prog: program) : option (tenv * genv) :=
    eval_prog tabs eval_statement impl prog.

End DENOT.
