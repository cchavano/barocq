From BarocqComp Require Import Maps2 Syntax Imp2 Imp2gen.

Section REWRITE.

  Variable GLOBINFO : ident * ident.

  Definition ginfo_tid := fst GLOBINFO.

  Definition ginfo_vname := snd GLOBINFO.

  Definition is_glob_typ (ty: typ2) :=
    match ty with
    | TRecord rid =>
        if Ident.eq_dec rid ginfo_tid then true
        else false
    | _ => false
    end.

  Fixpoint rewrite_typ (t: typ2) : typ2 :=
    match t with
    | TFun tparams tret =>
        TFun (List.map rewrite_typ tparams) (rewrite_typ tret)
    | TRecord rid =>
        if Ident.eq_dec rid ginfo_tid then TVoid
        else t
    | _ => t
  end.

  Fixpoint rewrite_atom (a: atom) : atom :=
    match a with
    | ATrue | AFalse | AInt32 _ _ | AInt64 _ _ | AConstr _ _ _ => a
    | AVar x tx =>
        if is_glob_typ tx then AVar ginfo_vname tx
        else a
    | ACast a ty => ACast (rewrite_atom a) ty
    | AUnaryOp op a ty => AUnaryOp op (rewrite_atom a) ty
    | ABinaryOp op a1 a2 ty => ABinaryOp op (rewrite_atom a1) (rewrite_atom a2) ty
    | AArrayGet a i ly ty => AArrayGet (rewrite_atom a) (rewrite_atom i) ly ty
    | ARecordProj a f ly ty => ARecordProj (rewrite_atom a) f ly ty
    | APureCall f tf args tr =>
        let tr' := if is_glob_typ tr (* should always be false *) then TVoid else tr in
        let args' := List.map rewrite_atom args in
        let args' :=
          List.filter (fun a => negb (is_glob_typ (typof_atom a))) args'
        in
        APureCall f tf args' tr'
    end.

  (* Definition rewrite_expr (e: expr) : expr :=
    match e with
    | ERecordProj a f ty ly => ERecordProj (rewrite_atom a) f ty ly
    | EDeepAccess a ac ty => EDeepAccess (rewrite_atom a) ac ty
    | _ => e
    end. *)

  Definition rewrite_ecomp (ec: ecomp) : ecomp := 
    match ec with
    | EcArraySet a i v => EcArraySet (rewrite_atom a) (rewrite_atom i) (rewrite_atom v)
    | EcRecordUpdate a1 f a2 => EcRecordUpdate (rewrite_atom a1) f (rewrite_atom a2)
    end.

  Fixpoint rewrite_statement (s: statement) : statement :=
    match s with
    | StSkip => StSkip
    | StSet x a =>
        if is_glob_typ (typof_atom a) then StSkip
        else StSet x (rewrite_atom a)
    | StEcomp ec => StEcomp (rewrite_ecomp ec)
    | StCall x f tf args ty =>
        let (x', ty') := 
          if is_glob_typ ty then (None, TVoid)
          else (x, ty)
        in
        let args' :=
          List.filter (fun a => negb (is_glob_typ (typof_atom a))) args
        in
        let args' := List.map rewrite_atom args' in
        StCall x' f tf args' ty'
    | StIfThenElse a s1 s2 =>
        StIfThenElse (rewrite_atom a) (rewrite_statement s1) (rewrite_statement s2)
    | StSwitch a cases =>
        StSwitch (rewrite_atom a) (MapList.map rewrite_statement cases)
    | StSequence s1 s2 =>
        StSequence (rewrite_statement s1) (rewrite_statement s2)
    | StReturn a =>
        match a with
        | Some av =>
            if is_glob_typ (typof_atom av) then StReturn None
            else StReturn (Some (rewrite_atom av))
        | None => StReturn None
        end
    end.

  Definition rewrite_function (f: function) : function :=
    {|
      fn_return := rewrite_typ (fn_return f);
      fn_params := List.filter (fun '(_, pty) => negb (is_glob_typ pty)) (fn_params f);
      fn_vars := List.filter (fun '(_, pty) => negb (is_glob_typ pty)) (fn_vars f);
      fn_body := rewrite_statement (fn_body f)
    |}.

  Definition rewrite_globdef (def: globdef) : globdef :=
    match def with
    | DefFun fid f => DefFun fid (rewrite_function f)
    | DeclFun fid tparams tret =>
        let tparams' := List.filter (fun '(_, pty) => negb (is_glob_typ pty)) tparams in
        DeclFun fid tparams' (rewrite_typ tret)
    | _ => def
    end.

  Definition rewrite_program (prog: program) : program :=
    {|
      prog_defs := List.map rewrite_globdef (prog_defs prog);
      prog_types := prog_types prog;
      prog_tabs := prog_tabs prog;
    |}.

End REWRITE.