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

  Definition rewrite_atom (a: atom) : atom :=
    match a with
    | AVar x tx =>
        if is_glob_typ tx then AVar ginfo_vname tx
        else a
    | _ => a
    end.

  Definition rewrite_expr (e: expr) : expr :=
    match e with
    | ERecordProj a f ty ly => ERecordProj (rewrite_atom a) f ty ly
    | EDeepAccess a ac ty => EDeepAccess (rewrite_atom a) ac ty
    | _ => e
    end.

  Definition rewrite_ecomp (ec: ecomp) : ecomp := 
    match ec with
    | EcRecordUpdate a1 f a2 => EcRecordUpdate (rewrite_atom a1) f a2
    | _ => ec
    end.

  Fixpoint rewrite_statement (s: statement) : statement :=
    match s with
    | StSkip => StSkip
    | StSetExpr x e =>
        match e with
        | EAtom a ta =>
            if is_glob_typ ta then StSkip
            else StSetExpr x (rewrite_expr e)
        | _ => StSetExpr x (rewrite_expr e)
        end
    | StEcomp ec => StEcomp (rewrite_ecomp ec)
    | StCall x a args ty =>
        let (x', ty') := 
          if is_glob_typ ty then (None, TVoid)
          else (x, ty)
        in
        let args' :=
          List.filter (fun a => negb (is_glob_typ (typof_atom a))) args
        in
        StCall x' a args' ty'
    | StIfThenElse a s1 s2 =>
        StIfThenElse a (rewrite_statement s1) (rewrite_statement s2)
    | StSwitch a cases =>
        StSwitch a (MapList.map rewrite_statement cases)
    | StSequence s1 s2 =>
        StSequence (rewrite_statement s1) (rewrite_statement s2)
    | StReturn a =>
        match a with
        | Some av =>
            if is_glob_typ (typof_atom av) then StReturn None
            else StReturn a
        | None => StReturn a
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