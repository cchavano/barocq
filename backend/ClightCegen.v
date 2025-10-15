From Coq Require Import ZArith String List FMapPositive MSetPositive.
From compcert Require Import AST Ctypes Clight ClightCe Clightdefs Cop Maps Integers.
From BarocqComp Require Import Ident Benum Error Maps2 Utils Syntax Imp2.
Import ClightNotations.

Local Open Scope clight_scope.
Local Open Scope string_scope.

Section TRANSL.

  Variable abs_types_impl : PMap.t Ctypes.type.

  Fixpoint transl_typ2 (ty: typ2) : Ctypes.type :=
    match ty with
    | TVoid => Tvoid
    | TBool => tbool
    | TInt32 Types.Signed => tint
    | TInt32 Types.Unsigned => tuint
    | TInt64 Types.Signed => tlong
    | TInt64 Types.Unsigned => tulong
    | TArray ta => tptr (transl_typ2 ta)
    | TRecord t => tptr (Tstruct (Ident.to_pos t) noattr)
    | TEnum te => Tenum (Ident.to_pos te) noattr
    | TFun tparams tret =>
        let tparams' := List.map transl_typ2 tparams in
        let tret' := transl_typ2 tret in
        tptr (Tfunction tparams' tret' cc_default)
    | TAbs t => tptr (PMap.get (Ident.to_pos t) abs_types_impl)
    end.

  Definition transl_typ2_to_xtype (ty: typ2) : AST.xtype :=
    match ty with
    | TVoid => Xvoid
    | TBool => Xbool
    | TInt32 _ => Xint
    | TInt64 _ => Xlong
    | TEnum _ => Xint
    | TArray _
    | TRecord _
    | TFun _ _ 
    | TAbs _ => Xptr
    end.

  Definition transl_typ2_lit (ty: typ2) (n: Z) : Ctypes.type :=
    match ty with
    | TArray ta => Tarray (transl_typ2 ta) n noattr
    | TRecord t => Tstruct (Ident.to_pos t) noattr
    | _ => transl_typ2 ty
    end.

  Definition transl_literal_base (l: Imp2.literal_base) : AST.init_data :=
    match l with
    | LbTrue => Init_int32 Int.one
    | LbFalse => Init_int32 Int.zero
    | LbInt32 i => Init_int32 i
    | LbInt64 i => Init_int64 i
    | LbVar x => Init_addrof (Ident.to_pos x) Ptrofs.zero
    end.

  Definition transl_literal (l: Imp2.literal) : list AST.init_data :=
    match l with
    | Imp2.LBase b _ => transl_literal_base b :: nil
    | Imp2.LArray a _ => map transl_literal_base a
    | Imp2.LRecord st _ => map (fun '(_, lx) => transl_literal_base lx) st
    end.

  Definition transl_unary_op (op: Syntax.unary_op) : res Cop.unary_operation :=
    match op with
    | UopNotbool => eret Onotbool
    | UopNotint => eret Onotint
    | UopNeg => eret Oneg
    | UopPlus => fail
    end.

  Definition transl_binary_op (op: Syntax.binary_op) : res Cop.binary_operation :=
    match op with
    | BopAndint => ret Oand
    | BopOrint => ret Oor
    | BopXorbool => ret One
    | BopXorint => ret Oxor
    | BopAdd => ret Oadd
    | BopSub => ret Osub
    | BopMul => ret Omul
    | BopDiv => ret Odiv
    | BopMod => ret Omod
    | BopShl => ret Oshl
    | BopShr => ret Oshr
    | BopEq => ret Oeq
    | BopNeq => ret One
    | BopLt => ret Olt
    | BopGt => ret Ogt
    | BopLe => ret Ole
    | BopGe => ret Oge
    | BopAndbool
    | BopOrbool =>
        failwith "ClightCegen.transl_binary_op: unsupported boolean operator"
    end.

  Fixpoint transl_atom (globs: pset) (a: Imp2.atom) : res ClightCe.expr :=
    match a with
    | ATrue => ret (Econst_int Int.one tbool)
    | AFalse => ret (Econst_int Int.zero tbool)
    | AInt32 i _ => ret (Econst_int i tint)
    | AInt64 i _ => ret (Econst_long i tlong)
    | AConstr x ty => ret (Eenumlit (Ident.to_pos x) (transl_typ2 ty))
    | AVar x ty =>
        if smem globs (Ident.to_pos x) then ret (Evar (Ident.to_pos x) (transl_typ2 ty))
        else ret (Etempvar (Ident.to_pos x) (transl_typ2 ty))
    | ACast a ty =>
        let* e := transl_atom globs a in
        ret (Ecast e (transl_typ2 ty))
    | AUnaryOp op a1 ty =>
        let* e := transl_atom globs a1 in
        let t := transl_typ2 ty in
        match transl_unary_op op with
        | OK op' => ret (Eunop op' e t)
        | Error _ => ret e
        end
    | ABinaryOp op a1 a2 ty =>
        let* e1 := transl_atom globs a1 in
        let* e2 := transl_atom globs a2 in
        let t := transl_typ2 ty in
        let* op' := transl_binary_op op in
        ret (Ebinop op' e1 e2 t)
    end.

  Definition deref_pointer (ty: type) : type :=
    match ty with
    | Tpointer t _ => t
    | _ => ty
    end.

  Fixpoint transl_deep_access (globs: pset) (a: atom) (acs: list access) : res ClightCe.expr :=
    match acs with
    | nil => transl_atom globs a
    | ac :: nil =>
        match ac with
        | AcRecordField f ty =>
            let* e := transl_atom globs a in
            let tderef := deref_pointer (typeof e) in
            let tfield := transl_typ2 ty in
            ret (Efield (Ederef e tderef) (Ident.to_pos f) tfield)
        | AcArrayIndex ai ty =>
            let* e := transl_atom globs a in
            let* ei := transl_atom globs ai in
            let tarith := typeof e in
            let tderef := transl_typ2 ty in
            ret (Ederef (Ebinop Oadd e ei tarith) tderef)
        end
    | ac :: acs' =>
        match ac with
        | AcRecordField f ty =>
          let* er := transl_deep_access globs a acs' in
          let tderef := deref_pointer (typeof er) in
          let tfield := transl_typ2 ty in
          ret (Efield (Ederef er tderef) (Ident.to_pos f) tfield)    
        | AcArrayIndex ai ty =>
            let* er := transl_deep_access globs a acs' in
            let* ei := transl_atom globs ai in
            let tarith := typeof er in
            let tderef := transl_typ2 ty in
            ret (Ederef (Ebinop Oadd er ei tarith) tderef)
        end
    end.

  Definition transl_expr (globs: pset) (e: Imp2.expr) : res ClightCe.expr :=
    match e with
    | EAtom a _ => transl_atom globs a
    | EArrayGet a1 a2 ty =>
        let* e1 := transl_atom globs a1 in
        let* e2 := transl_atom globs a2 in
        let tarith := typeof e1 in
        let tderef := transl_typ2 ty in
        ret (Ederef (Ebinop Oadd e1 e2 tarith) tderef)
    | ERecordProj a f ty =>
        let* e := transl_atom globs a in
        let tderef := deref_pointer (typeof e) in
        let tfield := transl_typ2 ty in
        ret (Efield (Ederef e tderef) (Ident.to_pos f) tfield)
    | EDeepAccess a acs _ => transl_deep_access globs a (List.rev' acs)
    end.

  Definition transl_ecomp (globs: pset) (ec: Imp2.ecomp) : res ClightCe.statement :=
    match ec with
    | EcArraySet a1 a2 a3 =>
        let* e1 := transl_atom globs a1 in
        let* e2 := transl_atom globs a2 in
        let* e3 := transl_atom globs a3 in
        let tarith := typeof e1 in
        let tderef := typeof e3 in
        ret (Sassign (Ederef (Ebinop Oadd e1 e2 tarith) tderef) e3)
    | EcRecordUpdate a1 f a2 =>
        let* e1 := transl_atom globs a1 in
        let* e2 := transl_atom globs a2 in
        let tderef := deref_pointer (typeof e1) in
        let tfield := typeof e2 in
        ret (Sassign (Efield (Ederef e1 tderef) (Ident.to_pos f) tfield) e2)
    end.

  Fixpoint transl_cond_atom (globs: pset) (a: atom) : res ClightCe.cexpr :=
    match transl_atom globs a with
    | OK a' => ret (CE_expr a')
    | Error _ =>
        match a with
        | AUnaryOp op a1 _ =>
            let* a1' := transl_cond_atom globs a1 in
            match op with
            | UopNotbool => ret (CE_not a1')
            | _ => fail
            end
        | ABinaryOp op a1 a2 _ =>
            let* a1' := transl_cond_atom globs a1 in
            let* a2' := transl_cond_atom globs a2 in
            match op with
            | BopAndbool => ret (CE_and a1' a2')
            | BopOrbool => ret (CE_or a1' a2')
            | _ => fail
            end
        | _ => fail
        end
    end.

  Fixpoint transl_statement (globs: pset) (s: Imp2.statement) (tret: Ctypes.type): res ClightCe.statement :=
    let fix transl_switch_cases (globs: pset) (ei: AST.ident) (cases: list (pattern * Imp2.statement)) : res ClightCe.labeled_statements :=
      match cases with
      | nil => fail
      | (p, sp) :: nil =>
          let* sp' := transl_statement globs sp tret in
          match p with
          | PIdent i =>
              let default_retval :=
                match tret with
                | Tvoid => None
                | _ => Some (Econst_int Int.zero tint)
                end
              in
              ret (LScons (Some (SwitchE (Ident.to_pos i) ei)) (Ssequence sp' Sbreak)
                    (LScons None (Sreturn default_retval) LSnil))
          | PWildcard =>
              ret (LScons None sp' LSnil)
          end
      | (p, sp) :: ((_ :: _) as cases') =>
          match p with
          | PIdent i =>
              let* sc' := transl_statement globs sp tret in
              let* ccases := transl_switch_cases globs ei cases' in
              ret (LScons (Some (SwitchE (Ident.to_pos i) ei)) (Ssequence sc' Sbreak) ccases)
          | PWildcard => fail (* Ill-typed program *)
          end
      end
    in
    match s with
    | StSkip => ret Sskip
    | StSetExpr x e =>
        let* e' := transl_expr globs e in
        ret (Sset (Ident.to_pos x) e')
    | StEcomp ec => transl_ecomp globs ec
    | StCall x a args _ =>
        let x' :=
          match x with
          | Some x => Some (Ident.to_pos x)
          | _ => None
          end
        in
        let* e := transl_atom globs a in
        let* args' := mmap (transl_atom globs) args in
        ret (Scall x' e args')
    | StIfThenElse a s1 s2 =>
        let* e := transl_cond_atom globs a in
        let* s1' := transl_statement globs s1 tret in
        let* s2' := transl_statement globs s2 tret in
        ret (Sifthenelse e s1' s2')
    | StSwitch a cases =>
        let* e := transl_atom globs a in
        match typeof e with
        | Tenum ei _ =>
            let* cases' := transl_switch_cases globs ei cases in
            ret (Sswitch e cases')
        | _ => fail
        end
    | StSequence s1 s2 =>
        let* s1' := transl_statement globs s1 tret in
        let* s2' := transl_statement globs s2 tret in
        ret (Ssequence s1' s2')
    | StReturn a =>
        match a with
        | Some a =>
            let* e := transl_atom globs a in
            ret (Sreturn (Some e))
        | None => ret (Sreturn None)
        end
    end.

  Definition transl_function (globs: pset) (f: Imp2.function) : res ClightCe.function :=
    let ty := transl_typ2 (fn_return f) in
    let params := List.map (fun '(pid, pty) => (Ident.to_pos pid, transl_typ2 pty)) (fn_params f) in
    let temps := List.map (fun '(pid, pty) => (Ident.to_pos pid, transl_typ2 pty)) (fn_vars f) in
    let* body := transl_statement globs (fn_body f) ty in
    ret {|
      ClightCe.fn_return := ty;
      ClightCe.fn_callconv := cc_default;
      ClightCe.fn_params := params;
      ClightCe.fn_vars := nil;
      ClightCe.fn_temps := temps;
      ClightCe.fn_body := body
    |}.

  Definition transl_abs_function (f: ident) (tparams: list (param_attr * typ2)) (tret: typ2) : ClightCe.fundef :=
    let tparams := List.map snd tparams in
    let ext_func :=
      EF_external f
        {|
          sig_args := List.map transl_typ2_to_xtype tparams;
          sig_res := transl_typ2_to_xtype tret;
          sig_cc := cc_default
        |}
    in
    External ext_func (List.map transl_typ2 tparams) (transl_typ2 tret) cc_default.

  Import ListNotations.

  Definition cglobdef : Type :=
    AST.ident * AST.globdef (Ctypes.fundef ClightCe.function) type.

  Definition literal_size (l: Imp2.literal) : Z :=
    match l with
    | Imp2.LArray a _ => Z.of_nat (Barray.length a)
    | _ => Z.of_nat 0
    end.

  Fixpoint transl_globdefs_rec (defs: list Imp2.globdef) (globs: pset): res (list cglobdef) :=
    match defs with
    | nil => ret nil
    | d :: defs' =>
        match d with
        | DefConst x l ty =>
            let init := transl_literal l in
            let t := transl_typ2_lit ty (literal_size l) in
            let (t, readonly) :=
              match ty, l with
              | TRecord _, LBase (LbVar _) _ => (tptr t, true)
              | (TBool | TInt32 _ | TInt64 _ | TEnum _), _ => (t, true)
              | _, _ => (t, false)
              end
            in
            let d := (Ident.to_pos x, Gvar {|
              gvar_info := t;
              gvar_init := init;
              gvar_readonly := readonly;
              gvar_volatile := false
            |}) in
            let* r := transl_globdefs_rec defs' (sadd globs (Ident.to_pos x)) in
            ret (d :: r)
        | DefFun x f =>
            let* f' := transl_function globs f in
            let d := ((Ident.to_pos x), (Gfun (Internal f'))) in
            let* r := transl_globdefs_rec defs' (sadd globs (Ident.to_pos x)) in
            ret (d :: r)
        | DeclConst x ty =>
            let t := transl_typ2 ty in
            let* r := transl_globdefs_rec defs' (sadd globs (Ident.to_pos x)) in
            let d := ((Ident.to_pos x), Gvar {|
              gvar_info := t;
              gvar_init := nil;
              gvar_readonly := true;
              gvar_volatile := false
            |})
            in
            ret (d :: r)
        | DeclFun x tparams tret =>
            let* r := transl_globdefs_rec defs' (sadd globs (Ident.to_pos x)) in
            let d := ((Ident.to_pos x), Gfun (transl_abs_function x tparams tret)) in
            ret (d :: r)
      end
    end.

  Definition transl_enum_btyp (x: ident) (elems: list ident) : Ctypes.composite_definition :=
    Composite (Ident.to_pos x) Enum (List.map (fun e => Member_plain (Ident.to_pos e) tint) elems) noattr.

  Definition transl_globdefs (defs: list Imp2.globdef) : res (list cglobdef) :=
    transl_globdefs_rec defs sempty.
    
  Fixpoint transl_record_fields (fields: smaplist typ2) : Ctypes.members :=
    match fields with
    | nil => nil
    | (x, tx) :: fields' =>
        let tx' := transl_typ2 tx in
        let r := transl_record_fields fields' in
        (Member_plain (Ident.to_pos x) tx') :: r
    end.

  Definition transl_record_btyp (x: ident) (fields: smaplist typ2) : Ctypes.composite_definition :=
    Composite (Ident.to_pos x) Struct (transl_record_fields fields) noattr.

  Fixpoint transl_prog_types (types: list (type_def typ2)) : list Ctypes.composite_definition :=
    match types with
    | nil => nil
    | td :: types' =>
      let cdr := transl_prog_types types' in
      match td with
      | TdEnum ed => (transl_enum_btyp (ed_name ed) (ed_elems ed)) :: cdr
      | TdRecord rd => (transl_record_btyp (rd_name rd) (rd_fields rd)) :: cdr
      | _ => cdr
      end
    end.

  Fixpoint public_idents (defs: list Imp2.globdef) : list ident :=
    match defs with
    | nil => nil
    | d :: defs' =>
        match d with
        | DefConst x _ _
        | DefFun x _
        | DeclConst x _
        | DeclFun x _ _ => x :: (public_idents defs')
        end
    end.

  Definition _main : AST.ident := $"main".

  Close Scope string_scope.

End TRANSL.

Fixpoint mk_abs_types_impl (types: list (type_def typ2)) : PMap.t Ctypes.type :=
  match types with
  | nil => PMap.init Tvoid
  | td :: types' =>
      match td with
      | TdAbstract tid tk =>
          let ct :=
            match tk with
            | SU_struct => Tstruct (Ident.to_pos tid) noattr
            | SU_union => Tunion (Ident.to_pos tid) noattr
            end
          in
          PMap.set (Ident.to_pos tid) ct (mk_abs_types_impl types')
      | _ => mk_abs_types_impl types'
      end
  end.

Definition transl_program (prog: Imp2.program) : res ClightCe.program :=
  let types := prog_types prog in
  let defs := prog_defs prog in
  let abs_types_impl := mk_abs_types_impl types in
  let ts := transl_prog_types abs_types_impl types in
  let* cdefs := transl_globdefs abs_types_impl defs in
  let public := List.map Ident.to_pos (public_idents defs) in
  let main := _main in
  match Ctypes.make_program ts cdefs public main with
  | OK prog => OK prog
  | Error _ => failwith "ClightgenCe.transl_program: error when calling Ctypes.make_program"
  end.

Section IDENTS.

  Fixpoint typ_idents_rec (ids: pset) (t: Ctypes.type) : pset :=
    match t with
    | Tstruct tid _
    | Tunion tid _ => sadd ids tid
    | Tpointer t' _
    | Tarray t' _ _ => sunion ids (typ_idents_rec ids t')
    | Tfunction tparams tret _ =>
        List.fold_left
          (fun ids tp => typ_idents_rec ids tp)
          tparams
          (typ_idents_rec ids tret)
    | _ => ids
    end.

  Definition typ_idents (t: Ctypes.type) : pset :=
    typ_idents_rec sempty t.

  Definition function_idents (f: ClightCe.function) : pset :=
    let param_idents :=
      List.fold_left
      (fun ids '(pid, pty) =>
        sunion (typ_idents pty) (sadd ids pid))
      (ClightCe.fn_params f)
      sempty
    in
    let var_idents :=
      List.fold_left
        (fun ids vid => sadd ids vid)
        (List.map fst (ClightCe.fn_vars f))
        sempty
    in
    let temp_idents :=
      List.fold_left
        (fun ids tid => sadd ids tid)
        (List.map fst (ClightCe.fn_temps f))
        sempty
    in
    sunion (sunion param_idents var_idents) temp_idents.

  Definition globdef_idents (def: cglobdef) : pset :=
    let '(x, def) := def in
    let ids :=
      match def with
      | Gfun (Internal f) => function_idents f
      | Gfun (External _ tparams tret _) =>
          List.fold_left
            (fun ids pty => sunion ids (typ_idents pty))
            tparams
            (typ_idents tret)
      | _ => sempty
      end
    in
    sadd ids x.

  Fixpoint members_idents (m: Ctypes.members) : pset :=
    match m with
    | nil => sempty
    | h :: t => sadd (members_idents t) (name_member h)
    end.

  Definition composite_idents (cd: Ctypes.composite_definition) : pset :=
    match cd with Composite x _ m _ => sadd (members_idents m) x end.

  Definition program_idents (prog: ClightCe.program) : list AST.ident :=
    let ids :=
      List.fold_left
        (fun ids def => sunion (globdef_idents def) ids)
        (Ctypes.prog_defs prog)
        sempty
    in
    let ids :=
      List.fold_left
        (fun ids types => sunion (composite_idents types) ids)
        (Ctypes.prog_types prog)
        ids
    in
    PositiveSet.elements ids.

End IDENTS.