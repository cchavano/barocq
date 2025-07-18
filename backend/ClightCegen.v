From Coq Require Import ZArith String List FMapPositive MSetPositive.
From compcert Require Import AST Ctypes Clight ClightCe Clightdefs Cop Maps Integers.
From BarocqComp Require Import Error MapList Utils Types Syntax.
Import ClightNotations.
Import Syntax.Typed.
From BarocqComp Require Import Imp2.

Local Open Scope clight_scope.
Local Open Scope string_scope.

Section TRANSL.

  Variable abs_types_impl : PMap.t Ctypes.type.

  Fixpoint transl_btyp (ty: btyp) : Ctypes.type :=
    match ty with
    | BBool => tbool
    | BInt32 Signed => tint
    | BInt32 Unsigned => tuint
    | BInt64 Signed => tlong
    | BInt64 Unsigned => tulong
    | BArray ta => tptr (transl_btyp ta)
    | BRecord t => tptr (Tstruct t noattr)
    | BFun tparams tret =>
        let tparams' := List.map transl_btyp tparams in
        let tret' := transl_btyp tret in
        tptr (Tfunction tparams' tret' cc_default)
    | BAbs t => tptr (PMap.get t abs_types_impl)
    end.

  Definition transl_btyp_to_xtype (ty: btyp) : AST.xtype :=
    match ty with
    | BBool => Xbool
    | BInt32 _ => Xint
    | BInt64 _ => Xlong
    | BArray _
    | BRecord _
    | BFun _ _ 
    | BAbs _ => Xptr
    end.

  Definition transl_btyp_lit (ty: btyp) (n: Z) : Ctypes.type :=
    match ty with
    | BArray ta => Tarray (transl_btyp ta) n noattr
    | BRecord t => Tstruct t noattr
    | _ => transl_btyp ty
    end.

  Definition transl_literal_base (l: Imp2.literal_base) : AST.init_data :=
    match l with
    | LbTrue => Init_int32 Int.one
    | LbFalse => Init_int32 Int.zero
    | LbInt32 i => Init_int32 i
    | LbInt64 i => Init_int64 i
    | LbVar x => Init_addrof x Ptrofs.zero
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

  Fixpoint transl_atom (globs: pset) (a: Syntax.Typed.atom) : res ClightCe.expr :=
    match a with
    | ATrue _ => ret (Econst_int Int.one tbool)
    | AFalse _ => ret (Econst_int Int.zero tbool)
    | AInt32 i _ => ret (Econst_int i tint)
    | AInt64 i _ => ret (Econst_long i tlong)
    | AVar x ty =>
        if smem globs x then ret (Evar x (transl_btyp ty))
        else ret (Etempvar x (transl_btyp ty))
    | ACast a ty =>
        let* e := transl_atom globs a in
        ret (Ecast e (transl_btyp ty))
    | AUnaryOp op a1 ty =>
        let* e := transl_atom globs a1 in
        let t := transl_btyp ty in
        match transl_unary_op op with
        | OK op' => ret (Eunop op' e t)
        | Error _ => ret e
        end
    | ABinaryOp op a1 a2 ty =>
        let* e1 := transl_atom globs a1 in
        let* e2 := transl_atom globs a2 in
        let t := transl_btyp ty in
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
            let tfield := transl_btyp ty in
            ret (Efield (Ederef e tderef) f tfield)
        | AcArrayIndex ai ty =>
            let* e := transl_atom globs a in
            let* ei := transl_atom globs ai in
            let tarith := typeof e in
            let tderef := transl_btyp ty in
            ret (Ederef (Ebinop Oadd e ei tarith) tderef)
        end
    | ac :: acs' =>
        match ac with
        | AcRecordField f ty =>
          let* er := transl_deep_access globs a acs' in
          let tderef := deref_pointer (typeof er) in
          let tfield := transl_btyp ty in
          ret (Efield (Ederef er tderef) f tfield)    
        | AcArrayIndex ai ty =>
            let* er := transl_deep_access globs a acs' in
            let* ei := transl_atom globs ai in
            let tarith := typeof er in
            let tderef := transl_btyp ty in
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
        let tderef := transl_btyp ty in
        ret (Ederef (Ebinop Oadd e1 e2 tarith) tderef)
    | ERecordProj a f ty =>
        let* e := transl_atom globs a in
        let tderef := deref_pointer (typeof e) in
        let tfield := transl_btyp ty in
        ret (Efield (Ederef e tderef) f tfield)
    | EDeepAccess a acs _ => transl_deep_access globs a (List.rev' acs)
    end.

  Definition transl_ecomp (globs: pset) (ec: Imp2.ecomp) : res (ClightCe.expr * ClightCe.statement) :=
    match ec with
    | EcArraySet a1 a2 a3 =>
        let* e1 := transl_atom globs a1 in
        let* e2 := transl_atom globs a2 in
        let* e3 := transl_atom globs a3 in
        let tarith := typeof e1 in
        let tderef := typeof e3 in
        ret (e1, Sassign (Ederef (Ebinop Oadd e1 e2 tarith) tderef) e3)
    | EcRecordUpdate a1 f a2 =>
        let* e1 := transl_atom globs a1 in
        let* e2 := transl_atom globs a2 in
        let tderef := deref_pointer (typeof e1) in
        let tfield := typeof e2 in
        ret (e1, Sassign (Efield (Ederef e1 tderef) f tfield) e2)
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

  Fixpoint transl_statement (globs: pset) (s: Imp2.statement) : res ClightCe.statement :=
    match s with
    | StSkip => ret Sskip
    | StSetExpr x e =>
        let* e' := transl_expr globs e in
        ret (Sset x e')
    | StSetEcomp x ec =>
        let* (e, s) := transl_ecomp globs ec in
        let sset := Sset x e in
        ret (Ssequence s sset)
    | StCall x a args =>
        let* e := transl_atom globs a in
        let* args' := mmap (transl_atom globs) args in
        ret (Scall (Some x) e args')
    | StIfThenElse a s1 s2 =>
        let* e := transl_cond_atom globs a in
        let* s1' := transl_statement globs s1 in
        let* s2' := transl_statement globs s2 in
        ret (Sifthenelse e s1' s2')
    | StSequence s1 s2 =>
        let* s1' := transl_statement globs s1 in
        let* s2' := transl_statement globs s2 in
        ret (Ssequence s1' s2')
    | StReturn a =>
        let* e := transl_atom globs a in
        ret (Sreturn (Some e))
    end.

  Definition transl_function (globs: pset) (f: Imp2.function) : res ClightCe.function :=
    let ty := transl_btyp (fn_return f) in
    let params := map_k transl_btyp (fn_params f) in
    let temps := map_k transl_btyp (fn_vars f) in
    let* body := transl_statement globs (fn_body f) in
    ret {|
      ClightCe.fn_return := ty;
      ClightCe.fn_callconv := cc_default;
      ClightCe.fn_params := params;
      ClightCe.fn_vars := nil;
      ClightCe.fn_temps := temps;
      ClightCe.fn_body := body
    |}.

  Definition transl_abs_function (f: ident) (tparams: list (param_attr * btyp)) (tret: btyp) : ClightCe.fundef :=
    let tparams := List.map snd tparams in
    let ext_func :=
      EF_external (string_of_ident f)
        {|
          sig_args := List.map transl_btyp_to_xtype tparams;
          sig_res := transl_btyp_to_xtype tret;
          sig_cc := cc_default
        |}
    in
    External ext_func (List.map transl_btyp tparams) (transl_btyp tret) cc_default.

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
            let t := transl_btyp_lit ty (literal_size l) in
            let t :=
              match ty, l with
              | BRecord _, LBase (LbVar _) _ => tptr t
              | _, _ => t
              end
            in
            let d := (x, Gvar {|
              gvar_info := t;
              gvar_init := init;
              gvar_readonly := btyp_is_prim ty;
              gvar_volatile := false
            |}) in
            let* r := transl_globdefs_rec defs' (sadd globs x) in
            ret (d :: r)
        | DefFun x f =>
            let* f' := transl_function globs f in
            let d := (x, (Gfun (Internal f'))) in
            let* r := transl_globdefs_rec defs' (sadd globs x) in
            ret (d :: r)
        | DeclConst x ty =>
            let t := transl_btyp ty in
            let* r := transl_globdefs_rec defs' (sadd globs x) in
            let d := (x, Gvar {|
              gvar_info := t;
              gvar_init := nil;
              gvar_readonly := false;
              gvar_volatile := false
            |})
            in
            ret (d :: r)
        | DeclFun x tparams tret =>
            let* r := transl_globdefs_rec defs' (sadd globs x) in
            let d := (x, Gfun (transl_abs_function x tparams tret)) in
            ret (d :: r)
      end
    end.

  Definition transl_globdefs (defs: list Imp2.globdef) : res (list cglobdef) :=
    transl_globdefs_rec defs sempty.
    
  Fixpoint transl_struct_fields (fields: list (ident * btyp)) : Ctypes.members :=
    match fields with
    | nil => nil
    | (x, tx) :: fields' =>
        let tx' := transl_btyp tx in
        let r := transl_struct_fields fields' in
        (Member_plain x tx') :: r
    end.

  Definition transl_struct_btyp (x: ident) (fields: list (ident * btyp)) : Ctypes.composite_definition :=
    Composite x Struct (transl_struct_fields fields) noattr.

  Definition transl_prog_types (types: list type_def) : list Ctypes.composite_definition :=
    List.map
      (fun sd => transl_struct_btyp (rd_name sd) (rd_fields sd))
      (Syntax.get_record_defs types).

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

  Definition _main : ident := $"main".

  Close Scope string_scope.

End TRANSL.

Fixpoint mk_abs_types_impl (types: list type_def) : PMap.t Ctypes.type :=
  match types with
  | nil => PMap.init Tvoid
  | td :: types' =>
      match td with
      | TdAbstract tid tk =>
          let ct :=
            match tk with
            | Struct => Tstruct tid noattr
            | Union => Tunion tid noattr
            end
          in
          PMap.set tid ct (mk_abs_types_impl types')
      | _ => mk_abs_types_impl types'
      end
  end.

Definition transl_program (prog: Imp2.program) : res ClightCe.program :=
  let types := prog_types prog in
  let defs := prog_defs prog in
  let abs_types_impl := mk_abs_types_impl types in
  let ts := transl_prog_types abs_types_impl types in
  let* cdefs := transl_globdefs abs_types_impl defs in
  let public := public_idents defs in
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

  Definition program_idents (prog: ClightCe.program) : list ident :=
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