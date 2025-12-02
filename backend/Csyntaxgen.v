From Coq Require Import ZArith String List FMapPositive MSetPositive.
From compcert Require Import AST Ctypes Csyntax Csyntaxdefs Values Cop Maps Integers.
From BarocqComp Require Import Ident Types Benum Error Maps2 Utils Syntax Imp2.
Import ListNotations.
Import CsyntaxNotations.

Local Open Scope csyntax_scope.
Local Open Scope string_scope.

Section TRANSL.

  Variable abs_types_impl : PMap.t Ctypes.type.

  Fixpoint transl_typ2_rec (ly: layout) (ty: typ2) : Ctypes.type :=
    match ty with
    | TVoid => Tvoid
    | TBool => tbool
    | TInt32 Types.Signed => tint
    | TInt32 Types.Unsigned => tuint
    | TInt64 Types.Signed => tlong
    | TInt64 Types.Unsigned => tulong
    | TArray ta lya =>
        let ta' := transl_typ2_rec lya ta in
        match ly with
        | LyBoxed => tptr ta'
        | LyUnboxed (Some sz) => Tarray ta' sz noattr
        | _ => Tarray ta' 0%Z noattr (* ill-typed program *)
        end
    | TRecord t =>
        let tr := Tstruct (Ident.to_pos t) noattr in
        match ly with
        | LyBoxed => tptr tr
        | _ => tr
        end
    | TEnum te => Tenum (Ident.to_pos te) noattr
    | TFun tparams tret =>
        let tparams' := List.map (transl_typ2_rec LyBoxed) tparams in
        let tret' := transl_typ2_rec LyBoxed tret in
        tptr (Tfunction tparams' tret' cc_default)
    | TAbs t => tptr (PMap.get (Ident.to_pos t) abs_types_impl)
    end.

  Definition transl_typ2 (ty: typ2) : Ctypes.type :=
    transl_typ2_rec LyBoxed ty.

  Definition deref_pointer (ty: type) : Ctypes.type :=
    match ty with
    | Tpointer t _ => t
    | _ => ty
    end.

  Definition transl_typ2_fun (ty: typ2) : Ctypes.type :=
    match ty with
    | TFun _ _ => deref_pointer (transl_typ2 ty)
    | _ => transl_typ2 ty
    end.

  Definition transl_typ2_to_xtype (ty: typ2) : AST.xtype :=
    match ty with
    | TVoid => Xvoid
    | TBool => Xbool
    | TInt32 _ => Xint
    | TInt64 _ => Xlong
    | TEnum _ => Xint
    | TArray _ _
    | TRecord _
    | TFun _ _ 
    | TAbs _ => Xptr
    end.

  Definition transl_typ2_lit (ty: typ2) (n: Z) : Ctypes.type :=
    match ty with
    | TArray ta ly => Tarray (transl_typ2_rec ly ta) n noattr
    | TRecord t => Tstruct (Ident.to_pos t) noattr
    | _ => transl_typ2 ty
    end.

  Fixpoint transl_literal (l: Imp2.literal) : list AST.init_data :=
    match l with
    | LTrue => [Init_int32 Int.one]
    | LFalse => [Init_int32 Int.zero]
    | LInt32 i _ => [Init_int32 i]
    | LInt64 i _ => [Init_int64 i]
    | LVar x _ => [Init_addrof (Ident.to_pos x) Ptrofs.zero]
    | LArray a _ _ => List.concat (List.map transl_literal a)
    | LRecord rc _ _ => List.concat (List.map (fun '(_, lf) => transl_literal lf) rc)
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
    | BopOrbool => fail
    end.

  Fixpoint transl_atom (a: Imp2.atom) : res Csyntax.expr :=
    match a with
    | ATrue => ret (Eval Vtrue tbool)
    | AFalse => ret (Eval Vfalse tbool)
    | AInt32 i Signed => ret (Eval (Vint i) tint)
    | AInt32 i Unsigned => ret (Eval (Vint i) tuint)
    | AInt64 i Signed => ret (Eval (Vlong i) tlong)
    | AInt64 i Unsigned => ret (Eval (Vlong i) tulong)
    | AConstr x i ty => ret (Eval (Vint i) (transl_typ2 ty))
    | AVar x ty => ret (Evar (Ident.to_pos x) (transl_typ2 ty))
    | ACast a ty =>
        let* e := transl_atom a in
        ret (Ecast e (transl_typ2 ty))
    | AUnaryOp op a1 ty =>
        let* e := transl_atom a1 in
        let t := transl_typ2 ty in
        match transl_unary_op op with
        | OK op' => ret (Eunop op' e t)
        | Error _ => ret e
        end
    | ABinaryOp op a1 a2 ty =>
        let* e1 := transl_atom a1 in
        let* e2 := transl_atom a2 in
        let t := transl_typ2 ty in
        match op with
        | BopAndbool => ret (Eseqand e1 e2 tbool)
        | BopOrbool => ret (Eseqor e1 e2 tbool)
        | _ =>
            let* op' := transl_binary_op op in
            ret (Ebinop op' e1 e2 t)
        end
    | AArrayGet a1 a2 ly ty =>
        let* e1 := transl_atom a1 in
        let* e2 := transl_atom a2 in
        let tarith := typeof e1 in
        let tderef := transl_typ2_rec ly ty in
        let ederef := Ederef (Ebinop Oadd e1 e2 tarith) tderef in
        match ly with
        | LyBoxed
        | LyUnboxed (Some _)
        | LyPrim => ret ederef
        | LyUnboxed None => ret (Eaddrof ederef (tptr tderef))
        end
    | ARecordProj a f ly ty =>
        let* e := transl_atom a in
        let tderef := deref_pointer (typeof e) in
        let tfield := transl_typ2_rec ly ty in
        let efield := Efield (Ederef e tderef) (Ident.to_pos f) tfield in
        match ly, ty with
        | (LyBoxed | LyPrim), _ => ret efield
        | LyUnboxed _, TArray _ _ =>
            let tfield := transl_typ2 ty in
            ret (Efield (Ederef e tderef) (Ident.to_pos f) tfield)
        | LyUnboxed _, TRecord _ => ret (Eaddrof efield (tptr tfield))
        | _, _ => fail
        end
    | APureCall f tf args tr =>
        let* args' := mmap transl_atom args in
        let args' := List.fold_right (fun ei acc => Econs ei acc) Enil args' in
        let tr' := transl_typ2 tr in
        ret (Ecall (Evar (Ident.to_pos f) (transl_typ2_fun tf)) args' tr')
    end.

  (* Fixpoint transl_deep_access (globs: pset) (a: atom) (acs: list access) : res Csyntax.expr :=
    match acs with
    | nil => transl_atom globs a
    | ac :: nil =>
        match ac with
        | AcRecordField f ty ly =>
            let* e := transl_atom globs a in
            let tderef := deref_pointer (typeof e) in
            let tfield := transl_typ2_rec ly ty in
            ret (Efield (Ederef e tderef) (Ident.to_pos f) tfield)
        | AcArrayIndex ai ty ly =>
            let* e := transl_atom globs a in
            let* ei := transl_atom globs ai in
            let tarith := typeof e in
            let tderef := transl_typ2_rec ly ty in
            ret (Ederef (Ebinop Oadd e ei tarith) tderef)
        end
    | ac :: acs' =>
        match ac with
        | AcRecordField f ty ly =>
            let* er := transl_deep_access globs a acs' in
            let* er :=
              match typeof er with
              | Tpointer (Tstruct rid attr) _ =>
                  ret (Ederef er (Tstruct rid attr))
              | Tstruct rid attr => ret er
              | _ => fail
              end
            in
            let tfield := transl_typ2_rec ly ty in
            ret (Efield er (Ident.to_pos f) tfield)
        | AcArrayIndex ai ty ly =>
            let* er := transl_deep_access globs a acs' in
            let* ei := transl_atom globs ai in
            let tarith := typeof er in
            let tderef := transl_typ2_rec ly ty in
            ret (Ederef (Ebinop Oadd er ei tarith) tderef)
        end
    end. *)

  (* Definition transl_expr (globs: pset) (e: Imp2.expr) : res Csyntax.expr :=
    match e with
    | EAtom a _ => transl_atom globs a
    | EArrayGet a1 a2 ty ly =>
        let* e1 := transl_atom globs a1 in
        let* e2 := transl_atom globs a2 in
        let tarith := typeof e1 in
        let tderef := transl_typ2_rec ly ty in
        let ederef := Ederef (Ebinop Oadd e1 e2 tarith) tderef in
        match ly with
        | LyBoxed
        | LyUnboxed (Some _)
        | LyPrim => ret ederef
        | LyUnboxed None => ret (Eaddrof ederef (tptr tderef))
        end
    | ERecordProj a f ty ly =>
        let* e := transl_atom globs a in
        let tderef := deref_pointer (typeof e) in
        let tfield := transl_typ2_rec ly ty in
        let efield := Efield (Ederef e tderef) (Ident.to_pos f) tfield in
        match ly, ty with
        | (LyBoxed | LyPrim), _ => ret efield
        | LyUnboxed _, TArray _ _ =>
            let tfield := transl_typ2 ty in
            ret (Efield (Ederef e tderef) (Ident.to_pos f) tfield)
        | LyUnboxed _, TRecord _ => ret (Eaddrof efield (tptr tfield))
        | _, _ => fail
        end
    | EDeepAccess a acs _ => transl_deep_access globs a (List.rev' acs)
    end. *)

  Definition transl_ecomp (ec: Imp2.ecomp) : res Csyntax.statement :=
    match ec with
    | EcArraySet a1 a2 a3 =>
        let* e1 := transl_atom a1 in
        let* e2 := transl_atom a2 in
        let* e3 := transl_atom a3 in
        let tarith := typeof e1 in
        let tderef := typeof e3 in
        ret (Sdo (Eassign (Ederef (Ebinop Oadd e1 e2 tarith) tderef) e3 (typeof e3)))
    | EcRecordUpdate a1 f a2 =>
        let* e1 := transl_atom a1 in
        let* e2 := transl_atom a2 in
        let tderef := deref_pointer (typeof e1) in
        let tfield := typeof e2 in
        ret (Sdo (Eassign (Efield (Ederef e1 tderef) (Ident.to_pos f) tfield) e2 (typeof e2)))
    end.

  Fixpoint transl_statement (s: Imp2.statement) (tret: Ctypes.type): res Csyntax.statement :=
    let fix transl_switch_cases (ei: AST.ident) (cases: list (pattern * Imp2.statement)) : res Csyntax.labeled_statements :=
      match cases with
      | nil => fail
      | (p, sp) :: nil =>
          let* sp' := transl_statement sp tret in
          match p with
          | PIdent i z =>
              let default_retval :=
                match tret with
                | Tvoid => None
                | _ => Some (Eval (Vint Int.zero) tint)
                end
              in
              ret (LScons (Some z) (Ssequence sp' Sbreak)
                    (LScons None (Sreturn default_retval) LSnil))
          | PWildcard =>
              ret (LScons None sp' LSnil)
          end
      | (p, sp) :: ((_ :: _) as cases') =>
          match p with
          | PIdent i z =>
              let* sc' := transl_statement sp tret in
              let* ccases := transl_switch_cases ei cases' in
              ret (LScons (Some z) (Ssequence sc' Sbreak) ccases)
          | PWildcard => fail (* Ill-typed program *)
          end
      end
    in
    match s with
    | StSkip => ret Sskip
    | StSet x a =>
        let* e := transl_atom a in
        let te := typeof e in
        ret (Sdo (Eassign (Evar (Ident.to_pos x) te) e te))
    | StEcomp ec => transl_ecomp ec
    | StCall x f tf args ty =>
        let ty' := transl_typ2 ty in
        let* args' := mmap transl_atom args in
        let args' := List.fold_right (fun ei acc => Econs ei acc) Enil args' in
        let ecall := Ecall (Evar (Ident.to_pos f) (transl_typ2_fun tf)) args' ty' in
        match x with
        | Some x =>
            ret (Sdo (Eassign (Evar (Ident.to_pos x) ty') ecall ty'))
        | None => ret (Sdo ecall)
        end
    | StIfThenElse a s1 s2 =>
        let* e := transl_atom a in
        let* s1' := transl_statement s1 tret in
        let* s2' := transl_statement s2 tret in
        ret (Sifthenelse e s1' s2')
    | StSwitch a cases =>
        let* e := transl_atom a in
        match typeof e with
        | Tenum ei _ =>
            let* cases' := transl_switch_cases ei cases in
            ret (Sswitch e cases')
        | _ => fail
        end
    | StSequence s1 s2 =>
        let* s1' := transl_statement s1 tret in
        let* s2' := transl_statement s2 tret in
        ret (Ssequence s1' s2')
    | StReturn a =>
        match a with
        | Some a =>
            let* e := transl_atom a in
            ret (Sreturn (Some e))
        | None => ret (Sreturn None)
        end
    end.

  Definition transl_function (f: Imp2.function) : res Csyntax.function :=
    let ty := transl_typ2 (fn_return f) in
    let params := List.map (fun '(pid, pty) => (Ident.to_pos pid, transl_typ2 pty)) (fn_params f) in
    let vars := List.map (fun '(pid, pty) => (Ident.to_pos pid, transl_typ2 pty)) (fn_vars f) in
    let* body := transl_statement (fn_body f) ty in
    ret {|
      Csyntax.fn_return := ty;
      Csyntax.fn_callconv := cc_default;
      Csyntax.fn_params := params;
      Csyntax.fn_vars := vars;
      Csyntax.fn_body := body
    |}.

  Definition transl_abs_function (f: ident) (tparams: list (param_attr * typ2)) (tret: typ2) : Csyntax.fundef :=
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
    AST.ident * AST.globdef (Ctypes.fundef Csyntax.function) type.

  Definition literal_size (l: Imp2.literal) : Z :=
    match l with
    | Imp2.LArray a _ _ => Z.of_nat (Barray.length a)
    | _ => Z.of_nat 0
    end.

  Fixpoint transl_globdefs_rec (defs: list Imp2.globdef) : res (list cglobdef) :=
    match defs with
    | nil => ret nil
    | d :: defs' =>
        match d with
        | DefConst x l ty =>
            let init := transl_literal l in
            let t := transl_typ2_lit ty (literal_size l) in
            let (t, readonly) :=
              match ty, l with
              | TRecord _, LVar _ _ => (tptr t, true)
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
            let* r := transl_globdefs_rec defs' in
            ret (d :: r)
        | DefFun x f =>
            let* f' := transl_function f in
            let d := ((Ident.to_pos x), (Gfun (Internal f'))) in
            let* r := transl_globdefs_rec defs' in
            ret (d :: r)
        | DeclConst x ty =>
            let t := transl_typ2 ty in
            let* r := transl_globdefs_rec defs' in
            let d := ((Ident.to_pos x), Gvar {|
              gvar_info := t;
              gvar_init := nil;
              gvar_readonly := true;
              gvar_volatile := false
            |})
            in
            ret (d :: r)
        | DeclFun x tparams tret =>
            let* r := transl_globdefs_rec defs' in
            let d := ((Ident.to_pos x), Gfun (transl_abs_function x tparams tret)) in
            ret (d :: r)
      end
    end.

  Definition transl_globdefs (defs: list Imp2.globdef) : res (list cglobdef) :=
    transl_globdefs_rec defs.

  Definition transl_enum_typ2 (x: ident) (elems: list ident) : Ctypes.composite_definition :=
    Composite (Ident.to_pos x) Enum (List.map (fun e => Member_plain (Ident.to_pos e) tint) elems) noattr.
    
  Definition transl_record_fields (fields: smaplist (typ2 * layout)) : Ctypes.members :=
    MapList.fold_right
      (fun tid '(ty, ly) acc =>
        (Member_plain (Ident.to_pos tid) (transl_typ2_rec ly ty)) :: acc)
      nil
      fields.

  Definition transl_record_typ2 (x: ident) (fields: smaplist (typ2 * layout)) : Ctypes.composite_definition :=
    Composite (Ident.to_pos x) Struct (transl_record_fields fields) noattr.

  Definition transl_prog_types (types: smaplist (type_def (typ2 * layout))) : list Ctypes.composite_definition :=
    MapList.fold_right
      (fun tid td cds =>
        let cd :=
          match td with
          | TdEnum elems => transl_enum_typ2 tid elems
          | TdRecord fields => transl_record_typ2 tid fields
          end
        in
        cd :: cds)
      nil
      types.

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

Definition mk_abs_types_impl (tabs: smaplist struct_or_union) : PMap.t Ctypes.type :=
  MapList.fold_left
    (fun acc tid su =>
      let ptid := Ident.to_pos tid in
      let ct :=
        match su with
        | SU_struct => Tstruct ptid noattr
        | SU_union => Tunion ptid noattr
        end
      in
      PMap.set ptid ct acc)
    tabs
    (PMap.init Tvoid).

Definition transl_program (prog: Imp2.program) : res Csyntax.program :=
  let types := prog_types prog in
  let defs := prog_defs prog in
  let abs_types_impl := mk_abs_types_impl (prog_tabs prog) in
  let ts := transl_prog_types abs_types_impl types in
  let* cdefs := transl_globdefs abs_types_impl defs in
  let public := List.map Ident.to_pos (public_idents defs) in
  let main := _main in
  match Ctypes.make_program ts cdefs public main with
  | OK prog => OK prog
  | Error (MSG msg :: CTX id :: _) => failwith (String.append msg (string_of_ident id))
  | Error _ => failwith "Csyntaxgen.transl_program: error when calling Ctypes.make_program"
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

  Definition function_idents (f: Csyntax.function) : pset :=
    let param_idents :=
      List.fold_left
      (fun ids '(pid, pty) =>
        sunion (typ_idents pty) (sadd ids pid))
      (Csyntax.fn_params f)
      sempty
    in
    let var_idents :=
      List.fold_left
        (fun ids vid => sadd ids vid)
        (List.map fst (Csyntax.fn_vars f))
        sempty
    in
    sunion (sunion param_idents var_idents) var_idents.

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

  Definition program_idents (prog: Csyntax.program) : list AST.ident :=
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