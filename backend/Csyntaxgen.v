From Stdlib Require Import ZArith String List FMapPositive MSetPositive.
From compcert Require Import AST Ctypes Ctyping Csyntax Csyntaxdefs Values Cop Maps Integers.
From BarocqComp Require Import Ident Types Benum Res Maps2 Utils Syntax Imp2.
Import ListNotations.
Import CsyntaxNotations.

Local Open Scope error_monad_scope.
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
    | TRecord t _ =>
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
    | TActR _ => Tvoid (* this should not happen *)
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
    | TRecord _ _
    | TFun _ _ 
    | TAbs _ => Xptr
    | TActR _ => Xptr (* should not happen *)
    end.

  Definition transl_typ2_lit (ty: typ2) (n: Z) : Ctypes.type :=
    match ty with
    | TArray ta ly => Tarray (transl_typ2_rec ly ta) n noattr
    | TRecord t  _ => Tstruct (Ident.to_pos t) noattr
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
    | UopPlus => efail
    end.

  Definition transl_binary_op (op: Syntax.binary_op) : res Cop.binary_operation :=
    match op with
    | BopAndint => eret Oand
    | BopOrint => eret Oor
    | BopXorbool => eret One
    | BopXorint => eret Oxor
    | BopAdd => eret Oadd
    | BopSub => eret Osub
    | BopMul => eret Omul
    | BopDiv => eret Odiv
    | BopMod => eret Omod
    | BopShl => eret Oshl
    | BopShr => eret Oshr
    | BopEq => eret Oeq
    | BopNeq => eret One
    | BopLt => eret Olt
    | BopGt => eret Ogt
    | BopLe => eret Ole
    | BopGe => eret Oge
    | BopAndbool
    | BopOrbool => efail
    end.

  Fixpoint transl_atom (a: Imp2.atom) : res Csyntax.expr :=
    let fix transl_atom_rec (a: Imp2.atom) : res Csyntax.expr :=
      match a with
      | ATrue => eret (Eval Vtrue tbool)
      | AFalse => eret (Eval Vfalse tbool)
      | AInt32 i Signed => eret (Eval (Vint i) tint)
      | AInt32 i Unsigned => eret (Eval (Vint i) tuint)
      | AInt64 i Signed => eret (Eval (Vlong i) tlong)
      | AInt64 i Unsigned => eret (Eval (Vlong i) tulong)
      | AConstr x i ty => eret (Eval (Vint i) (transl_typ2 ty))
      | AVar x ty => eret (Evar (Ident.to_pos x) (transl_typ2 ty))
      | ACast a ty =>
          do e <- transl_atom a;
          eret (Ecast e (transl_typ2 ty))
      | AUnaryOp op a1 ty =>
          do e <- transl_atom a1;
          let t := transl_typ2 ty in
          match transl_unary_op op with
          | OK op' => eret (Eunop op' e t)
          | Error _ => eret e
          end
      | ABinaryOp op a1 a2 ty =>
          do e1 <- transl_atom a1;
          do e2 <- transl_atom a2;
          let t := transl_typ2 ty in
          match op with
          | BopAndbool => eret (Eseqand e1 e2 tbool)
          | BopOrbool => eret (Eseqor e1 e2 tbool)
          | _ =>
              do op' <- transl_binary_op op;
              eret (Ebinop op' e1 e2 t)
          end
      | AArrayGet a1 a2 ly ty =>
          do e1 <- transl_atom a1;
          do e2 <- transl_atom a2;
          let ty' := transl_typ2_rec ly ty in
          let eindex := Eindex e1 e2 ty' in
          match ly with
          | LyBoxed
          | LyUnboxed (Some _)
          | LyPrim => eret eindex
          | LyUnboxed None => eret (Ebinop Oadd e1 e2 ty')
          end
      | ARecordProj a f ly ty =>
          do e <- transl_atom a;
          let tderef := deref_pointer (typeof e) in
          let tfield := transl_typ2_rec ly ty in
          let efield := Efield (Evalof (Ederef e tderef) tderef) (Ident.to_pos f) tfield in
          match ly, ty with
          | (LyBoxed | LyPrim), _ => eret efield
          | LyUnboxed _, TArray _ _ =>
              let tfield := transl_typ2 ty in
              eret (Efield (Evalof (Ederef e tderef) tderef) (Ident.to_pos f) tfield)
          | LyUnboxed _, TRecord _ _ => eret (Eaddrof efield (tptr tfield))
          | _, _ => efail
          end
      | APureCall f tf args tr =>
          do args' <- mmap transl_atom args;
          let args' := List.fold_right (fun ei acc => Econs ei acc) Enil args' in
          let tr' := transl_typ2 tr in
          let tf' := transl_typ2_fun tf in
          eret (Ecall (Evalof (Evar (Ident.to_pos f) tf') tf') args' tr')
      end
    in
    do e <- transl_atom_rec a;
    match Ctyping.expr_kind e with
    | Csem.LV => eret (Evalof e (typeof e))
    | _ => eret e
    end.

  Definition transl_ecomp (ec: Imp2.ecomp) : res Csyntax.statement :=
    match ec with
    | EcArraySet a1 a2 a3 =>
        match Imp2.typof_atom a1 with
        | TArray ((TRecord _ _| TArray _ _)) (LyUnboxed _) => efail
        | _ =>
            do e1 <- transl_atom a1;
            do e2 <- transl_atom a2;
            do e3 <- transl_atom a3;
            eret (Sdo (Eassign (Eindex e1 e2 (typeof e3)) e3 (typeof e3)))
        end
    | EcRecordUpdate a1 f a2 =>
        match Imp2.typof_atom a1 with
        | TRecord rid ub =>
            if list_mem Ident.eq_dec f ub then efail
            else
              do e1 <- transl_atom a1;
              do e2 <- transl_atom a2;
              let tderef := deref_pointer (typeof e1) in
              let tfield := typeof e2 in
              eret (Sdo (Eassign (Efield (Evalof (Ederef e1 tderef) tderef) (Ident.to_pos f) tfield) e2 (typeof e2)))
        | _ => efail
        end
    end.

  Fixpoint transl_statement (s: Imp2.statement): res Csyntax.statement :=
    let fix transl_switch_cases (cases: list (pattern * Imp2.statement)) : res Csyntax.labeled_statements :=
      match cases with
      | nil => efail
      | (p, sp) :: nil =>
          do sp' <- transl_statement sp;
          match p with
          | PIdent i z =>
              eret (LScons (Some z) (Ssequence sp' Sbreak) LSnil)
          | PWildcard =>
              eret (LScons None sp' LSnil)
          end
      | (p, sp) :: ((_ :: _) as cases') =>
          match p with
          | PIdent i z =>
              do sc' <- transl_statement sp;
              do ccases <- transl_switch_cases cases';
              eret (LScons (Some z) (Ssequence sc' Sbreak) ccases)
          | PWildcard => efail (* Ill-typed program *)
          end
      end
    in
    match s with
    | StSkip => eret Sskip
    | StSet x a =>
        do e <- transl_atom a;
        let te := typeof e in
        eret (Sdo (Eassign (Evar (Ident.to_pos x) te) e te))
    | StEcomp ec => transl_ecomp ec
    | StCall x f tf args tr =>
        do args' <- mmap transl_atom args;
        let args' := List.fold_right (fun ei acc => Econs ei acc) Enil args' in
        let tr' := transl_typ2 tr in
        let tf' := transl_typ2_fun tf in
        let ecall := Ecall (Evalof (Evar (Ident.to_pos f) tf') tf') args' tr' in
        match x with
        | Some x => eret (Sdo (Eassign (Evar (Ident.to_pos x) tr') ecall tr'))
        | None => eret (Sdo ecall)
        end
    | StIfThenElse a s1 s2 =>
        do e <- transl_atom a;
        do s1' <- transl_statement s1;
        do s2' <- transl_statement s2;
        eret (Sifthenelse e s1' s2')
    | StWhile cond _ body =>
        do cond' <- transl_atom cond;
        do body' <- transl_statement body;
        OK (Swhile cond' body')
    | StSwitch a cases =>
        do e <- transl_atom a;
        match typeof e with
        | Tenum ei _ =>
            do cases' <- transl_switch_cases cases;
            eret (Sswitch e cases')
        | _ => efail
        end
    | StSequence s1 s2 =>
        do s1' <- transl_statement s1;
        do s2' <- transl_statement s2;
        eret (Ssequence s1' s2')
    | StReturn a =>
        match a with
        | Some a =>
            do e <- transl_atom a;
            eret (Sreturn (Some e))
        | None => eret (Sreturn None)
        end
    end.

  Fixpoint all_locals (s: Imp2.statement) : smaplist typ2 :=
    match s with
    | Imp2.StSkip
    | Imp2.StReturn _
    | Imp2.StEcomp _
    | Imp2.StCall None _ _ _ _ => MapList.empty
    | Imp2.StCall (Some x) _ _ _ ty => MapList.add Ident.eq_dec x ty MapList.empty 
    | Imp2.StSet x a => MapList.add Ident.eq_dec x (typof_atom a) MapList.empty
    | Imp2.StIfThenElse _ s1 s2
    | Imp2.StSequence s1 s2 => MapList.merge Ident.eq_dec (all_locals s1) (all_locals s2)
    | Imp2.StWhile cond _ body => all_locals body
    | Imp2.StSwitch _ cases =>
        MapList.fold_left
          (fun acc _ si => MapList.merge Ident.eq_dec (all_locals si) acc)
          cases
          MapList.empty
      
    end.

  Definition transl_function (f: Imp2.function) : res Csyntax.function :=
    let ty := transl_typ2 (fn_return f) in
    let params := List.map (fun '(pid, pty) => (Ident.to_pos pid, transl_typ2 pty)) (fn_params f) in
    let vars := List.map (fun '(pid, pty) => (Ident.to_pos pid, transl_typ2 pty)) (all_locals (fn_body f)) in
    do body <- transl_statement (fn_body f);
    eret {|
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
    | Imp2.LArray a _ _ => Barray.Zlength a
    | _ => Z.of_nat 0
    end.

  Fixpoint transl_globdefs_rec (defs: list Imp2.globdef) : res (list cglobdef) :=
    match defs with
    | nil => eret nil
    | d :: defs' =>
        match d with
        | DefConst x l ty =>
            let init := transl_literal l in
            let t := transl_typ2_lit ty (literal_size l) in
            let (t, readonly) :=
              match ty, l with
              | TRecord _ _, LVar _ _ => (tptr t, true)
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
            do r <- transl_globdefs_rec defs';
            eret (d :: r)
        | DefFun x f =>
            do f' <- transl_function f;
            let d := ((Ident.to_pos x), (Gfun (Internal f'))) in
            do r <- transl_globdefs_rec defs';
            eret (d :: r)
        | DeclConst x ty =>
            let t := transl_typ2 ty in
            do r <- transl_globdefs_rec defs';
            let d := ((Ident.to_pos x), Gvar {|
              gvar_info := t;
              gvar_init := nil;
              gvar_readonly := true;
              gvar_volatile := false
            |})
            in
            eret (d :: r)
        | DeclFun x tparams tret =>
            do r <- transl_globdefs_rec defs';
            let d := ((Ident.to_pos x), Gfun (transl_abs_function x tparams tret)) in
            eret (d :: r)
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
  do cdefs <- transl_globdefs abs_types_impl defs;
  let public := List.map Ident.to_pos (public_idents defs) in
  let main := _main in
  match Ctypes.make_program ts cdefs public main with
  | Errors.OK prog =>
      match Ctyping.typecheck_program prog with
      | _ => eret prog (* TODO: implement enum types in Csyntax *)
      end
  | Errors.Error (Errors.MSG msg :: Errors.CTX id :: _) => efailwith (String.append msg (string_of_ident id))
  | Errors.Error _ => efailwith "Csyntaxgen.transl_program: error when calling Ctypes.make_program"
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

Section GLOB_ARRAYS.

  Definition is_glob_array (g: AST.globdef (Ctypes.fundef Csyntax.function) type) : bool :=
    match g with
    | Gvar gv =>
        match gvar_info gv with
        | Tarray _ _ _ => true
        | _ => false
        end
    | _ => false
    end.

  Definition program_glob_arrays (prog: Csyntax.program) : list AST.ident :=
    List.fold_left
      (fun acc '(x, g) => if is_glob_array g then x :: acc else acc)
      (Ctypes.prog_defs prog)
      nil.

End GLOB_ARRAYS.
