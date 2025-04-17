From Coq Require Import ZArith String List FMapPositive.
From compcert Require Import AST Ctypes Clight Clightdefs Cop Maps Integers.
From BarocqComp Require Import Error MapList Utils Types Syntax.
Import ClightNotations.
Import Syntax.Typed.
From BarocqComp Require Import Imp2.

Local Open Scope clight_scope.
Local Open Scope string_scope.

Fixpoint transl_ctyp (ty: ctyp) : Ctypes.type :=
  match ty with
  | CBool => tbool
  | CInt32 Signed => tint
  | CInt32 Unsigned => tuint
  | CInt64 Signed => tlong
  | CInt64 Unsigned => tulong
  | CArray ta => tptr (transl_ctyp ta)
  | CStruct t => tptr (Tstruct t noattr)
  | CFun tparams tret =>
      let tparams' := map transl_ctyp tparams in
      let tret' := transl_ctyp tret in
      tptr (Tfunction tparams' tret' cc_default) 
  end.

Definition transl_ctyp_lit (ty: ctyp) (n: Z) : Ctypes.type :=
  match ty with
  | CArray ta => Tarray (transl_ctyp ta) n noattr
  | CStruct t => Tstruct t noattr
  | _ => transl_ctyp ty
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
  | Imp2.LStruct st _ => map (fun '(_, lx) => transl_literal_base lx) st
  end.

Definition transl_unary_op (op: Syntax.unary_op) : Cop.unary_operation :=
  match op with
  | UopNotbool => Onotbool
  | UopNotint => Onotint
  | UopNeg => Oneg
  end.

Definition transl_binary_op (op: Syntax.binary_op) : Cop.binary_operation :=
  match op with
  | BopAndbool
  | BopAndint => Oand
  | BopOrbool
  | BopOrint => Oor
  | BopXorbool
  | BopXorint => Oxor
  | BopAdd => Oadd
  | BopSub => Osub
  | BopMul => Omul
  | BopDiv => Odiv
  | BopMod => Omod
  | BopShl => Oshl
  | BopShr => Oshr
  | BopEq => Oeq
  | BopNeq => One
  | BopLt => Olt
  | BopGt => Ogt
  | BopLe => Ole
  | BopGe => Oge
  end.

Fixpoint transl_atom (globs: pset) (a: Syntax.Typed.atom) : Clight.expr :=
  match a with
  | ATrue _ => Econst_int Int.one tbool
  | AFalse _ => Econst_int Int.zero tbool
  | AInt32 i _ => Econst_int i tint
  | AInt64 i _ => Econst_long i tlong
  | AVar x ty =>
      if smem globs x then Evar x (transl_ctyp ty)
      else Etempvar x (transl_ctyp ty)
  | AUnaryOp op a1 ty =>
      let e := transl_atom globs a1 in
      let t := transl_ctyp ty in
      let op' := transl_unary_op op in
      Eunop op' e t
  | ABinaryOp op a1 a2 ty =>
      let e1 := transl_atom globs a1 in
      let e2 := transl_atom globs a2 in
      let t := transl_ctyp ty in
      let op' := transl_binary_op op in
      Ebinop op' e1 e2 t
  end.

Definition deref_pointer (ty: type) : type :=
  match ty with
  | Tpointer t _ => t
  | _ => ty
  end.

Fixpoint transl_deep_access (globs: pset) (a: atom) (acs: list access) : Clight.expr :=
  match acs with
  | nil => transl_atom globs a
  | ac :: nil =>
      match ac with
      | AcStructField f ty =>
          let e := transl_atom globs a in
          let tderef := deref_pointer (typeof e) in
          let tfield := transl_ctyp ty in
          Efield (Ederef e tderef) f tfield
      | AcArrayIndex ai ty =>
          let e := transl_atom globs a in
          let ei := transl_atom globs ai in
          let tarith := typeof e in
          let tderef := transl_ctyp ty in
          Ederef (Ebinop Oadd e ei tarith) tderef
      end
  | ac :: acs' =>
      match ac with
      | AcStructField f ty =>
        let er := transl_deep_access globs a acs' in
        let tderef := deref_pointer (typeof er) in
        let tfield := transl_ctyp ty in
        Efield (Ederef er tderef) f tfield     
      | AcArrayIndex ai ty =>
          let er := transl_deep_access globs a acs' in
          let ei := transl_atom globs ai in
          let tarith := typeof er in
          let tderef := transl_ctyp ty in
          Ederef (Ebinop Oadd er ei tarith) tderef
      end
  end.

Definition transl_expr (globs: pset) (e: Imp2.expr) : Clight.expr :=
  match e with
  | EAtom a _ => transl_atom globs a
  | EArrayGet a1 a2 ty =>
      let e1 := transl_atom globs a1 in
      let e2 := transl_atom globs a2 in
      let tarith := typeof e1 in
      let tderef := transl_ctyp ty in
      Ederef (Ebinop Oadd e1 e2 tarith) tderef
  | EStructProj a f ty =>
      let e := transl_atom globs a in
      let tderef := deref_pointer (typeof e) in
      let tfield := transl_ctyp ty in
      Efield (Ederef e tderef) f tfield
  | EDeepAccess a acs _ => transl_deep_access globs a (List.rev' acs)
  end.

Definition transl_ecomp (globs: pset) (ec: Imp2.ecomp) : Clight.expr * Clight.statement :=
  match ec with
  | EcArraySet a1 a2 a3 =>
      let e1 := transl_atom globs a1 in
      let e2 := transl_atom globs a2 in
      let e3 := transl_atom globs a3 in
      let tarith := typeof e1 in
      let tderef := typeof e3 in
      (e1, Sassign (Ederef (Ebinop Oadd e1 e2 tarith) tderef) e3)
  | EcStructUpdate a1 f a2 =>
      let e1 := transl_atom globs a1 in
      let e2 := transl_atom globs a2 in
      let tderef := deref_pointer (typeof e1) in
      let tfield := typeof e2 in
      (e1, Sassign (Efield (Ederef e1 tderef) f tfield) e2)
  end.

Fixpoint transl_statement (globs: pset) (s: Imp2.statement) : Clight.statement :=
  match s with
  | StSkip => Sskip
  | StSetExpr x e =>
      let e' := transl_expr globs e in
      Sset x e'
  | StSetEcomp x ec =>
      let (e, s) := transl_ecomp globs ec in
      let sset := Sset x e in
      Ssequence s sset
  | StCall x a args =>
      let e := transl_atom globs a in
      let args' := map (transl_atom globs) args in
      Scall (Some x) e args'
  | StIfThenElse a s1 s2 =>
      let e := transl_atom globs a in
      let s1' := transl_statement globs s1 in
      let s2' := transl_statement globs s2 in
      Sifthenelse e s1' s2'
  | StSequence s1 s2 =>
      let s1' := transl_statement globs s1 in
      let s2' := transl_statement globs s2 in
      Ssequence s1' s2'
  | StReturn a =>
      let e := transl_atom globs a in
      Sreturn (Some e)
  end.

Definition transl_function (globs: pset) (f: Imp2.function) : Clight.function :=
  let ty := transl_ctyp (fn_return f) in
  let params := map_k transl_ctyp (fn_params f) in
  let temps := map_k transl_ctyp (fn_vars f) in
  let body := transl_statement globs (fn_body f) in
  {|
    Clight.fn_return := ty;
    Clight.fn_callconv := cc_default;
    Clight.fn_params := params;
    Clight.fn_vars := nil;
    Clight.fn_temps := temps;
    Clight.fn_body := body
  |}.

Definition cglobdef : Type :=
  AST.ident * AST.globdef (Ctypes.fundef Clight.function) type.

Definition literal_size (l: Imp2.literal) : Z :=
  match l with
  | Imp2.LArray a _ => Z.of_nat (Array.length a)
  | _ => Z.of_nat 0
  end.

Fixpoint transl_globdefs_rec (defs: list Imp2.globdef) (globs: pset): list cglobdef :=
  match defs with
  | nil => nil
  | DefConst x l ty :: defs' =>
      let init := transl_literal l in
      let t := transl_ctyp_lit ty (literal_size l) in
      let t :=
        match ty, l with
        | CStruct _, LBase (LbVar _) _ => tptr t
        | _, _ => t
        end
      in
      let d := (x, Gvar {|
        gvar_info := t;
        gvar_init := init;
        gvar_readonly := false;
        gvar_volatile := false
      |}) in
      d :: (transl_globdefs_rec defs' (sadd globs x))
  | DefFun x f :: defs'=>
      let f' := transl_function globs f in
      let d := (x, (Gfun (Internal f'))) in
      d :: (transl_globdefs_rec defs' (sadd globs x))
  end.

Definition transl_globdefs (defs: list Imp2.globdef) : list cglobdef :=
  transl_globdefs_rec defs sempty.

Fixpoint transl_struct_fields (fields: list (ident * ctyp)) : Ctypes.members :=
  match fields with
  | nil => nil
  | (x, tx) :: fields' =>
      let tx' := transl_ctyp tx in
      let r := transl_struct_fields fields' in
      (Member_plain x tx') :: r
  end.

Definition transl_struct_ctyp (x: ident) (fields: list (ident * ctyp)) : Ctypes.composite_definition :=
  Composite x Struct (transl_struct_fields fields) noattr.

Definition transl_prog_types (ts: types) : list Ctypes.composite_definition :=
  map (fun '(x, tx) => transl_struct_ctyp x tx) (PTree.elements ts).

Fixpoint public_idents (defs: list Imp2.globdef) : list ident :=
  match defs with
  | nil => nil
  | d :: defs' =>
      match d with
      | DefConst _ _ _ => nil
      | DefFun f _ => f :: (public_idents defs')
      end
  end.

Definition _main : ident := $"main".

Close Scope string_scope.

Definition f_main : Clight.function := {|
  Clight.fn_return := tint;
  Clight.fn_callconv := cc_default;
  Clight.fn_params := nil;
  Clight.fn_vars := nil;
  Clight.fn_temps := nil;
  Clight.fn_body :=
    (Ssequence
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition globdef_main : cglobdef := (_main, (Gfun (Internal f_main))).

Definition transl_program (prog: Imp2.program) : res Clight.program :=
  let ts := transl_prog_types (prog_types prog) in
  let defs := (transl_globdefs (prog_defs prog)) ++ (globdef_main :: nil) in
  let public := public_idents (prog_defs prog) in
  let main := _main in
  match Ctypes.make_program ts defs public main with
  | OK prog => OK prog
  | Error _ => failwith "Clightgen.transl_program: error when calling Ctypes.make_program"
  end.

Section IDENTS.

  Definition function_idents (f: Clight.function) : list ident :=
    (map fst (Clight.fn_params f))
    ++ (map fst (Clight.fn_vars f))
    ++ (map fst (Clight.fn_temps f)).

  Definition globdef_idents (def: cglobdef) : list ident :=
    let '(x, def) := def in
    match def with
    | Gfun (Internal f) => x :: (function_idents f)
    | _ => x :: nil
    end.

  Fixpoint members_idents (m: Ctypes.members) : list ident :=
    match m with
    | nil => nil
    | h :: t => name_member h :: (members_idents t)
    end.

  Definition composite_idents (cd: Ctypes.composite_definition) : list ident :=
    match cd with Composite x _ m _ => x :: (members_idents m) end.

  Definition program_idents (prog: Clight.program) : list ident :=
    let globdefs_idents := List.concat (map globdef_idents (Ctypes.prog_defs prog)) in
    let types_idents := List.concat (map composite_idents (Ctypes.prog_types prog)) in
    globdefs_idents ++ types_idents. 

End IDENTS.