$MODULES
From Coq Require Import String List Lia.
From compcert Require Import Integers Coqlib.
From BarocqComp Require Import Target Utils Monads Error Barray Brecord Types Barocq BarocqVC Maps2.
Import Typed.
Open Scope list_scope.

Ltac gen_list L :=
  match L with
  | nil => idtac
  | (_,VAL _ ?F) :: ?L1 =>
      let vr := fresh "f"in
      generalize F as vr ; intro; gen_list L1
  end.

Ltac vc :=
  match goal with
  | |- @check_value  _ _ _ _ => reflexivity
  | |-
      let ge := genv_has_property ?ABS ?ENV ?L in
      let v  := build_funval ?A ?ABS ?TE ge ?P ?R
                  (Syntax.fn_body ?F) in
      eq_value ?ABS (VAL ?TY ?G) ?DTYP v
    => let L1 := (eval unfold L in L) in
       cbv beta delta [F TY G L P R Syntax.fn_body build_funval];
       gen_list L1; intro ge ; compute in ge;
       unfold eq_value; apply same_value_refl';[reflexivity | (compute; reflexivity)]
  end.


Definition is_ktype (d:Typed.globdef) :=
  match kind_of_globdef d with
  | KindType => true
  | _    => false
  end.

Ltac has_property_FFI :=
  unfold has_property; eexists; split;
  [reflexivity |
    unfold snd;
    apply same_value_refl; reflexivity].

Opaque Benum.enum_eq_dec.
Opaque Benum.match_with_err.
Opaque Benum.of_i32.
Opaque Int.add Int64.add.
Opaque Int.sub Int64.sub.
Opaque Int.mul Int64.mul.
Opaque Intop.I32.div Intop.U32.div Intop.I64.div Intop.U64.div.
Opaque Intop.I32.mod Intop.U32.mod Intop.I64.mod Intop.U64.mod.
Opaque Int.and Int64.and.
Opaque Int.or Int64.or.
Opaque Int.xor Int64.xor.
Opaque Int.shl Int64.shl.
Opaque Int.shr Int.shru Int64.shr Int64.shru.
Opaque Int.eq Int64.eq.
Opaque Int.lt Int.ltu Int64.lt Int64.ltu.
Opaque Int.cmp Int.cmpu Int64.cmp Int64.cmpu.
Opaque Intop.I32.of_u64.
Opaque Intop.U64.of_i32.

Theorem eval_prog_spec : exists te ge, eval_prog $ARCH abs_types_impl abs_defs_impl $PROG = OK (te, ge) /\
                                      Forall (has_property abs_types_impl ge) (List.app decl_prop def_prop).
Proof.
  (** Proof of abs_types_impl *)
  assert (partition is_ktype prog = (prog_types, (prog_decls ++ prog_defs))).
  { reflexivity.
  }
  assert (PART2: partition_props abs_types_impl (prog_decls ++ prog_defs) (List.app decl_prop def_prop) = OK(decl_prop,def_prop)).
  { reflexivity.
  }
  (* Let prove that the initial environment verifies all the properties [decl_prop].
     This is a manual proof...
   *)
  assert (Forall (has_property  abs_types_impl abs_defs_impl) decl_prop).
  {
    apply (Forall_app_sound _ decl_prop).
    all:has_property_FFI.
  }
  (* Prove that we can prove all the properties of the definitions
     assuming the properties of the declarations in the typing environment*)
  assert (EX : exists (te': Typing.tenv) (ge : genv abs_types_impl),
    eval_prog_rec $ARCH abs_types_impl typing_env abs_defs_impl prog_defs = OK (te', ge) /\
      Forall (has_property abs_types_impl ge) def_prop).
  {
    assert (GO :generate_obligations abs_types_impl $ARCH typing_env decl_prop nil prog_defs def_prop = OK vc).
    {
      reflexivity.
    }
    apply generate_obligations_sound  with (ge:=abs_defs_impl) (vc:=nil) (checked:=decl_prop) (ol:=vc); auto.
    { apply nodup_NoDup.
      reflexivity.
    }
    - (* discharge all the proof obligations *)
      apply (Forall_app_sound _ vc).
      all: time vc.
    - unfold wf_env.
      rewrite <- Forall_forall.
      apply (Forall_app_sound _ prog_defs).
      all:reflexivity.
  }
  destruct EX as (te' & ge & EVAL & ALL).
  exists te'. exists ge.
  rewrite prog_decomp.
  unfold eval_prog.
  split.
  rewrite List.app_assoc.
  apply eval_prog_rec_app with (te1:=typing_env) (ge1:= abs_defs_impl) ; eauto.
  eapply eval_prog_rec_preserve_app_properties;eauto.
Time Qed.
