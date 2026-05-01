From kernel Require Import  kernel_Types kernel_ShallowB kernel_Deep kernel_CorresBD_Prelude.
From compcert Require Import Integers Coqlib.
From BarocqComp Require Import Utils StateMonads ExtEqual Option Denot Barray Brecord Types BarocqBNF BarocqBNFVC Maps2.
From Stdlib Require Import String List Lia.
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
      let v  := eval_fun ?A ?ABS ?TE ge ?P ?R
                  (Syntax.fn_body ?F) in
      eq_value ?ABS (VAL ?TY ?G) ?DTYP v
    => let L1 := (eval unfold L in L) in
       cbv beta delta [F TY G L P R Syntax.fn_body eval_fun];
       gen_list L1; intro ge ; compute in ge;
       unfold eq_value; apply same_value_refl';[reflexivity | (compute; reflexivity)]
  | |- _ => unfold eq_value; apply same_value_refl';[reflexivity | reflexivity]
  end.


Ltac has_property_FFI :=
  unfold has_property; eexists; split;
  [reflexivity |
    unfold snd;
    apply same_value_refl; reflexivity].

Opaque Benum.enum_eq_dec.
Opaque Benum.ematch_with.
Opaque Benum.of_Z.
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

Theorem eval_prog_spec : exists te ge, eval_prog abs_types_impl abs_defs_impl kernel_Deep.prog = Some (te, ge) /\
                                      Forall (has_property abs_types_impl ge) prop_list.
Proof.
  (* Prove that we can prove all the properties of the definitions
     assuming the properties of the declarations in the typing environment*)
  assert (EX : exists  (ge : genv abs_types_impl),
    eval_prog_rec abs_types_impl typing_env abs_defs_impl STree.empty prog_defs = Some ge /\
      Forall (has_property abs_types_impl ge) prop_list).
  {
    assert (GO :generate_obligations abs_types_impl typing_env abs_defs_impl nil nil prog_defs
                  prop_list = Some vc).
    {
      reflexivity.
    }
    apply generate_obligations_sound  with  (vc:=nil) (checked:=nil) (ol:=vc); auto.
    { apply nodup_NoDup.
      reflexivity.
    }
    - (* discharge all the proof obligations *)
      apply (Forall_app_sound _ vc).
      all: time vc.
    - apply wf_env_empty.
  }
  apply eval_prog_has_property with (gds:= prog_defs) (te:= typing_env); auto.
Time Qed.
