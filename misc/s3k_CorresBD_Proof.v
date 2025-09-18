From Coq Require Import String List Lia.
From compcert Require Import Integers Coqlib.
From BarocqComp Require Import Target Utils Monads Error Barray Brecord Types Barocq BarocqVC Maps2.
From s3k Require Import s3k_Types s3k_ShallowB s3k_Deep s3k_CorresBD_Prelude.
Import Typed.
Open Scope list_scope.

Ltac ext_equal_equal :=
  match goal with
  | H : ext_equal ?A ?T1 ?V1 ?V2 |- _ =>
      apply no_TFun_equal in H;[|reflexivity]
end.


Ltac eq_value :=
  unfold eq_value, VAL;
  apply ext_equal_same_value;
  match goal with
  | |- ext_equal ?A ?T ?V1 ?V2 =>
      unfold T;
      match goal with
      | |- ext_equal ?A ?T ?V1 ?V2 =>
          match T with
          | TFun nil ?RET =>
              change (forall (x:unit), ext_equal (V1 x) (V2 x))
          | TFun  ?L ?RET =>
              change (ext_fun A (ext_equal A) RET L V1 V2);
              unfold ext_fun;intros;
              repeat ext_equal_equal; subst
          | _  => idtac
          end
      end
  end.

Ltac vc :=
  (split;reflexivity) (* for litterals *)
  ||
  (eq_value; apply res_rel_ext_equal_eq;reflexivity) (* for functions *)
.


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

Opaque project.
Opaque Benum.enum_eq_dec.
Opaque upd.



Theorem eval_prog_spec : exists te ge, eval_prog Ptr64 abs_types_impl abs_defs_impl s3k_Deep.prog = OK (te, ge) /\
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
    eval_prog_rec Ptr64 abs_types_impl typing_env abs_defs_impl prog_defs = OK (te', ge) /\
      Forall (has_property abs_types_impl ge) def_prop).
  {
    assert (GO :generate_obligations abs_types_impl Ptr64 typing_env decl_prop nil prog_defs def_prop = OK vc).
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
