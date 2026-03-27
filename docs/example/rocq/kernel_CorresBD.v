From Coq Require Import String.
From compcert Require Import Integers.
From BarocqComp Require Import Target StateMonads Option Barray Brecord Types Barocq.
From BarocqComp Require Import CorresBD_Tactics.
From kernel Require Import kernel_Types kernel_ShallowB kernel_Deep kernel_CorresBD_Prelude kernel_CorresBD_Proof.

Open Scope string_scope.

(** * Program correspondence theorems *)

Definition eval_def := BarocqBNF.eval_def2 Ptr64 abs_types_impl abs_defs_impl kernel_Deep.prog.

Ltac BD :=
destruct eval_prog_spec as (te & ge & EVAL & ALL);
let h := fresh "HASP" in
ltac2:(has_property ident:(HASP) @ge constr:(abs_types_impl));[ 
(eapply BarocqBNFVC.has_property_find_err; eauto) |
apply BarocqBNFVC.has_property_equal with (1:= EVAL) in h;[apply h|reflexivity]
].


Theorem fun_Machine_write_timecmp_corres :
  exists Machine_write_timecmp_val,
  eval_def "Machine_write_timecmp" = Some (VAL Deeptypes.typof_Machine_write_timecmp Machine_write_timecmp_val) /\
  (forall (a0: Machine_state) (a1: int64),
   Machine_write_timecmp_val a0 a1 =
   kernel_ShallowB.Machine_write_timecmp a0 a1).
Proof. BD. Qed.

Theorem const_Kernel_nb_procs_corres :
  eval_def "Kernel_nb_procs" = Some (VAL Deeptypes.typof_Kernel_nb_procs kernel_ShallowB.Kernel_nb_procs).
Proof.
  reflexivity.
Qed.

Theorem const_Kernel_quantum_corres :
  eval_def "Kernel_quantum" = Some (VAL Deeptypes.typof_Kernel_quantum kernel_ShallowB.Kernel_quantum).
Proof.
  reflexivity.
Qed.

Theorem fun_Kernel_update_proc_status_corres :
  exists Kernel_update_proc_status_val,
  eval_def "Kernel_update_proc_status" = Some (VAL Deeptypes.typof_Kernel_update_proc_status Kernel_update_proc_status_val) /\
  (forall (p_ks: Kernel_state) (p_pid: int64) (p_status: Kernel_proc_status),
   Kernel_update_proc_status_val p_ks p_pid p_status =
   kernel_ShallowB.Kernel_update_proc_status p_ks p_pid p_status).
Proof. BD. Qed.

Theorem fun_Kernel_schedule_corres :
  exists Kernel_schedule_val,
  eval_def "Kernel_schedule" = Some (VAL Deeptypes.typof_Kernel_schedule Kernel_schedule_val) /\
  (forall (p_ks: Kernel_state) (p_now: int64),
   Kernel_schedule_val p_ks p_now =
   kernel_ShallowB.Kernel_schedule p_ks p_now).
Proof. BD. Qed.
