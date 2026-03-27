From Coq Require Import String.
From compcert Require Import Integers.
From BarocqComp Require Import Target StateMonads Option Barray Brecord Types Barocq.
From kernel Require Import kernel_Types kernel_ShallowR kernel_Deep kernel_CorresBD_Prelude.
From kernel Require kernel_CorresRB kernel_CorresBD.

Open Scope option_monad_scope.
Open Scope string_scope.

(** * Program correspondence theorems *)

Definition eval_def := kernel_CorresBD.eval_def.

Theorem fun_Machine_write_timecmp_corres :
  exists Machine_write_timecmp_val,
  eval_def "Machine_write_timecmp" = Some (VAL Deeptypes.typof_Machine_write_timecmp Machine_write_timecmp_val) /\
  (forall (a0: Machine_state) (a1: int64),
   Machine_write_timecmp_val a0 a1 =
   kernel_ShallowR.Machine_write_timecmp a0 a1).
Proof.
  pose proof kernel_CorresBD.fun_Machine_write_timecmp_corres as [Machine_write_timecmp_val [Heval HcorresBD]].
  exists Machine_write_timecmp_val. split.
  - exact Heval.
  - intros. specialize (HcorresBD a0 a1).
    rewrite HcorresBD. rewrite kernel_CorresRB.fun_Machine_write_timecmp_corres.
    reflexivity.
Qed.

Theorem const_Kernel_nb_procs_corres :
  eval_def "Kernel_nb_procs" = Some (VAL Deeptypes.typof_Kernel_nb_procs (kernel_ShallowR.Kernel_nb_procs)).
Proof.
  reflexivity.
Qed.

Theorem const_Kernel_quantum_corres :
  eval_def "Kernel_quantum" = Some (VAL Deeptypes.typof_Kernel_quantum (kernel_ShallowR.Kernel_quantum)).
Proof.
  reflexivity.
Qed.

Theorem fun_Kernel_update_proc_status_corres :
  exists Kernel_update_proc_status_val,
  eval_def "Kernel_update_proc_status" = Some (VAL Deeptypes.typof_Kernel_update_proc_status Kernel_update_proc_status_val) /\
  (forall (ks: Kernel_state) (pid: int64) (status: Kernel_proc_status),
   Kernel_update_proc_status_val (rconv_Kernel_state_RtoB ks) pid (econv_Kernel_proc_status_RtoB status) =
   let* r := kernel_ShallowR.Kernel_update_proc_status ks pid status in
   Some (rconv_Kernel_state_RtoB r)).
Proof.
  pose proof kernel_CorresBD.fun_Kernel_update_proc_status_corres as [Kernel_update_proc_status_val [Heval HcorresBD]].
  exists Kernel_update_proc_status_val. split.
  - exact Heval.
  - intros. specialize (HcorresBD (rconv_Kernel_state_RtoB ks) pid (econv_Kernel_proc_status_RtoB status)).
    rewrite HcorresBD. rewrite kernel_CorresRB.fun_Kernel_update_proc_status_corres.
    reflexivity.
Qed.

Theorem fun_Kernel_schedule_corres :
  exists Kernel_schedule_val,
  eval_def "Kernel_schedule" = Some (VAL Deeptypes.typof_Kernel_schedule Kernel_schedule_val) /\
  (forall (ks: Kernel_state) (now: int64),
   Kernel_schedule_val (rconv_Kernel_state_RtoB ks) now =
   let* r := kernel_ShallowR.Kernel_schedule ks now in
   Some (rconv_Kernel_state_RtoB r)).
Proof.
  pose proof kernel_CorresBD.fun_Kernel_schedule_corres as [Kernel_schedule_val [Heval HcorresBD]].
  exists Kernel_schedule_val. split.
  - exact Heval.
  - intros. specialize (HcorresBD (rconv_Kernel_state_RtoB ks) now).
    rewrite HcorresBD. rewrite kernel_CorresRB.fun_Kernel_schedule_corres.
    reflexivity.
Qed.
