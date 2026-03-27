From Coq Require Import String.
From compcert Require Import Integers.
From BarocqComp Require Import Option.
From kernel Require Import kernel_Types kernel_ShallowR kernel_ShallowB kernel_CorresRB_Tactics.

Open Scope option_monad_scope.
Open Scope string_scope.

Opaque Benum.enum.
Opaque Benum.match_with_err.
Opaque Brecord.record.
Opaque Brecord.project.
Opaque Brecord.upd.
Opaque Barray.get.
Opaque Barray.set.
Opaque econv_Kernel_proc_status_RtoB.
Opaque econv_Kernel_proc_status_BtoR.

Theorem fun_Machine_write_timecmp_corres : 
  forall (a0: Machine_state) (a1: int64),
  kernel_ShallowB.Machine_write_timecmp a0 a1 =
  kernel_ShallowR.Machine_write_timecmp a0 a1.
Proof.
  intros. unfold kernel_ShallowB.Machine_write_timecmp.
  destruct (kernel_ShallowR.Machine_write_timecmp a0 a1); reflexivity.
Qed.

Opaque kernel_ShallowR.Machine_write_timecmp.
Opaque kernel_ShallowB.Machine_write_timecmp.

Instance RewriteRB_inst_Machine_write_timecmp : RewriteRB_Machine_write_timecmp := {
  corresRB_Machine_write_timecmp := fun_Machine_write_timecmp_corres
}.

Theorem const_Kernel_nb_procs_corres :
  kernel_ShallowB.Kernel_nb_procs = kernel_ShallowR.Kernel_nb_procs.
Proof.
  reflexivity.
Qed.

Hint Opaque Kernel_nb_procs : corresRB_consts.
Hint Rewrite const_Kernel_nb_procs_corres : corresRB_consts.

Theorem const_Kernel_quantum_corres :
  kernel_ShallowB.Kernel_quantum = kernel_ShallowR.Kernel_quantum.
Proof.
  reflexivity.
Qed.

Hint Opaque Kernel_quantum : corresRB_consts.
Hint Rewrite const_Kernel_quantum_corres : corresRB_consts.

Theorem fun_Kernel_update_proc_status_corres : 
  forall (ks: kernel_ShallowR.Kernel_state) (pid: int64) (status: kernel_ShallowR.Kernel_proc_status),
  kernel_ShallowB.Kernel_update_proc_status (rconv_Kernel_state_RtoB ks) pid (econv_Kernel_proc_status_RtoB status) =
  let* r := kernel_ShallowR.Kernel_update_proc_status ks pid status in
  Some (rconv_Kernel_state_RtoB r).
Proof.
  intros. unfold kernel_ShallowB.Kernel_update_proc_status; unfold kernel_ShallowR.Kernel_update_proc_status.
  corres_rb_timeout.
Qed.

Opaque kernel_ShallowR.Kernel_update_proc_status.
Opaque kernel_ShallowB.Kernel_update_proc_status.

Instance RewriteRB_inst_Kernel_update_proc_status : RewriteRB_Kernel_update_proc_status := {
  corresRB_Kernel_update_proc_status := fun_Kernel_update_proc_status_corres
}.

Theorem fun_Kernel_schedule_corres : 
  forall (ks: kernel_ShallowR.Kernel_state) (now: int64),
  kernel_ShallowB.Kernel_schedule (rconv_Kernel_state_RtoB ks) now =
  let* r := kernel_ShallowR.Kernel_schedule ks now in
  Some (rconv_Kernel_state_RtoB r).
Proof.
  intros. unfold kernel_ShallowB.Kernel_schedule; unfold kernel_ShallowR.Kernel_schedule.
  corres_rb_timeout.
Qed.

Opaque kernel_ShallowR.Kernel_schedule.
Opaque kernel_ShallowB.Kernel_schedule.

Instance RewriteRB_inst_Kernel_schedule : RewriteRB_Kernel_schedule := {
  corresRB_Kernel_schedule := fun_Kernel_schedule_corres
}.
