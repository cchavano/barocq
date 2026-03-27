From Coq Require Import Bool List BinIntDef String.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From BarocqComp Require Import Ident Option Barray Benum Brecord Intop.
From kernel Require Import kernel_Types.
Import BoolNotations ListNotations BarocqNotations.

Open Scope Z_scope.
Open Scope string_scope.
Local Open Scope option_monad_scope.

(** * Auxiliary functions *)

Definition neqb (b1 b2: bool) := negb (Bool.eqb b1 b2).

(** * Program *)

Definition Machine_write_timecmp : Machine_state -> int64 -> option Machine_state :=
  fun a0 a1 =>
    let* r := kernel_ShallowR.Machine_write_timecmp a0 a1 in
    ret r.

Definition Kernel_nb_procs : int64 := 5UL.

Definition Kernel_quantum : int64 := 100UL.

Definition Kernel_update_proc_status (p_ks: Kernel_state) (p_pid: int64) (p_status: Kernel_proc_status) : option Kernel_state :=
  let u1_procs := Brecord.project p_ks "procs" eq_refl in
  let* u1_proc := u1_procs.[p_pid] in
  let u2_proc := u1_proc @ "status" <- p_status in
  let* u2_procs := u1_procs.[p_pid <- u2_proc] in
  ret (p_ks @ "procs" <- u2_procs).

Definition Kernel_schedule (p_ks: Kernel_state) (p_now: int64) : option Kernel_state :=
  if (Int64.cmpu Cgt p_now (Brecord.project p_ks "deadline" eq_refl)) then
    let u1_curr_pid := Brecord.project p_ks "curr_pid" eq_refl in
    let* u1_next_pid := (u1_curr_pid +₆₄ (1UL)) modu₆₄ Kernel_nb_procs in
    let u1_next_deadline := p_now +₆₄ Kernel_quantum in
    let* u1_ks := Kernel_update_proc_status p_ks u1_curr_pid (kernel_Types.Kernel_READY) in
    let* u2_ks := Kernel_update_proc_status u1_ks u1_next_pid (kernel_Types.Kernel_RUNNING) in
    let u3_ks :=
      let b2 := u2_ks @ "curr_pid" <- u1_next_pid in
      b2 @ "deadline" <- u1_next_deadline
    in
    let* b5 := Machine_write_timecmp (Brecord.project u3_ks "mc" eq_refl) (Brecord.project u3_ks "deadline" eq_refl) in
    ret (u3_ks @ "mc" <- b5)
  else
    ret p_ks.
