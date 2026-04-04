From Stdlib Require Import Bool List BinIntDef.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From BarocqComp Require Import Option Barray Intop Utils.
From BarocqComp Require Import ShallowNotations.

(** * Abstract types *)

Parameter Machine_state : Type.

(** * Type definitions *)

Inductive Kernel_proc_status :=
  | Kernel_READY
  | Kernel_RUNNING.

Record Kernel_proc := mk_Kernel_proc {
  kernel_proc_pid: u64;
  kernel_proc_regs: list u64;
  kernel_proc_status: Kernel_proc_status
}.

Record Kernel_state := mk_Kernel_state {
  kernel_state_curr_pid: u64;
  kernel_state_procs: list Kernel_proc;
  kernel_state_deadline: u64;
  kernel_state_mc: Machine_state
}.

(** * Setters for records *)

Instance eta_Kernel_proc : Settable Kernel_proc :=
  settable! mk_Kernel_proc <kernel_proc_pid; kernel_proc_regs; kernel_proc_status>.

Instance eta_Kernel_state : Settable Kernel_state :=
  settable! mk_Kernel_state <kernel_state_curr_pid; kernel_state_procs; kernel_state_deadline; kernel_state_mc>.

(** * Auxiliary functions *)

Lemma Kernel_proc_status_eq_dec :
  forall (x y: Kernel_proc_status), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition Kernel_proc_status_eq (x y: Kernel_proc_status) : bool :=
  if Kernel_proc_status_eq_dec x y then true else false.

Definition Kernel_proc_status_neq (x y: Kernel_proc_status) : bool :=
  negb (Kernel_proc_status_eq x y).

Definition Kernel_proc_status_to_Z (e: Kernel_proc_status) : Z :=
  match e with
  | Kernel_READY => 0
  | Kernel_RUNNING => 1
  end.

Definition Kernel_proc_status_of_Z (z: Z) : option Kernel_proc_status :=
  cast_enum [
    Kernel_READY;
    Kernel_RUNNING
  ] z.

Definition neqb (b1 b2: bool) := negb (eqb b1 b2).

(** * Program *)

Parameter Machine_write_timecmp : Machine_state -> u64 -> option Machine_state.

Definition Kernel_nb_procs : u64 := 5UL.

Definition Kernel_quantum : u64 := 100UL.

Definition Kernel_update_proc_status (ks: Kernel_state) (pid: u64) (status: Kernel_proc_status) : option Kernel_state :=
  let procs := ks.(kernel_state_procs) in
  let* proc := procs.[pid] in
  let proc := proc <| kernel_proc_status := status |> in
  let* procs := procs.[pid <- proc] in
  ret (ks <| kernel_state_procs := procs |>).

Definition Kernel_schedule (ks: Kernel_state) (now: u64) : option Kernel_state :=
  if (Int64.cmpu Cgt now (ks.(kernel_state_deadline))) then
    let curr_pid := ks.(kernel_state_curr_pid) in
    let* next_pid := (curr_pid +₆₄ (1UL)) modu₆₄ Kernel_nb_procs in
    let next_deadline := now +₆₄ Kernel_quantum in
    let* ks := Kernel_update_proc_status ks curr_pid (Kernel_READY) in
    let* ks := Kernel_update_proc_status ks next_pid (Kernel_RUNNING) in
    let ks := (ks <| kernel_state_curr_pid := next_pid |>) <| kernel_state_deadline := next_deadline |> in
    let* b1 := Machine_write_timecmp (ks.(kernel_state_mc)) (ks.(kernel_state_deadline)) in
    ret (ks <| kernel_state_mc := b1 |>)
  else
    ret ks.
