From Coq Require Import Bool List BinIntDef.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From BarocqComp Require Import Error Barray Intop Utils.
Import BoolNotations ListNotations.

Open Scope Z_scope.
Open Scope error_monad_scope.

(** * Type definitions *)

Parameter Machine_state : Type.

Inductive Kernel_proc_status :=
  | Kernel_READY
  | Kernel_RUNNING.

Record Kernel_proc := mk_Kernel_proc {
  kernel_proc_pid: int64;
  kernel_proc_regs: array int64;
  kernel_proc_status: Kernel_proc_status
}.

Record Kernel_state := mk_Kernel_state {
  kernel_state_curr_pid: int64;
  kernel_state_procs: array Kernel_proc;
  kernel_state_deadline: int64;
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

Definition cast_Kernel_proc_status_to_i32 (e: Kernel_proc_status) : int :=
  match e with
  | Kernel_READY => Int.repr 0
  | Kernel_RUNNING => Int.repr 1
  end.

Definition cast_i32_to_Kernel_proc_status (i: int) : res Kernel_proc_status :=
  let ni := I32.to_nat i in
  if Int.cmp Clt i Int.zero || Nat.leb 2%nat ni then fail
  else
    list_nth_err
      [
        Kernel_READY;
        Kernel_RUNNING
      ]
      ni.

Definition neqb (b1 b2: bool) := negb (eqb b1 b2).

(** * Program *)

Parameter Machine_read_time : Machine_state -> res int64.

Parameter Machine_write_timecmp : Machine_state -> int64 -> res Machine_state.

Definition Kernel_nb_procs : int64 := Int64.repr 5.

Definition Kernel_quantum : int64 := Int64.repr 100.

Definition Kernel_sync (p_ks: Kernel_state) : res Kernel_state :=
  let* b0 := Machine_write_timecmp (p_ks.(kernel_state_mc)) (p_ks.(kernel_state_deadline)) in
  ret (p_ks <| kernel_state_mc := b0 |>).

Definition Kernel_update_proc_status (p_ks: Kernel_state) (p_pid: int64) (p_status: Kernel_proc_status) : res Kernel_state :=
  let u_procs := p_ks.(kernel_state_procs) in
  let* u_proc := Barray.get u_procs p_pid in
  let u_proc := u_proc <| kernel_proc_status := p_status |> in
  let* u_procs := Barray.set u_procs p_pid u_proc in
  ret (p_ks <| kernel_state_procs := u_procs |>).

Definition Kernel_schedule (p_ks: Kernel_state) : res Kernel_state :=
  let* b0 := Machine_read_time (p_ks.(kernel_state_mc)) in
  if (Int64.cmpu Cgt b0 (p_ks.(kernel_state_deadline))) then
    let u_curr_pid := p_ks.(kernel_state_curr_pid) in
    let* u_next_pid := U64.mod (Int64.add u_curr_pid (Int64.repr 1)) Kernel_nb_procs in
    let u_next_deadline := Int64.add (p_ks.(kernel_state_deadline)) Kernel_quantum in
    let* u_ks := Kernel_update_proc_status p_ks u_curr_pid (Kernel_READY) in
    let* u_ks := Kernel_update_proc_status u_ks u_next_pid (Kernel_RUNNING) in
    let u_ks := (u_ks <| kernel_state_curr_pid := u_next_pid |>) <| kernel_state_deadline := u_next_deadline |> in
    Kernel_sync u_ks
  else
    ret p_ks.
