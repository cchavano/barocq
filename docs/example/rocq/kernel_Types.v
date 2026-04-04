From Stdlib Require Import List String BinIntDef.
From compcert Require Import Integers.
From RecordUpdate Require Import RecordUpdate.
From BarocqComp Require Import Ident Option Barray Benum Brecord Utils.
From kernel Require Import kernel_ShallowR.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Local Open Scope option_monad_scope.

(** * Abstract types *)

Definition Machine_state : Type := kernel_ShallowR.Machine_state.

(** * Type definitions *)

Definition elems_of_Kernel_proc_status : list ident := [
  "Kernel_READY";
  "Kernel_RUNNING"
].

Notation Kernel_proc_status := (enum elems_of_Kernel_proc_status).

Definition fields_of_Kernel_proc : list (ident * Type) := [
  ("pid", int64 : Type);
  ("regs", array int64 : Type);
  ("status", Kernel_proc_status : Type)
].

Notation Kernel_proc := (record fields_of_Kernel_proc).

Definition fields_of_Kernel_state : list (ident * Type) := [
  ("curr_pid", int64 : Type);
  ("procs", array Kernel_proc : Type);
  ("deadline", int64 : Type);
  ("mc", Machine_state : Type)
].

Notation Kernel_state := (record fields_of_Kernel_state).

(** * Enum constructors *)

Definition Kernel_READY : Kernel_proc_status :=
  Benum.mk_enum elems_of_Kernel_proc_status "Kernel_READY" eq_refl.

Definition Kernel_RUNNING : Kernel_proc_status :=
  Benum.mk_enum elems_of_Kernel_proc_status "Kernel_RUNNING" eq_refl.

Lemma constr_Kernel_READY_make_ok :
  Benum.make_enum elems_of_Kernel_proc_status "Kernel_READY" = Some Kernel_READY.
Proof.
  reflexivity.
Qed.

Lemma constr_Kernel_RUNNING_make_ok :
  Benum.make_enum elems_of_Kernel_proc_status "Kernel_RUNNING" = Some Kernel_RUNNING.
Proof.
  reflexivity.
Qed.


(** * Barocq <-> Rocq enum conversions *)

Definition econv_Kernel_proc_status_RtoB (e: kernel_ShallowR.Kernel_proc_status) : Kernel_proc_status :=
  match e with
  | kernel_ShallowR.Kernel_READY => inl (Constr "Kernel_READY")
  | kernel_ShallowR.Kernel_RUNNING => inr (Constr "Kernel_RUNNING")
  end.

Definition econv_Kernel_proc_status_BtoR (e: Kernel_proc_status) : kernel_ShallowR.Kernel_proc_status :=
  match e with
  | inl _ => kernel_ShallowR.Kernel_READY
  | inr _ => kernel_ShallowR.Kernel_RUNNING
  end.

Lemma constr_Kernel_READY_RtoB_corres : 
  Kernel_READY = econv_Kernel_proc_status_RtoB kernel_ShallowR.Kernel_READY.
Proof.
  reflexivity.
Qed.

Lemma constr_Kernel_RUNNING_RtoB_corres : 
  Kernel_RUNNING = econv_Kernel_proc_status_RtoB kernel_ShallowR.Kernel_RUNNING.
Proof.
  reflexivity.
Qed.

Lemma constr_Kernel_READY_BtoR_corres : 
  econv_Kernel_proc_status_BtoR Kernel_READY = kernel_ShallowR.Kernel_READY.
Proof.
  reflexivity.
Qed.

Lemma constr_Kernel_RUNNING_BtoR_corres : 
  econv_Kernel_proc_status_BtoR Kernel_RUNNING = kernel_ShallowR.Kernel_RUNNING.
Proof.
  reflexivity.
Qed.


Theorem econv_Kernel_proc_status_inv1 :
  forall (e: kernel_ShallowR.Kernel_proc_status),
  econv_Kernel_proc_status_BtoR (econv_Kernel_proc_status_RtoB e) = e.
Proof.
  intro. destruct e; reflexivity.
Qed.

Theorem econv_Kernel_proc_status_inv2 :
  forall (e: Kernel_proc_status),
  econv_Kernel_proc_status_RtoB (econv_Kernel_proc_status_BtoR e) = e.
Proof.
  apply Benum.forallb_enum_equal.
  reflexivity.
Qed.

Lemma Kernel_proc_status_of_Z_corres :
  forall (z: Z),
  Benum.of_Z elems_of_Kernel_proc_status z =
  let* e := kernel_ShallowR.Kernel_proc_status_of_Z z in
  Some (econv_Kernel_proc_status_RtoB e).
Proof.
  intro. unfold Benum.of_Z. unfold Kernel_proc_status_of_Z.
  apply castZ_eqb_sound. reflexivity.
Qed.

Lemma Kernel_proc_status_to_Z_corres :
  forall (e: kernel_ShallowR.Kernel_proc_status),
  Benum.to_Z (econv_Kernel_proc_status_RtoB e) =
  kernel_ShallowR.Kernel_proc_status_to_Z e.
Proof.
  intro; destruct e; reflexivity.
Qed.

Lemma enum_eq_Kernel_proc_status_corres :
  forall (e1 e2: kernel_ShallowR.Kernel_proc_status),
  Benum.enum_eq (econv_Kernel_proc_status_RtoB e1) (econv_Kernel_proc_status_RtoB e2) =
  Kernel_proc_status_eq e1 e2.
Proof.
  intros. eapply bij_eq_iff. split.
  - apply econv_Kernel_proc_status_inv2.
  - apply econv_Kernel_proc_status_inv1.
Qed.

(** * Barocq <-> Rocq record conversions **)

Definition rconv_Kernel_proc_RtoB (r: kernel_ShallowR.Kernel_proc) : Kernel_proc :=
  (Field "pid" r.(kernel_proc_pid), (Field "regs" r.(kernel_proc_regs), (Field "status" (econv_Kernel_proc_status_RtoB r.(kernel_proc_status)), tt))).

Definition rconv_Kernel_state_RtoB (r: kernel_ShallowR.Kernel_state) : Kernel_state :=
  (Field "curr_pid" r.(kernel_state_curr_pid), (Field "procs" (Barray.map rconv_Kernel_proc_RtoB r.(kernel_state_procs)), (Field "deadline" r.(kernel_state_deadline), (Field "mc" r.(kernel_state_mc), tt)))).

Definition rconv_Kernel_proc_BtoR (r: Kernel_proc) : kernel_ShallowR.Kernel_proc :=
  match r with
  | (Field _ pid, (Field _ regs, (Field _ status, tt))) =>
      mk_Kernel_proc pid regs (econv_Kernel_proc_status_BtoR status)
  end.

Definition rconv_Kernel_state_BtoR (r: Kernel_state) : kernel_ShallowR.Kernel_state :=
  match r with
  | (Field _ curr_pid, (Field _ procs, (Field _ deadline, (Field _ mc, tt)))) =>
      mk_Kernel_state curr_pid (Barray.map rconv_Kernel_proc_BtoR procs) deadline mc
  end.

Lemma rconv_Kernel_proc_RtoB_proj_pid_correct :
  forall (r: kernel_ShallowR.Kernel_proc),
  @Brecord.project fields_of_Kernel_proc (rconv_Kernel_proc_RtoB r) "pid" eq_refl = r.(kernel_proc_pid).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_proc_RtoB_proj_regs_correct :
  forall (r: kernel_ShallowR.Kernel_proc),
  @Brecord.project fields_of_Kernel_proc (rconv_Kernel_proc_RtoB r) "regs" eq_refl = r.(kernel_proc_regs).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_proc_RtoB_proj_status_correct :
  forall (r: kernel_ShallowR.Kernel_proc),
  @Brecord.project fields_of_Kernel_proc (rconv_Kernel_proc_RtoB r) "status" eq_refl = econv_Kernel_proc_status_RtoB r.(kernel_proc_status).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_state_RtoB_proj_curr_pid_correct :
  forall (r: kernel_ShallowR.Kernel_state),
  @Brecord.project fields_of_Kernel_state (rconv_Kernel_state_RtoB r) "curr_pid" eq_refl = r.(kernel_state_curr_pid).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_state_RtoB_proj_procs_correct :
  forall (r: kernel_ShallowR.Kernel_state),
  @Brecord.project fields_of_Kernel_state (rconv_Kernel_state_RtoB r) "procs" eq_refl = Barray.map rconv_Kernel_proc_RtoB r.(kernel_state_procs).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_state_RtoB_proj_deadline_correct :
  forall (r: kernel_ShallowR.Kernel_state),
  @Brecord.project fields_of_Kernel_state (rconv_Kernel_state_RtoB r) "deadline" eq_refl = r.(kernel_state_deadline).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_state_RtoB_proj_mc_correct :
  forall (r: kernel_ShallowR.Kernel_state),
  @Brecord.project fields_of_Kernel_state (rconv_Kernel_state_RtoB r) "mc" eq_refl = r.(kernel_state_mc).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_proc_RtoB_update_pid_correct : 
  forall (r: kernel_ShallowR.Kernel_proc) (v: int64),
  @Brecord.upd fields_of_Kernel_proc (rconv_Kernel_proc_RtoB r) "pid" (int64) v eq_refl = rconv_Kernel_proc_RtoB (r <| kernel_proc_pid := v |>).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_proc_RtoB_update_regs_correct : 
  forall (r: kernel_ShallowR.Kernel_proc) (v: array int64),
  @Brecord.upd fields_of_Kernel_proc (rconv_Kernel_proc_RtoB r) "regs" (array int64) v eq_refl = rconv_Kernel_proc_RtoB (r <| kernel_proc_regs := v |>).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_proc_RtoB_update_status_correct : 
  forall (r: kernel_ShallowR.Kernel_proc) (v: kernel_ShallowR.Kernel_proc_status),
  @Brecord.upd fields_of_Kernel_proc (rconv_Kernel_proc_RtoB r) "status" (Kernel_proc_status) (econv_Kernel_proc_status_RtoB v) eq_refl = rconv_Kernel_proc_RtoB (r <| kernel_proc_status := v |>).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_state_RtoB_update_curr_pid_correct : 
  forall (r: kernel_ShallowR.Kernel_state) (v: int64),
  @Brecord.upd fields_of_Kernel_state (rconv_Kernel_state_RtoB r) "curr_pid" (int64) v eq_refl = rconv_Kernel_state_RtoB (r <| kernel_state_curr_pid := v |>).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_state_RtoB_update_procs_correct : 
  forall (r: kernel_ShallowR.Kernel_state) (v: array kernel_ShallowR.Kernel_proc),
  @Brecord.upd fields_of_Kernel_state (rconv_Kernel_state_RtoB r) "procs" (array Kernel_proc) (Barray.map rconv_Kernel_proc_RtoB v) eq_refl = rconv_Kernel_state_RtoB (r <| kernel_state_procs := v |>).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_state_RtoB_update_deadline_correct : 
  forall (r: kernel_ShallowR.Kernel_state) (v: int64),
  @Brecord.upd fields_of_Kernel_state (rconv_Kernel_state_RtoB r) "deadline" (int64) v eq_refl = rconv_Kernel_state_RtoB (r <| kernel_state_deadline := v |>).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_state_RtoB_update_mc_correct : 
  forall (r: kernel_ShallowR.Kernel_state) (v: Machine_state),
  @Brecord.upd fields_of_Kernel_state (rconv_Kernel_state_RtoB r) "mc" (Machine_state) v eq_refl = rconv_Kernel_state_RtoB (r <| kernel_state_mc := v |>).
Proof.
  reflexivity.
Qed.

Lemma rconv_Kernel_proc_BtoR_correct :
  forall (b: Kernel_proc) (r: kernel_ShallowR.Kernel_proc),
  rconv_Kernel_proc_BtoR b = r ->
  @Brecord.project fields_of_Kernel_proc b "pid" eq_refl = r.(kernel_proc_pid) /\
  @Brecord.project fields_of_Kernel_proc b "regs" eq_refl = r.(kernel_proc_regs) /\
  econv_Kernel_proc_status_BtoR (@Brecord.project fields_of_Kernel_proc b "status" eq_refl) = r.(kernel_proc_status).
Proof.
  Brecord.apply_decomp_field.
  compute. intros. subst. repeat esplit.
Qed.

Lemma rconv_Kernel_state_BtoR_correct :
  forall (b: Kernel_state) (r: kernel_ShallowR.Kernel_state),
  rconv_Kernel_state_BtoR b = r ->
  @Brecord.project fields_of_Kernel_state b "curr_pid" eq_refl = r.(kernel_state_curr_pid) /\
  Barray.map rconv_Kernel_proc_BtoR (@Brecord.project fields_of_Kernel_state b "procs" eq_refl) = r.(kernel_state_procs) /\
  @Brecord.project fields_of_Kernel_state b "deadline" eq_refl = r.(kernel_state_deadline) /\
  @Brecord.project fields_of_Kernel_state b "mc" eq_refl = r.(kernel_state_mc).
Proof.
  Brecord.apply_decomp_field.
  compute. intros. subst. repeat esplit.
Qed.

Theorem array_map_conv_inv :
  forall (A B: Type) (f: A -> B) (g: B -> A) (Hinv: forall x, g (f x) = x),
  forall (a: array A), Barray.map g (Barray.map f a) = a.
Proof.
  induction a as [|a0 a']; intros.
  - reflexivity.
  - simpl. rewrite (Hinv a0). f_equal. apply IHa'.
Qed.

Theorem rconv_Kernel_proc_inv1 :
  forall (r: kernel_ShallowR.Kernel_proc),
  rconv_Kernel_proc_BtoR (rconv_Kernel_proc_RtoB r) = r.
Proof.
  intro. destruct r; simpl. f_equal.
  - apply econv_Kernel_proc_status_inv1.
Qed.

Theorem rconv_Kernel_state_inv1 :
  forall (r: kernel_ShallowR.Kernel_state),
  rconv_Kernel_state_BtoR (rconv_Kernel_state_RtoB r) = r.
Proof.
  intro. destruct r; simpl. f_equal.
  - apply array_map_conv_inv; apply rconv_Kernel_proc_inv1.
Qed.

Theorem rconv_Kernel_proc_inv2 :
  forall (r: Kernel_proc),
  rconv_Kernel_proc_RtoB (rconv_Kernel_proc_BtoR r) = r.
Proof.
  Brecord.apply_decomp_field. unfold rconv_Kernel_proc_RtoB.
  simpl; repeat apply Brecord.field_eq;auto.
  - apply econv_Kernel_proc_status_inv2.
Qed.

Theorem rconv_Kernel_state_inv2 :
  forall (r: Kernel_state),
  rconv_Kernel_state_RtoB (rconv_Kernel_state_BtoR r) = r.
Proof.
  Brecord.apply_decomp_field. unfold rconv_Kernel_state_RtoB.
  simpl; repeat apply Brecord.field_eq;auto.
  - apply array_map_conv_inv; apply rconv_Kernel_proc_inv2.
Qed.
