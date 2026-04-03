From Stdlib Require Import String List.
From compcert Require Import Integers.
From BarocqComp Require Import Ident Option Maps2 Barray Benum Brecord Types Typing Denot ExtEqual BarocqBNF BarocqBNFVC CorresBD_Tactics Syntax.
From kernel Require Import kernel_Types kernel_ShallowB kernel_Deep.

Import ListNotations.

Open Scope string_scope.

Module Deeptypes.

  Definition tbool := TBool.

  Definition tint32 := TInt32 Signed.

  Definition tuint32 := TInt32 Unsigned.

  Definition tint64 := TInt64 Signed.

  Definition tuint64 := TInt64 Unsigned.

  Definition elems_of_Kernel_proc_status : list ident := ["Kernel_READY"; "Kernel_RUNNING"].

  Definition Kernel_proc_status : typ := TEnum "Kernel_proc_status" elems_of_Kernel_proc_status.

  Definition fields_of_Kernel_proc : list (ident * typ) := [("pid", tuint64); ("regs", TArray tuint64); ("status", Kernel_proc_status)].

  Definition Kernel_proc : typ := TRecord "Kernel_proc" fields_of_Kernel_proc.

  Definition fields_of_Kernel_state : list (ident * typ) := [("curr_pid", tuint64); ("procs", TArray Kernel_proc); ("deadline", tuint64); ("mc", TAbs "Machine_state")].

  Definition Kernel_state : typ := TRecord "Kernel_state" fields_of_Kernel_state.

  Definition typof_Machine_write_timecmp := TFun [TAbs "Machine_state"; tuint64] (TAbs "Machine_state").

  Definition typof_Kernel_nb_procs := tuint64.

  Definition typof_Kernel_quantum := tuint64.

  Definition typof_Kernel_update_proc_status := TFun [Kernel_state; tuint64; Kernel_proc_status] Kernel_state.

  Definition typof_Kernel_schedule := TFun [Kernel_state; tuint64] Kernel_state.

End Deeptypes.

(** * Abstract types implementation *)

Definition abs_types_impl : SMap.t Type :=
  List.fold_left
    (fun ge '(d, s) => SMap.set d s ge)
    [
      ("Machine_state", Machine_state : Type)
    ]
    (SMap.init (unit : Type)).

Local Notation "# X" := (Types.eval_typ abs_types_impl X) (at level 90).

Definition VAL (t: typ) (v: #t) := Val abs_types_impl t v.

Definition abs_defs_impl : genv abs_types_impl :=
  List.fold_left
    (fun ge '(d, s) => STree.set d s ge)
    [
      ("Machine_write_timecmp", VAL Deeptypes.typof_Machine_write_timecmp Machine_write_timecmp)
    ]
    STree.empty.

(** Typing environment *)

Definition typing_env : tenv := Eval compute in {|
  TEnv.tenv_defs :=
    STree.set "Kernel_proc_status" (TdEnum Deeptypes.elems_of_Kernel_proc_status)
      (STree.set "Kernel_proc" (TdRecord Deeptypes.fields_of_Kernel_proc)
        (STree.set "Kernel_state" (TdRecord Deeptypes.fields_of_Kernel_state)
          (STree.empty)));
  TEnv.tenv_constr_types :=
    STree.set "Kernel_READY" "Kernel_proc_status"
      (STree.set "Kernel_RUNNING" "Kernel_proc_status"
        (STree.empty))
|}.

(** Properties environments *)

Definition propt : Type := string * value abs_types_impl.

Definition prop_list : list propt :=
  [
    ("Machine_write_timecmp",VAL Deeptypes.typof_Machine_write_timecmp kernel_ShallowB.Machine_write_timecmp);
    ("Kernel_nb_procs",VAL Deeptypes.typof_Kernel_nb_procs kernel_ShallowB.Kernel_nb_procs);
    ("Kernel_quantum",VAL Deeptypes.typof_Kernel_quantum kernel_ShallowB.Kernel_quantum);
    ("Kernel_update_proc_status",VAL Deeptypes.typof_Kernel_update_proc_status kernel_ShallowB.Kernel_update_proc_status);
    ("Kernel_schedule",VAL Deeptypes.typof_Kernel_schedule kernel_ShallowB.Kernel_schedule)
  ].

Definition arch : Target.archi := Target.Ptr64.

Definition needed_checked_Machine_write_timecmp : list propt := [].
Definition needed_checked_Kernel_update_proc_status : list propt := []  .
Definition needed_checked_Kernel_schedule : list propt := [
    ("Machine_write_timecmp",VAL Deeptypes.typof_Machine_write_timecmp kernel_ShallowB.Machine_write_timecmp);
    ("Kernel_nb_procs",VAL Deeptypes.typof_Kernel_nb_procs kernel_ShallowB.Kernel_nb_procs);
    ("Kernel_quantum",VAL Deeptypes.typof_Kernel_quantum kernel_ShallowB.Kernel_quantum);
    ("Kernel_update_proc_status",VAL Deeptypes.typof_Kernel_update_proc_status kernel_ShallowB.Kernel_update_proc_status)
  ]
  .
Definition params_Machine_write_timecmp : list (ident * typ) := [("a0", TAbs "Machine_state"); ("a1", Deeptypes.tuint64)].
Definition params_Kernel_update_proc_status : list (ident * typ) := [("p_ks", Deeptypes.Kernel_state); ("p_pid", Deeptypes.tuint64); ("p_status", Deeptypes.Kernel_proc_status)].
Definition params_Kernel_schedule : list (ident * typ) := [("p_ks", Deeptypes.Kernel_state); ("p_now", Deeptypes.tuint64)].
Definition vc : list Prop :=
  [
    let ge := genv_has_property abs_types_impl STree.empty needed_checked_Kernel_schedule in
      let v : #Deeptypes.typof_Kernel_schedule := eval_fun arch abs_types_impl typing_env ge params_Kernel_schedule Deeptypes.Kernel_state (Syntax.fn_body kernel_Deep.fun_Kernel_schedule) in
eq_value abs_types_impl (VAL Deeptypes.typof_Kernel_schedule Kernel_schedule) _ v
;
    (* ========================== *)
    let ge := genv_has_property abs_types_impl STree.empty needed_checked_Kernel_update_proc_status in
      let v : #Deeptypes.typof_Kernel_update_proc_status := eval_fun arch abs_types_impl typing_env ge params_Kernel_update_proc_status Deeptypes.Kernel_state (Syntax.fn_body kernel_Deep.fun_Kernel_update_proc_status) in
eq_value abs_types_impl (VAL Deeptypes.typof_Kernel_update_proc_status Kernel_update_proc_status) _ v
;
    (* ========================== *)
     check_value abs_types_impl (Barocq.eval_literal abs_types_impl typing_env kernel_Deep.const_Kernel_quantum) (Deeptypes.typof_Kernel_quantum) (VAL Deeptypes.typof_Kernel_quantum kernel_ShallowB.Kernel_quantum);
    (* ========================== *)
     check_value abs_types_impl (Barocq.eval_literal abs_types_impl typing_env kernel_Deep.const_Kernel_nb_procs) (Deeptypes.typof_Kernel_nb_procs) (VAL Deeptypes.typof_Kernel_nb_procs kernel_ShallowB.Kernel_nb_procs);
    (* ========================== *)
    let ge := genv_has_property abs_types_impl STree.empty needed_checked_Machine_write_timecmp in
      let v : #Deeptypes.typof_Machine_write_timecmp := kernel_ShallowB.Machine_write_timecmp in
eq_value abs_types_impl (VAL Deeptypes.typof_Machine_write_timecmp Machine_write_timecmp) _ v

  ].