From Stdlib Require Import String.
From compcert Require Import Integers.
From BarocqComp Require Import Utils Option.
From kernel Require Import kernel_Types kernel_ShallowR kernel_ShallowB.
Local Open Scope option_monad_scope.

Create HintDb corresRB_types.
Create HintDb corresRB_consts.
Create HintDb corresRB_pattern_matching.

Hint Rewrite constr_Kernel_READY_RtoB_corres : corresRB_consts.
Hint Rewrite constr_Kernel_READY_BtoR_corres : corresRB_pattern_matching.
Hint Rewrite constr_Kernel_READY_make_ok : corresRB_pattern_matching.
Hint Rewrite constr_Kernel_RUNNING_RtoB_corres : corresRB_consts.
Hint Rewrite constr_Kernel_RUNNING_BtoR_corres : corresRB_pattern_matching.
Hint Rewrite constr_Kernel_RUNNING_make_ok : corresRB_pattern_matching.

Hint Rewrite Kernel_proc_status_of_Z_corres : corresRB_types.
Hint Rewrite Kernel_proc_status_to_Z_corres : corresRB_types.
Hint Rewrite enum_eq_Kernel_proc_status_corres : corresRB_types.
Hint Unfold Benum.enum_neq : corresRB_types.
Hint Unfold Kernel_proc_status_neq : corresRB_types.

Hint Rewrite rconv_Kernel_proc_RtoB_proj_pid_correct : corresRB_types.
Hint Rewrite rconv_Kernel_proc_RtoB_update_pid_correct : corresRB_types.

Hint Rewrite rconv_Kernel_proc_RtoB_proj_regs_correct : corresRB_types.
Hint Rewrite rconv_Kernel_proc_RtoB_update_regs_correct : corresRB_types.

Hint Rewrite rconv_Kernel_proc_RtoB_proj_status_correct : corresRB_types.
Hint Rewrite rconv_Kernel_proc_RtoB_update_status_correct : corresRB_types.
Hint Rewrite rconv_Kernel_state_RtoB_proj_curr_pid_correct : corresRB_types.
Hint Rewrite rconv_Kernel_state_RtoB_update_curr_pid_correct : corresRB_types.

Hint Rewrite rconv_Kernel_state_RtoB_proj_procs_correct : corresRB_types.
Hint Rewrite rconv_Kernel_state_RtoB_update_procs_correct : corresRB_types.

Hint Rewrite rconv_Kernel_state_RtoB_proj_deadline_correct : corresRB_types.
Hint Rewrite rconv_Kernel_state_RtoB_update_deadline_correct : corresRB_types.

Hint Rewrite rconv_Kernel_state_RtoB_proj_mc_correct : corresRB_types.
Hint Rewrite rconv_Kernel_state_RtoB_update_mc_correct : corresRB_types.

Class RewriteRB_Machine_write_timecmp := {
  corresRB_Machine_write_timecmp:
    forall (a0: Machine_state) (a1: int64),
    kernel_ShallowB.Machine_write_timecmp a0 a1 =
    kernel_ShallowR.Machine_write_timecmp a0 a1
}.

Class RewriteRB_Kernel_update_proc_status := {
  corresRB_Kernel_update_proc_status:
    forall (ks: kernel_ShallowR.Kernel_state) (pid: int64) (status: kernel_ShallowR.Kernel_proc_status),
    kernel_ShallowB.Kernel_update_proc_status (rconv_Kernel_state_RtoB ks) pid (econv_Kernel_proc_status_RtoB status) =
    let* r := kernel_ShallowR.Kernel_update_proc_status ks pid status in
    Some (rconv_Kernel_state_RtoB r)
}.

Class RewriteRB_Kernel_schedule := {
  corresRB_Kernel_schedule:
    forall (ks: kernel_ShallowR.Kernel_state) (now: int64),
    kernel_ShallowB.Kernel_schedule (rconv_Kernel_state_RtoB ks) now =
    let* r := kernel_ShallowR.Kernel_schedule ks now in
    Some (rconv_Kernel_state_RtoB r)
}.

Ltac pattern_match_err_corres E :=
  match type of E with
  | kernel_ShallowR.Kernel_proc_status =>
      erewrite Benum.ematch_with_eq_ematch_with2 with
        (E_eq_dec := Kernel_proc_status_eq_dec)
        (econv_to := econv_Kernel_proc_status_BtoR)
        (econv_from := econv_Kernel_proc_status_RtoB);
      intros; try (apply econv_Kernel_proc_status_inv1 || apply econv_Kernel_proc_status_inv2);
      cbn [Benum.ematch_with2]; rewrite econv_Kernel_proc_status_inv1;
      autorewrite with corresRB_pattern_matching; simpl;
      autorewrite with corresRB_pattern_matching;
      destruct E; simpl
  end.

Ltac corres_rb_match P :=
  match P with
  | ret ?X => corres_rb_match X
  | bind (Some _) _ => simpl
  | bind ?F _ => corres_rb_match F
  | let _ := _ in _ => simpl
  | if ?C then _ else _ => destruct C; simpl; try reflexivity
  | Intop.I32.div ?X ?Y => destruct (Intop.I32.div X Y); simpl; try reflexivity
  | Intop.U32.div ?X ?Y => destruct (Intop.U32.div X Y); simpl; try reflexivity
  | Intop.I64.div ?X ?Y => destruct (Intop.I64.div X Y); simpl; try reflexivity
  | Intop.U64.div ?X ?Y => destruct (Intop.U64.div X Y); simpl; try reflexivity
  | Intop.I32.mod ?X ?Y => destruct (Intop.I32.mod X Y); simpl; try reflexivity
  | Intop.U32.mod ?X ?Y => destruct (Intop.U32.mod X Y); simpl; try reflexivity
  | Intop.I64.mod ?X ?Y => destruct (Intop.I64.mod X Y); simpl; try reflexivity
  | Intop.U64.mod ?X ?Y => destruct (Intop.U64.mod X Y); simpl; try reflexivity
  | Kernel_proc_status_of_Z ?X =>
      destruct (Kernel_proc_status_of_Z X); simpl; try reflexivity
  | Benum.enum_eq (_ ?E) _ => destruct E; try reflexivity
  | Benum.ematch_with (_ ?E) _ => pattern_match_err_corres E
  | Barray.get ?A ?I =>
      destruct (Barray.get A I); simpl; try reflexivity
  | Barray.set ?A ?I ?V =>
      destruct (Barray.set A I V); simpl; try reflexivity
  | kernel_ShallowB.Machine_write_timecmp _ _ =>
      rewrite corresRB_Machine_write_timecmp
  | kernel_ShallowR.Machine_write_timecmp ?A0 ?A1 =>
      destruct (kernel_ShallowR.Machine_write_timecmp A0 A1); simpl; try reflexivity
  | kernel_ShallowB.Kernel_update_proc_status _ _ _ =>
      rewrite corresRB_Kernel_update_proc_status
  | kernel_ShallowR.Kernel_update_proc_status ?KS ?PID ?STATUS =>
      destruct (kernel_ShallowR.Kernel_update_proc_status KS PID STATUS); simpl; try reflexivity
  | kernel_ShallowB.Kernel_schedule _ _ =>
      rewrite corresRB_Kernel_schedule
  | kernel_ShallowR.Kernel_schedule ?KS ?NOW =>
      destruct (kernel_ShallowR.Kernel_schedule KS NOW); simpl; try reflexivity
  end.

Ltac corres_rewrite P :=
  match P with
  | kernel_ShallowB.Machine_write_timecmp _ _ => rewrite corresRB_Machine_write_timecmp
  | kernel_ShallowB.Kernel_update_proc_status _ _ _ => rewrite corresRB_Kernel_update_proc_status
  | kernel_ShallowB.Kernel_schedule _ _ => rewrite corresRB_Kernel_schedule
  end.

Ltac rewrite_prelude :=
  autounfold with corresRB_types;
  autorewrite with corresRB_types; hnf;
  repeat (rewrite Barray.get_map_same);
  repeat (rewrite Barray.set_map_same).

Ltac finish :=
  match goal with
  | |- context[if ?E then _ else _] =>
      destruct E; try reflexivity; finish
  | _ => reflexivity
  end.

Ltac corres_rb_rec :=
  repeat
    match goal with
    | [ |- bind (ret ?X) _ = _ ] => rewrite bind_ret with (e:=X)
    | [ |- _ = bind (ret ?X) _ ] => rewrite bind_ret with (e:=X)
    | [ |- bind (Some ?X) _ = _  ] => rewrite bind_ret with (e:=X)
    | [ |- _ = bind (Some ?X) _  ] => rewrite bind_ret with (e:=X)
    | [ |- (bind (bind ?E1 ?E2) ?E3) = _ ] => rewrite assoc_bind
    | [ |- _ = (bind (bind ?E1 ?E2) ?E3) ] => rewrite assoc_bind
    | [ |- bind ?X _ = bind ?Y _ ] => apply bind_equal; intro; intros _
    | [ |-  _ = let* x := if ?C then _ else _ in _ ] => rewrite bind_if
    | [ |- (let* x := if ?C then _ else _ in _) = _ ] => rewrite bind_if
    | [ |- (if ?C then _  else _) = (if ?D then _ else _) ] => apply elim_if
    | [ |- bind ?X _ = _    ] => corres_rewrite X
    | [ |-  _  ] => progress rewrite_prelude
    | [ |- _ = match ?E with _ => _ end ] => destruct E; try reflexivity
    | [ |- ret _ = Some _ ] => finish
    | [ |- ?G = _  ] => reflexivity || (corres_rb_match G)
    end.

Ltac corres_rb :=
  autorewrite * with corresRB_consts;
  corres_rb_rec.

Ltac corres_rb_timeout :=
  timeout 600 corres_rb.
