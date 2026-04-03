From Stdlib Require Import String List BinIntDef.
From compcert Require Import Integers.
From BarocqComp Require Import Ident Types Syntax Benum BarocqBNF.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

Definition tbool := BBool.

Definition tint32 := BInt32 Signed.

Definition tuint32 := BInt32 Unsigned.

Definition tint64 := BInt64 Signed.

Definition tuint64 := BInt64 Unsigned.

Definition enum_Kernel_proc_status : type_def field_descr :=
  TdEnum[
    "Kernel_READY";
    "Kernel_RUNNING"
  ].
Definition record_Kernel_proc : type_def field_descr :=
  TdRecord[
    ("pid", (tuint64, LyPrim));
    ("regs", (BArray tuint64 LyPrim, (LyUnboxed (Some 32))));
    ("status", (BEnum "Kernel_proc_status", LyPrim))
  ].
Definition record_Kernel_state : type_def field_descr :=
  TdRecord[
    ("curr_pid", (tuint64, LyPrim));
    ("procs", (BArray (BRecord "Kernel_proc" ["regs"]) (LyUnboxed None), (LyUnboxed (Some 5))));
    ("deadline", (tuint64, LyPrim));
    ("mc", (BAbs "Machine_state", LyBoxed))
  ].

Definition const_Kernel_nb_procs : Syntax.literal := LInt64 (Int64.repr 5) Unsigned.
Definition const_Kernel_quantum : Syntax.literal := LInt64 (Int64.repr 100) Unsigned.
Definition fun_Kernel_update_proc_status : BarocqBNF.function := {|
  fn_return := BRecord "Kernel_state" ["procs"];
  fn_params := [("p_ks",BRecord "Kernel_state" ["procs"]);("p_pid",tuint64);("p_status",BEnum "Kernel_proc_status")];
  fn_body :=
    ELetIn "u1_procs" (EAtom (ARecordProj (AVar "p_ks" (BRecord "Kernel_state" ["procs"])) "procs" (LyUnboxed (Some 5)) (BArray (BRecord "Kernel_proc" ["regs"]) (LyUnboxed None))))
      (ELetIn "u1_proc" (EAtom (AArrayGet (AVar "u1_procs" (BArray (BRecord "Kernel_proc" ["regs"]) (LyUnboxed None))) (AVar "p_pid" (tuint64)) (LyUnboxed None) (BRecord "Kernel_proc" ["regs"])))
        (ELetIn "u2_proc" (ERecordUpdate (AVar "u1_proc" (BRecord "Kernel_proc" ["regs"])) "status" (AVar "p_status" (BEnum "Kernel_proc_status")) (BRecord "Kernel_proc" ["regs"]))
          (ELetIn "u2_procs" (EArraySet (AVar "u1_procs" (BArray (BRecord "Kernel_proc" ["regs"]) (LyUnboxed None))) (AVar "p_pid" (tuint64)) (AVar "u2_proc" (BRecord "Kernel_proc" ["regs"])) (BArray (BRecord "Kernel_proc" ["regs"]) (LyUnboxed None)))
            (ERecordUpdate (AVar "p_ks" (BRecord "Kernel_state" ["procs"])) "procs" (AVar "u2_procs" (BArray (BRecord "Kernel_proc" ["regs"]) (LyUnboxed None))) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])
|}.
Definition fun_Kernel_schedule : BarocqBNF.function := {|
  fn_return := BRecord "Kernel_state" ["procs"];
  fn_params := [("p_ks",BRecord "Kernel_state" ["procs"]);("p_now",tuint64)];
  fn_body :=
    EIfThenElse (ABinaryOp BopGt (AVar "p_now" (tuint64)) (ARecordProj (AVar "p_ks" (BRecord "Kernel_state" ["procs"])) "deadline" LyPrim (tuint64)) (tbool))
      (ELetIn "u1_curr_pid" (EAtom (ARecordProj (AVar "p_ks" (BRecord "Kernel_state" ["procs"])) "curr_pid" LyPrim (tuint64)))
        (ELetIn "u1_next_pid" (EAtom (ABinaryOp BopMod (ABinaryOp BopAdd (AVar "u1_curr_pid" (tuint64)) (AInt64 (Int64.repr 1) Unsigned) (tuint64)) (AVar "Kernel_nb_procs" (tuint64)) (tuint64)))
          (ELetIn "u1_next_deadline" (EAtom (ABinaryOp BopAdd (AVar "p_now" (tuint64)) (AVar "Kernel_quantum" (tuint64)) (tuint64)))
            (ELetIn "u1_ks" (EApp (AVar "Kernel_update_proc_status" (BFun [BRecord "Kernel_state" ["procs"]; tuint64; BEnum "Kernel_proc_status"] (BRecord "Kernel_state" ["procs"]))) [AVar "p_ks" (BRecord "Kernel_state" ["procs"]);AVar "u1_curr_pid" (tuint64);AConstr "Kernel_READY" (Int.repr 0) (BEnum "Kernel_proc_status")] (BRecord "Kernel_state" ["procs"]))
              (ELetIn "u2_ks" (EApp (AVar "Kernel_update_proc_status" (BFun [BRecord "Kernel_state" ["procs"]; tuint64; BEnum "Kernel_proc_status"] (BRecord "Kernel_state" ["procs"]))) [AVar "u1_ks" (BRecord "Kernel_state" ["procs"]);AVar "u1_next_pid" (tuint64);AConstr "Kernel_RUNNING" (Int.repr 1) (BEnum "Kernel_proc_status")] (BRecord "Kernel_state" ["procs"]))
                (ELetIn "u3_ks" (ELetIn "b2" (ERecordUpdate (AVar "u2_ks" (BRecord "Kernel_state" ["procs"])) "curr_pid" (AVar "u1_next_pid" (tuint64)) (BRecord "Kernel_state" ["procs"]))
  (ERecordUpdate (AVar "b2" (BRecord "Kernel_state" ["procs"])) "deadline" (AVar "u1_next_deadline" (tuint64)) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"]))
                  (ELetIn "b5" (EApp (AVar "Machine_write_timecmp" (BFun [BAbs "Machine_state"; tuint64] (BAbs "Machine_state"))) [ARecordProj (AVar "u3_ks" (BRecord "Kernel_state" ["procs"])) "mc" LyBoxed (BAbs "Machine_state");ARecordProj (AVar "u3_ks" (BRecord "Kernel_state" ["procs"])) "deadline" LyPrim (tuint64)] (BAbs "Machine_state"))
                    (ERecordUpdate (AVar "u3_ks" (BRecord "Kernel_state" ["procs"])) "mc" (AVar "b5" (BAbs "Machine_state")) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"])) (BRecord "Kernel_state" ["procs"]))
      (EAtom (AVar "p_ks" (BRecord "Kernel_state" ["procs"]))) (BRecord "Kernel_state" ["procs"])
|}.

Definition prog_types : prog_types_t := [
  ("Kernel_proc_status",enum_Kernel_proc_status);
  ("Kernel_proc",record_Kernel_proc);
  ("Kernel_state",record_Kernel_state)
].

Definition prog_defs : list globdef := [
DeclFun "Machine_write_timecmp" [(AttrWrite,BAbs "Machine_state");(AttrNone,tuint64)] (BAbs "Machine_state");
DefConst "Kernel_nb_procs" const_Kernel_nb_procs (tuint64);
DefConst "Kernel_quantum" const_Kernel_quantum (tuint64);
DefFun "Kernel_update_proc_status" fun_Kernel_update_proc_status;
DefFun "Kernel_schedule" fun_Kernel_schedule
].

Definition prog_tabs  := [
  ("Machine_state",SU_struct)
].

Definition prog := mk_program prog_defs prog_types prog_tabs.
