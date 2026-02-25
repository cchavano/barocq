From Coq Require Import List Bool.
From BarocqComp Require Import Utils Syntax Types Typing Imp1 Maps2.

Fixpoint check_statement (s: statement) : bool :=
  match s with
  | StSet x (CpArraySet a i v _) =>
      let ta := btypof_atom a in
      match ta with
      | BArray ((BRecord _ _ | BArray _ _)) (LyUnboxed _) => false
      | _ => true
      end
  | StSet x (CpRecordUpdate a f v _) =>
      let ta := btypof_atom a in
      match ta with
      | BRecord rid ub =>
          if list_mem Ident.eq_dec f ub then false
          else true
      | _ => true
      end
  | StIfThenElse c s1 s2 =>
      (check_statement s1) && (check_statement s2)
  | StSwitch a cases =>
      List.forallb (fun '(_, si) => check_statement si) cases
  | StSequence s1 s2 =>
      (check_statement s1) && (check_statement s2)
  | _ => true
end.

Definition check_function (f: function) : bool :=
  check_statement (fn_body f).

Definition check_program (prog: program) : bool :=
  List.forallb
    (fun d =>
      match d with
      | DefFun x f => check_function f
      | _ => true
      end)
    (prog_defs prog).