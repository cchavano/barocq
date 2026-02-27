From Coq Require Import String List.
From BarocqComp Require Import Monads Syntax Barocq Benum Ident Maps2.

Open Scope string_scope.

Module STATE <: STATE_TYPE.
  Definition t := STree.t nat.
End STATE.

Module MonRename := MonState(STATE).

Import MonRename.

Open Scope state_monad_scope.

Definition mk_local_id (n: nat) (x: ident) : ident :=
  let ui := Ident.concat "u" (Ident.of_str_nat n) in
  Ident.concat (Ident.concat ui "_") x.

Definition rename_var (se: STree.t ident) (x: ident) : ident :=
  match STree.get x se with
  | Some x' => x'
  | None => x
  end.
  (* match STree.get x se with
  (* parameter *)
  | Some 0 => Ident.concat "p_" x
  (* local variable *)
  | Some n => mk_local_id n x
  (* global variable *)
  | None => x
  end. *)

Definition fresh_var (se: STree.t ident) (x: ident) : MonRename.M (ident * STree.t ident) :=
  fun s =>
    let n :=
      match STree.get x s with
      | Some n => n + 1
      | None => 1
      end
    in
    let x' := mk_local_id n x in
    ((x', STree.set x x' se), STree.set x n s).

Fixpoint rename_expr (se: STree.t ident) (e: expr) : MonRename.M expr :=
  match e with
  | ETrue | EFalse
  | EInt32 _ _ | EInt64 _ _
  | EConstr _ => ret e
  | EVar x =>
      let x' := rename_var se x in
      ret (EVar x')
  | ECast e1 ty =>
      let* e1' := rename_expr se e1 in
      ret (ECast e1' ty)
  | EUnaryOp op e1 =>
      let* e1' := rename_expr se e1 in
      ret (EUnaryOp op e1')
  | EBinaryOp op e1 e2 =>
      let* e1' := rename_expr se e1 in
      let* e2' := rename_expr se e2 in
      ret (EBinaryOp op e1' e2')
  | EArrayGet e1 e2 =>
      let* e1' := rename_expr se e1 in
      let* e2' := rename_expr se e2 in
      ret (EArrayGet e1' e2')
  | EArraySet e1 e2 e3 =>
      let* e1' := rename_expr se e1 in
      let* e2' := rename_expr se e2 in
      let* e3' := rename_expr se e3 in
      ret (EArraySet e1' e2' e3')
  | ERecordProj e1 f =>
      let* e1' := rename_expr se e1 in
      ret (ERecordProj e1' f)
  | ERecordUpdate e1 f e2 =>
      let* e1' := rename_expr se e1 in
      let* e2' := rename_expr se e2 in
      ret (ERecordUpdate e1' f e2')
  | EApp e1 args =>
      let* e1' := rename_expr se e1 in
      let* args' :=
        List.fold_right
          (fun e acc =>
            let* acc := acc in
            let* e' := rename_expr se e in
            ret (e' :: acc))
          (ret nil)
          args 
      in
      ret (EApp e1' args')
  | EIfThenElse e1 e2 e3 =>
      let* e1' := rename_expr se e1 in
      let* e2' := rename_expr se e2 in
      let* e3' := rename_expr se e3 in
      ret (EIfThenElse e1' e2' e3')
  | EMatch e1 cases =>
      let* e1' := rename_expr se e1 in
      let* cases' :=
        List.fold_right
          (fun '(pi, ei) acc =>
            let* acc := acc in
            let* ei' := rename_expr se ei in
            ret ((pi, ei') :: acc))
          (ret nil)
          cases 
      in
      ret (EMatch e1' cases')
  | ELetIn x e1 e2 =>
      let* e1' := rename_expr se e1 in
      let* (x', se') := fresh_var se x in
      let* e2' := rename_expr se' e2 in
      ret (ELetIn x' e1' e2')
  | EAttr a e1 =>
      let* e1' := rename_expr se e1 in
      ret (EAttr a e1')
  end.

Definition rename_function (f: function) : function :=
  let params :=
    List.map (fun '(pi, ti) => (Ident.concat "p_" pi, ti)) (fn_params f)
  in
  let (le_init, s_init) :=
    List.fold_left
      (fun '(acc_le, acc_s) '(pi, _) =>
        (STree.set pi (Ident.concat "p_" pi) acc_le, STree.set pi 0 acc_s))
      (fn_params f)
      (STree.empty, STree.empty)
  in
  let (body, _) := rename_expr le_init (fn_body f) s_init in
  {|
    fn_return := fn_return f;
    fn_params := params;
    fn_body := body
  |}.

Definition rename_globdef (def: globdef) : globdef :=
  match def with
  | DefFun x f => DefFun x (rename_function f)
  | _ => def
  end.

Definition rename_program (prog: program) : program :=
  List.map rename_globdef prog.
