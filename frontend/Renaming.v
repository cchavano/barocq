From Coq Require Import String List.
From BarocqComp Require Import Syntax Barocq Benum Ident Maps2.

Open Scope string_scope.

Definition mk_local_id (n: nat) (x: ident) : ident :=
  let ui := Ident.concat "u" (Ident.of_str_nat n) in
  Ident.concat (Ident.concat ui "_") x.

Definition rename_var (le: STree.t nat) (x: ident) : ident :=
  match STree.get x le with
  (* parameter *)
  | Some 0 => Ident.concat "p_" x
  (* local variable *)
  | Some n => mk_local_id n x
  (*global variable *)
  | None => x
  end.

Definition fresh_var (le: STree.t nat) (x: ident) : ident * STree.t nat :=
  let n :=
    match STree.get x le with
    | Some n => n + 1
    | None => 1
    end
  in
  (mk_local_id n x, STree.set x n le).

Fixpoint rename_expr (le: STree.t nat) (e: expr) : expr :=
  match e with
  | ETrue | EFalse
  | EInt32 _ _ | EInt64 _ _
  | EConstr _ => e
  | EVar x =>
      let x' := rename_var le x in
      EVar x'
  | ECast e1 ty =>
      let e1' := rename_expr le e1 in
      ECast e1' ty
  | EUnaryOp op e1 =>
      let e1' := rename_expr le e1 in
      EUnaryOp op e1'
  | EBinaryOp op e1 e2 =>
      let e1' := rename_expr le e1 in
      let e2' := rename_expr le e2 in
      EBinaryOp op e1' e2'
  | EArrayGet e1 e2 =>
      let e1' := rename_expr le e1 in
      let e2' := rename_expr le e2 in
      EArrayGet e1' e2'
  | EArraySet e1 e2 e3 =>
      let e1' := rename_expr le e1 in
      let e2' := rename_expr le e2 in
      let e3' := rename_expr le e3 in
      EArraySet e1' e2' e3'
  | ERecordProj e1 f =>
      let e1' := rename_expr le e1 in
      ERecordProj e1' f
  | ERecordUpdate e1 f e2 =>
      let e1' := rename_expr le e1 in
      let e2' := rename_expr le e2 in
      ERecordUpdate e1' f e2'
  | EApp e1 args =>
      let e1' := rename_expr le e1 in
      let args' := List.map (rename_expr le) args in
      EApp e1' args'
  | EIfThenElse e1 e2 e3 =>
      let e1' := rename_expr le e1 in
      let e2' := rename_expr le e2 in
      let e3' := rename_expr le e3 in
      EIfThenElse e1' e2' e3'
  | EMatch e1 cases =>
      let e1' := rename_expr le e1 in
      let cases' := MapList.map (rename_expr le) cases in
      EMatch e1' cases'
  | ELetIn x e1 e2 =>
      let e1' := rename_expr le e1 in
      let (x', le') := fresh_var le x in
      let e2' := rename_expr le' e2 in
      ELetIn x' e1' e2'
  | EAttr a e1 =>
      let e1' := rename_expr le e1 in
      EAttr a e1'
  end.

Definition rename_function (f: function) : function :=
  let params :=
    List.map (fun '(pi, ti) => (Ident.concat "p_" pi, ti)) (fn_params f)
  in
  let le_init :=
    List.fold_left
      (fun acc '(pi, _) => STree.set pi 0 acc)
      (fn_params f)
      STree.empty
  in
  let body := rename_expr le_init (fn_body f) in
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
