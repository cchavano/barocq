From Stdlib Require Import String List.
From BarocqComp Require Import StateMonads Syntax Barocq Benum Ident Maps2.

Open Scope string_scope.

(** * Rename local variables and parameters with fresh identifiers. *)

Module STATE <: STATE_TYPE.
  Definition t := STree.t nat.
End STATE.

Module MonRename := MonState(STATE).

Import MonRename.

Local Open Scope state_monad_scope.

Definition mk_local_id (n: nat) (x: ident) : ident :=
  let ui := Ident.concat "u" (Ident.of_str_nat n) in
  Ident.concat (Ident.concat ui "_") x.

Definition rename_var (se: STree.t ident) (x: ident) : ident :=
  match STree.get x se with
  | Some x' => x'
  | None => x
  end.

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


Fixpoint rename_atom (se: STree.t ident) (e: atom) :  atom :=
  match e with
  | ATrue | AFalse
  | AInt32 _ _ | AInt64 _ _
  | AConstr _ _ _  =>  e
  | AVar x ty =>
      let x' := rename_var se x in  (AVar x' ty)
  | ACast e1 ty =>
      let e1' := rename_atom se e1 in
       (ACast e1' ty)
  | AUnaryOp op e1 ty =>
      let e1' := rename_atom se e1 in
      AUnaryOp op e1' ty
  | ABinaryOp op e1 e2 ty=>
      let e1' := rename_atom se e1 in
      let e2' := rename_atom se e2 in
      ABinaryOp op e1' e2' ty
  | AArrayGet e1 e2 ly ty =>
      let e1' := rename_atom se e1 in
      let e2' := rename_atom se e2 in
      AArrayGet e1' e2' ly ty
  | ARecordProj e1 f ly bt =>
      let e1' := rename_atom se e1 in
      ARecordProj e1' f ly bt
  | APureCall f bt args bty =>
      let args' := List.map (rename_atom se) args in
      APureCall f bt args' bty
  end.

Section RenameBinding.

  Variable rename_expr : STree.t ident -> STree.t ident -> expr -> MonRename.M expr.


  Fixpoint rename_bindings (sfi: STree.t ident) (si:STree.t ident) (se:STree.t ident)   (l : list (Syntax.ident * expr)) :
    MonRename.M (STree.t ident * list (Syntax.ident * expr)) :=
    match l with
    | nil => sret (se,nil)
    | (x,e)::l =>
        (* rhs are rename using the current mapping - this is a parallel assignment *)
        do e' <- rename_expr sfi si e ;
        do (x', se') <- fresh_var se x;
        do (se'', l) <- rename_bindings sfi si se' l ;
        sret(se'',(x',e')::l)
    end.

  Fixpoint rename_actr (sf : STree.t ident) (se: STree.t ident) (l : list (Syntax.ident * expr)) :
    MonRename.M (list (Syntax.ident * expr)) :=
    match l with
    | nil => sret nil
    | (x,e)::l => do e' <- rename_expr sf se e ;
                  let x' := rename_var sf x in
                   do l <- rename_actr sf se l ;
                   sret((x',e')::l)
    end.


End RenameBinding.


Fixpoint rename_expr (sf: STree.t ident) (se: STree.t ident) (e: expr) : MonRename.M expr :=
  match e with
  | ETrue | EFalse
  | EInt32 _ _ | EInt64 _ _
  | EConstr _ => sret e
  | EVar x =>
      let x' := rename_var se x in
      sret (EVar x')
  | ECast e1 ty =>
      do e1' <- rename_expr sf se e1;
      sret (ECast e1' ty)
  | EUnaryOp op e1 =>
      do e1' <- rename_expr sf se e1;
      sret (EUnaryOp op e1')
  | EBinaryOp op e1 e2 =>
      do e1' <- rename_expr sf se e1;
      do e2' <- rename_expr sf se e2;
      sret (EBinaryOp op e1' e2')
  | EArrayGet e1 e2 =>
      do e1' <- rename_expr sf se e1;
      do e2' <- rename_expr sf se e2;
      sret (EArrayGet e1' e2')
  | EArraySet e1 e2 e3 =>
      do e1' <- rename_expr sf se e1;
      do e2' <- rename_expr sf se e2;
      do e3' <- rename_expr sf se e3;
      sret (EArraySet e1' e2' e3')
  | ERecordProj e1 f =>
      do e1' <- rename_expr sf se e1;
      sret (ERecordProj e1' f)
  | ERecordUpdate e1 f e2 =>
      do e1' <- rename_expr sf se e1;
      do e2' <- rename_expr sf se e2;
      sret (ERecordUpdate e1' f e2')
  | EApp e1 args =>
      do e1' <- rename_expr sf se e1;
      do args' <-
        List.fold_right
          (fun e acc =>
            do acc <- acc;
            do e' <- rename_expr sf se e;
            sret (e' :: acc))
          (sret nil)
          args;
      sret (EApp e1' args')
  | EIfThenElse e1 e2 e3 =>
      do e1' <- rename_expr sf se e1;
      do e2' <- rename_expr sf se e2;
      do e3' <- rename_expr sf se e3;
      sret (EIfThenElse e1' e2' e3')
  | EMatch e1 cases =>
      do e1' <- rename_expr sf se e1;
      do cases' <-
        List.fold_right
          (fun '(pi, ei) acc =>
            do acc <- acc;
            do ei' <- rename_expr sf se ei;
            sret ((pi, ei') :: acc))
          (sret nil)
          cases;
      sret (EMatch e1' cases')
  | ELetIn x e1 e2 =>
      do e1' <- rename_expr sf se e1;
      do (x', se') <- fresh_var se x;
      do e2' <- rename_expr sf se' e2;
      sret (ELetIn x' e1' e2')
  | EActR l => do l' <- rename_actr rename_expr sf se l ;
               sret (EActR l')
  | ELetW init cond decr body e2 =>
      do (sf',init') <- rename_bindings rename_expr sf se se init;
      do cond' <- rename_expr sf sf' cond;
      do decr' <- rename_expr sf sf' decr;
      do body' <- rename_expr sf' sf' body;
      do e2'   <- rename_expr sf sf' e2;
      sret (ELetW init' cond' decr' body' e2')
  | EAttr a e1 =>
      do e1' <- rename_expr sf se e1;
      sret (EAttr a e1')
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
  let (body, _) := rename_expr STree.empty le_init (fn_body f) s_init in
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
