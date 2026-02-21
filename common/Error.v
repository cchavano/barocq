From BarocqComp Require Import Monads.

Export MonError.

Open Scope error_monad_scope.

Ltac monadInv H :=
  match type of H with
  | err_of_opt ?F = Error _ =>
      let FEQ := fresh "FEQ" in
      destruct F eqn:FEQ; try discriminate; clear H
  | err_of_opt ?F = OK _ =>
      let FEQ := fresh "FEQ" in
      destruct F eqn:FEQ; try discriminate;
      inversion H; clear H; subst
  | _ => Res.monadInv H
  end.
