From BarocqComp Require BarocqVC.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Import Ltac2 Control.
Import Bool.BoolNotations.

(** [below_binder f] takes a constr that is either a Lambda or a Prod and returns the subterm.
    This is to circumvent a restriction of [lazy_match!] which does not go under binders *)
Ltac2 below_binder f :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Lambda _ c => c
  | Constr.Unsafe.Prod _ c => c
  |  _  => Control.throw (Tactic_failure (Some (Message.of_string "Not a binder")))
  end.

(** [get_function t] returns the name of the Rocq function
    that is checked for equality by correspondence theorem *)
Ltac2 rec get_function t :=
  lazy_match! t with
  | @ex _ ?p => get_function p
  | fun _  => _ => get_function (below_binder t)
  | forall _ , _ => get_function (below_binder t)
  | _ /\ ?b       => get_function b
  | _ = ?a => get_function a
  | ?f _  => get_function f
  |  ?x   =>  x
  end.

(** [get_function_string t] returns the deep name of the function *)
Ltac2 rec get_function_string t :=
  lazy_match! t with
  | @ex _ ?p =>  get_function_string (below_binder p)
  | _ ?a = _ /\ _  => a
  end.

(** [get_function_typ t] returns the deep type of the function *)
Ltac2 rec get_function_typ t :=
  lazy_match! t with
  | exists (_:(_ _ ?t)), _ =>  t
  end.

(** [get_function_spec ()] calls the previous and returns a triplet. *)
Ltac2 get_function_spec () :=
  let g := Control.goal () in
  let fname := get_function g in
  let fstring := get_function_string g in
  let ty      := get_function_typ g in
  (fstring,ty,fname).

(** [has_property ge] takes the initial global environment
    and asserts that the deep function and the shallow function has the same value. *)
Ltac2 has_property id ge abs_typ_impl :=
  let ge := Control.hyp ge in
  let (str,ty,f) :=  get_function_spec () in
  let c := constr:(BarocqVC.has_property $abs_typ_impl $ge ($str, (Barocq.Val $abs_typ_impl $ty $f))) in
  Std.assert (Std.AssertType (Init.Some (Std.IntroNaming (Std.IntroFresh id))) c  Init.None).
