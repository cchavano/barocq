From Coq Require Import List Bool.
From compcert Require Import Integers.
From BarocqComp Require Import Ident Intop Error Utils.

Import ListNotations.

Inductive constr : ident -> Type :=
  Constr : forall (i: ident), constr i.

Lemma constr_eq_dec :
  forall {i: ident} (x y: constr i), {x = y} + {x <> y}.
Proof.
  intros. left. destruct x; destruct y. reflexivity.
Defined.

Fixpoint enum (elems: list ident) : Type :=
  match elems with
  | nil => False
  | ei :: nil => constr ei
  | ei :: elems' => constr ei + (enum elems')
  end.

Lemma enum_eq_dec :
  forall {elems: list ident} (x y: enum elems), {x = y} + {x <> y}.
Proof.
  induction elems as [| e0 elems0]; intros.
  - destruct x.
  - simpl in x; simpl in y. destruct elems0 as [| e1 elems1].
    + apply constr_eq_dec.
    + destruct x; destruct y; try (right; discriminate).
      * decide equality. apply constr_eq_dec.
      * decide equality. apply constr_eq_dec.
Defined.

Definition enum_eq {elems: list ident} (x y: enum elems) :=
  if enum_eq_dec x y then true else false.

Definition enum_neq {elems: list ident} (x y: enum elems) :=
 if enum_eq_dec x y then false else true.

Fixpoint make_enum (elems: list ident) (i: ident) : res (enum elems) :=
  match elems as l0 return (res (enum l0)) with
  | [] => fail
  | s0 :: l0 =>
      if Ident.eq_dec i s0
      then
       ret match l0 as l2 return enum (s0:: l2) with
         | [] => Constr s0
         | s3 :: l2 => inl (Constr s0)
         end
      else
        match make_enum l0 i with
        | OK e =>
            ret
              (match l0 as l2 return (enum l2 -> enum (s0 :: l2)) with
               | [] => fun e1 : enum [] => False_rect (enum [s0]) e1
               | s3 :: l2 => fun e1 : enum (s3 :: l2) => inr e1
               end e)
       | Error e => Error e
       end
  end.

Definition ident_of_constr {elems: list ident} (e: enum elems) : ident.
  induction elems as [| e0 elems0].
  - destruct e.
  - destruct elems0.
    + apply e0.
    + destruct e.
      * apply e0.
      * apply (IHelems0 e).
Defined.

Definition to_i32 {elems: list ident} (e: enum elems) : int :=
  let fix aux (elems0: list ident) (ctr: int) : int :=
    match elems0 with
    | nil => Int.mone
    | ei :: elems0' =>
        if Ident.eq_dec ei (ident_of_constr e) then ctr
        else aux elems0' (Int.add ctr Int.one)
    end
  in
  aux elems Int.zero.

Definition of_i32 (elems: list ident) (i: int) : res (enum elems) :=
  if Int.cmp Clt i Int.zero
     || Nat.leb (List.length elems) (I32.to_nat i) then fail
  else
    let* ei := list_nth_err elems (I32.to_nat i) in
    make_enum elems ei.

Inductive pattern : Type := 
  | PIdent (i: ident) : pattern
  | PWildcard : pattern.

Fixpoint match_with {elems: list ident} {A: Type} (e: enum elems) (cases: list (pattern * A)) : res A :=
  match cases with
  | nil => fail
  | (ei, ai) :: cases' =>
      match ei with
      | PIdent i =>
          if Ident.eq_dec (ident_of_constr e) i then (ret ai)
          else match_with e cases'
      | PWildcard => ret ai
      end
  end.

Fixpoint match_with_err {elems: list ident} {A: Type} (e: enum elems) (cases: list (pattern * res A)) : res A :=
  match cases with
  | nil => fail
  | (ei, ai) :: cases' =>
      match ei with
      | PIdent i =>
          if Ident.eq_dec (ident_of_constr e) i then ai
          else match_with_err e cases'
      | PWildcard => ai
      end
  end.