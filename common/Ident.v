From BarocqComp Require Import ExtOrdered.
From Stdlib Require Import PArith String DecimalString.
From compcert Require Import Ctypesdefs.

Definition ident : Type := string.

Definition of_string (str: string) : ident :=
  str.

Definition to_string (i: ident) : string :=
  i.

Definition of_str_nat (n: nat) : ident :=
  let s := NilEmpty.string_of_uint (Nat.to_uint n) in
  of_string s.

Definition of_str_pos (p: positive) : ident :=
  let s := NilEmpty.string_of_uint (Pos.to_uint p) in
  of_string s.

Definition of_pos (p: positive) : ident :=
  Ctypesdefs.string_of_ident p.

Definition to_pos (i: ident) : positive :=
  Ctypesdefs.ident_of_string i.

Definition concat (i1 i2: ident) : ident :=
  let s1 := to_string i1 in
  let s2 := to_string i2 in
  of_string (String.append s1 s2).

Definition eq_dec := string_dec.

Definition eqb : ident -> ident -> bool := Stdlib.Strings.String.eqb.

Definition compare (i1 i2: ident) : comparison :=
  Str.compare i1 i2.

Lemma compare_eq :
  forall (i1 i2: ident), compare i1 i2 = Eq <-> i1 = i2.
Proof.
  apply Str.compare_eq.
Qed.

Lemma compare_trans :
  forall (i1 i2 i3: ident) (c: comparison),
  compare i1 i2 = c -> compare i2 i3 = c -> compare i1 i3 = c.
Proof.
  apply Str.compare_trans.
Qed.

Lemma compare_antisym :
  forall (i1 i2: ident),
  compare i1 i2 = CompOpp (compare i2 i1).
Proof.
  apply Str.compare_antisym.
Qed.
