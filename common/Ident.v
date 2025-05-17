From Coq Require Import PArith String DecimalString.
From compcert Require Import Ctypesdefs.

Definition t : Type := positive.

Definition of_string (str: string) : t :=
  Ctypesdefs.ident_of_string str.

Definition to_string (i: t) : string :=
  Ctypesdefs.string_of_ident i.

Definition of_str_nat (n: nat) : t :=
  let s := NilEmpty.string_of_uint (Nat.to_uint n) in
  of_string s.

Definition of_str_pos (p: positive) : t :=
  let s := NilEmpty.string_of_uint (Pos.to_uint p) in
  of_string s.

Definition concat (i1 i2: t) : t :=
  let s1 := to_string i1 in
  let s2 := to_string i2 in
  of_string (String.append s1 s2).

Definition prefix_with (str: string) (i: t) : t :=
  let s := to_string i in
  of_string (String.append str s).

Definition eq_dec := Pos.eq_dec.
