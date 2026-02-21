From Coq Require Import BinIntDef.
From compcert Require Import Integers.
From BarocqComp Require Import OptionMonad.

Local Open Scope bool_scope.

Module I32.

  Definition div (x y: int) : option int :=
    if Int.eq y Int.zero
       || Int.eq x (Int.repr Int.min_signed) && Int.eq y Int.mone
    then fail
    else ret (Int.divs x y).

  Definition mod (x y: int) : option int :=
    if Int.eq y Int.zero
       || Int.eq x (Int.repr Int.min_signed) && Int.eq y Int.mone
    then fail
    else ret (Int.mods x y).

  Definition of_bool (b: bool) : int :=
    if b then Int.one else Int.zero.

  Definition to_bool (x: int) : bool :=
    if Int.eq x Int.zero then false else true.

  Definition of_u32 (x: int) : int := x.

  Definition of_i64 (x: int64) : int :=
    Int.repr (Int64.signed x).

  Definition of_u64 (x: int64) : int :=
    Int.repr (Int64.unsigned x).

  Definition to_nat (x: int) : nat :=
    Z.to_nat (Int.signed x).

End I32.

Module U32.

  Definition div (x y: int) : option int :=
    if Int.eq y Int.zero then fail
    else ret (Int.divu x y).
   
  Definition mod (x y: int) : option int :=
    if Int.eq y Int.zero then fail
    else ret (Int.modu x y).

  Definition of_bool (b: bool) : int :=
    if b then Int.one else Int.zero.

  Definition to_bool (x: int) : bool :=
    if Int.eq x Int.zero then false else true.

  Definition of_i32 (x: int) : int := x.

  Definition of_i64 (x: int64) : int :=
    Int.repr (Int64.signed x).

 Definition of_u64 (x: int64) : int :=
    Int.repr (Int64.unsigned x).

End U32.

Module I64.

  Definition div (x y: int64) : option int64 :=
    if Int64.eq y Int64.zero
       || Int64.eq x (Int64.repr Int64.min_signed) && Int64.eq y Int64.mone
    then fail
    else ret (Int64.divs x y).

  Definition mod (x y: int64) : option int64 :=
    if Int64.eq y Int64.zero
       || Int64.eq y (Int64.repr Int64.min_signed) && Int64.eq y Int64.mone
    then fail
    else ret (Int64.mods x y).

  Definition of_bool (b: bool) : int64 :=
    if b then Int64.one else Int64.zero.

  Definition to_bool (x: int64) : bool :=
    if Int64.eq x Int64.zero then false else true.

  Definition of_u64 (x: int64) : int64 := x.

  Definition of_i32 (x: int) : int64 :=
    Int64.repr (Int.signed x).
 
  Definition of_u32 (x: int) : int64 :=
    Int64.repr (Int.unsigned x).

End I64.

Module U64.

  Definition div (x y: int64) : option int64 :=
    if Int64.eq y Int64.zero then fail
    else ret (Int64.divu x y).

  Definition mod (x y: int64) : option int64 :=
    if Int64.eq y Int64.zero then fail
    else ret (Int64.modu x y).

  Definition of_bool (b: bool) : int64 :=
    if b then Int64.one else Int64.zero.

  Definition to_bool (x: int64) : bool :=
    if Int64.eq x Int64.zero then false else true.

  Definition of_i64 (x: int64) : int64 := x.

  Definition of_i32 (x: int) : int64 :=
    Int64.repr (Int.signed x).

  Definition of_u32 (x: int) : int64 :=
    Int64.repr (Int.unsigned x).

  Definition to_nat (x: int64) : nat :=
    Z.to_nat (Int64.unsigned x).

End U64.
