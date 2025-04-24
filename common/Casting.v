From compcert Require Import Integers.

(* Casting of booleans *)

Definition bool_to_int (b: bool) : int :=
  if b then Int.one else Int.zero.
  
Definition bool_to_uint (b: bool) : int :=
  bool_to_int b.

Definition bool_to_int64 (b: bool) : int64 :=
  if b then Int64.one else Int64.zero.

Definition bool_to_uint64 (b: bool) : int64 :=
  bool_to_int64 b.

(* Casting of signed 32-bit integers *)

Definition int_to_bool (i: int) : bool :=
  if Int.eq_dec Int.zero i then false else true.

Definition int_to_uint (i: int) : int := i.

Definition int_to_int64 (i: int) : int64 :=
  Int64.repr (Int.signed i).

Definition int_to_uint64 (i: int) : int64 :=
  int_to_int64 i.

(* Casting of unsigned 32-bit integers *)

Definition uint_to_bool (i: int) : bool :=
  int_to_bool i.

Definition uint_to_int (i: int) : int := i.

Definition uint_to_int64 (i: int) : int64 :=
  Int64.repr (Int.unsigned i).

Definition uint_to_uint64 (i: int) : int64 :=
  uint_to_int64 i.

(* Casting of signed 64-bit integergs *)

Definition int64_to_bool (i: int64) : bool :=
  if Int64.eq_dec Int64.zero i then false else true.

Definition int64_to_int (i: int64) : int :=
  Int.repr (Int64.signed i).

Definition int64_to_uint (i: int64) : int :=
  int64_to_int i.

Definition int64_to_uint64 (i: int64) : int64 := i.

(* Casting of unsigned 64-bit integergs *)

Definition uint64_to_bool (i: int64) : bool :=
  int64_to_bool i.

Definition uint64_to_int (i: int64) : int :=
  Int.repr (Int64.unsigned i).

Definition uint64_to_uint (i: int64) : int :=
  uint64_to_int i.

Definition uint64_to_int64 (i: int64) : int64 := i.

