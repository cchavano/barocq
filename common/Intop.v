From Stdlib Require Import BinIntDef.
From compcert Require Import Integers.
From BarocqComp Require Import Option.

Local Open Scope bool_scope.

Module Wordsize_Int16.
  Definition wordsize := 16%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize. congruence. Qed.
End Wordsize_Int16.

Strategy opaque [Wordsize_Ptrofs.wordsize].

Module Intsize := Ptrofs.
Module Int16.
  Include Integers.Make(Wordsize_Int16).
End Int16.

Notation i8 := (Byte.int : Type).

Notation u8 := (Byte.int : Type).

Notation i16 := (Int16.int : Type).

Notation u16 := (Int16.int : Type).

Notation i32 := (Int.int : Type).

Notation u32 := (Int.int : Type).

Notation i64 := (Int64.int : Type).

Notation u64 := (Int64.int:Type).

Notation isize := Intsize.int.

Notation usize := Intsize.int.

Module Type INTTYPE.
  Parameter modulus : Z.
  Record int: Type := mkint { intval: Z; intrange: (Z.lt (-1)%Z intval) /\ (Z.lt intval modulus)}.
  Parameter zero : int.
  Parameter one : int.
  Parameter mone : int.
  Parameter repr : Z -> int.
  Parameter signed : int -> Z.
  Parameter unsigned : int -> Z.
  Parameter eq : int -> int -> bool.
  Parameter divs : int -> int -> int.
  Parameter divu : int -> int -> int.
  Parameter mods : int -> int -> int.
  Parameter modu : int -> int -> int.
  Parameter min_signed : Z.
End INTTYPE.

Module Make(INT: INTTYPE).

  Definition of_Z (x: Z) : INT.int := INT.repr x.

  Definition of_bool (b: bool) : INT.int :=
    if b then INT.one else INT.zero.

  Definition to_bool (x: INT.int) : bool :=
    if INT.eq x INT.zero then false else true.

  Definition of_i8 (x: i8) : INT.int :=
    INT.repr (Byte.signed x).

  Definition of_u8 (x: u8) : INT.int :=
    INT.repr (Byte.unsigned x).

  Definition of_i16 (x: i16) : INT.int :=
    INT.repr (Int16.signed x).

  Definition of_u16 (x: u16) : INT.int :=
    INT.repr (Int16.unsigned x).

  Definition of_i32 (x: i32) : INT.int :=
    INT.repr (Int.signed x).

  Definition of_u32 (x: u32) : INT.int :=
    INT.repr (Int.unsigned x).

  Definition of_i64 (x: i64) : INT.int :=
    INT.repr (Int64.signed x).

  Definition of_u64 (x: u64) : INT.int :=
    INT.repr (Int64.unsigned x).

  Definition of_isize (x: isize) : INT.int :=
    INT.repr (Intsize.signed x).

  Definition of_usize (x: usize) : INT.int :=
    INT.repr (Intsize.unsigned x).

End Make.

Module MakeS(INT: INTTYPE).
  Include Make(INT).

  Definition to_Z (x: INT.int) := INT.signed x.

  Definition div (x y: INT.int) : option INT.int :=
    if INT.eq y INT.zero
        || INT.eq x (INT.repr INT.min_signed) && INT.eq y INT.mone
    then fail
    else ret (INT.divs x y).

  Definition mod (x y: INT.int) : option INT.int :=
    if INT.eq y INT.zero
        || INT.eq x (INT.repr INT.min_signed) && INT.eq y INT.mone
    then fail
    else ret (INT.mods x y).


  Definition to_nat (x: INT.int) : nat :=
    Z.to_nat (INT.signed x).

End MakeS.

Module MakeU(INT: INTTYPE).
  Include Make(INT).

  Definition to_Z (x: INT.int) := INT.unsigned x.

  Definition div (x y: INT.int) : option INT.int :=
    if INT.eq y INT.zero then fail
    else ret (INT.divu x y).

  Definition mod (x y: INT.int) : option INT.int :=
    if INT.eq y INT.zero then fail
    else ret (INT.modu x y).

  Definition to_nat (x: INT.int) : nat :=
    Z.to_nat (INT.unsigned x).

End MakeU.

Module I8 := MakeS(Byte).
Module U8 := MakeS(Byte).
Module I16 := MakeS(Int16).
Module U16 := MakeU(Int16).
Module I32 := MakeS(Int).
Module U32 := MakeU(Int).
Module I64 := MakeS(Int64).
Module U64 := MakeU(Int64).
Module ISIZE := MakeS(Intsize).
Module USIZE := MakeU(Intsize).

(* Notations *)
Module IntopNotations.
  
Infix "+₆₄" := Int64.add (at level 50,left associativity).
Infix "+₃₂" := Int.add (at level 50,left associativity).
Infix "-₆₄" := Int64.sub (at level 50,left associativity).
Infix "-₃₂" := Int.sub (at level 50,left associativity).
Infix "*₆₄" := Int64.mul (at level 40,left associativity).
Infix "*₃₂" := Int.mul (at level 40,left associativity).
Infix "modu₆₄" := U64.mod (at level 40,left associativity).
Infix "modu₃₂" := U32.mod (at level 40,left associativity).
Infix "mods₆₄" := I64.mod (at level 40,left associativity).
Infix "mods₃₂" := I32.mod (at level 40,left associativity).

Infix "<<₃₂"  := Int.shl (at level 39,left associativity).
Infix "<<₆₄"  := Int64.shl (at level 39,left associativity).

Infix ">>₃₂"  := Int.shr (at level 39,left associativity).
Infix ">>u₃₂" := Int.shru (at level 39,left associativity).
Infix ">>₆₄"  := Int64.shr (at level 39,left associativity).
Infix ">>u₆₄" := Int64.shru (at level 39,left associativity).

Infix "&₃₂"    := Int.and (at level 40,left associativity).
Infix "&₆₄"    := Int64.and (at level 40,left associativity).
Infix "^₃₂"    := Int.xor (at level 45,left associativity).
Infix "^₆₄"    := Int64.xor (at level 45,left associativity).
Infix "|₃₂"    := Int.or (at level 50,left associativity).
Infix "|₆₄"    := Int64.or (at level 50,left associativity).

Notation "X 'UL'" := (Int64.repr X).
Notation "X 'L'" := (Int64.repr X).
Notation "X 'U'" := (Int.repr X).
Coercion Int.repr : Z >-> Int.int.

End IntopNotations.
