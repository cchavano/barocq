From Coq Require Import List MSetPositive.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Target Error Barray Brecord Benum Ident Maps2 Utils.

(** * Syntax of types *)

(** ** Plain types *)

Inductive signedness : Type :=  
  | Signed
  | Unsigned.

Lemma signedness_eq_dec: forall (s1 s2: signedness), {s1 = s2} + {s1 <> s2}.
Proof.
  intros. destruct s1; destruct s2.
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.

Inductive typ : Type :=
  | TBool : typ
  | TInt32 : signedness -> typ
  | TInt64 : signedness -> typ
  | TArray : typ -> typ
  | TEnum : ident -> list ident -> typ
  | TRecord : ident -> list (ident * typ) -> typ
  | TFun : list typ -> typ -> typ
  | TAbs : ident -> typ.

Fixpoint typ_eq_dec (t1 t2: typ) : { t1 = t2 } + { t1 <> t2 }.
Proof.
  decide equality.
  - apply signedness_eq_dec.
  - apply signedness_eq_dec.
  - apply list_eq_dec. apply Ident.eq_dec. 
  - apply Ident.eq_dec.
  - apply list_eq_dec. decide equality. apply Ident.eq_dec.
  - apply Ident.eq_dec.
  - apply list_eq_dec. apply typ_eq_dec.
  - apply Ident.eq_dec.
Defined.

(** ** Concrete types *)

Inductive btyp : Type :=
  | BBool : btyp
  | BInt32 : signedness -> btyp
  | BInt64 : signedness -> btyp
  | BArray : btyp -> btyp
  | BEnum : ident -> btyp
  | BRecord : ident -> btyp
  | BFun : list btyp -> btyp -> btyp
  | BAbs : ident -> btyp.

Definition btyp_is_prim (ty: btyp) : bool :=
  match ty with
  | BBool | BInt32 _ | BInt64 _ | BEnum _ => true
  | _ => false
  end.

Definition signed_of_int_btyp (ty: btyp) : signedness :=
  match ty with
  | BInt32 s
  | BInt64 s => s
  | _ => Signed
  end.

Fixpoint btyp_eq_dec (t1 t2: btyp) : { t1 = t2 } + { t1 <> t2 }.
Proof.
  decide equality.
  - apply signedness_eq_dec.
  - apply signedness_eq_dec.
  - apply Ident.eq_dec.
  - apply Ident.eq_dec.
  - apply list_eq_dec. apply btyp_eq_dec.
  - apply Ident.eq_dec.
Defined.

Definition mk_fun_btyp {A: Type} (params: list (A * btyp)) (tret: btyp) : btyp :=
  BFun (List.map snd params) tret.

(** * Type of a record field *)

Definition typof_field (k: ident) (fields: smaplist typ) : res typ :=
  MapList.find_err Ident.eq_dec k fields.

Definition btypof_field (k: ident) (fields: smaplist btyp) : res btyp :=
  MapList.find_err Ident.eq_dec k fields.

(* Type for array indexes *)

Definition arr_index_btyp (arch: Target.archi): btyp :=
  match arch with
  | Ptr32 => BInt32 Unsigned
  | Ptr64 => BInt64 Unsigned
  end.

Definition arr_index_typ (arch: Target.archi) : typ :=
  match arch with
  | Ptr32 => TInt32 Unsigned
  | Ptr64 => TInt64 Unsigned
  end.

(** * Conversion of a typ to a Coq Type *)

Section EVALTYP.

  Variable eval_typ : typ -> Type.

  Definition eval_fields_typ (fields: smaplist typ) : smaplist Type :=
    MapList.map eval_typ fields.

  Definition eval_recordtyp (fields: smaplist typ) : Type :=
    record (eval_fields_typ fields).

  Definition eval_funtyp (tparams: list typ) (tret: typ) : Type :=
    List.fold_right (fun tx acc => (eval_typ tx) -> acc) (res (eval_typ tret)) tparams.

End EVALTYP.

Fixpoint eval_typ (am: PMap.t Type) (t: typ) : Type :=
  match t with
  | TBool => bool
  | TInt32 _ => int
  | TInt64 _ => int64
  | TArray ta => array (eval_typ am ta)
  | TRecord _ fields => eval_recordtyp (eval_typ am) fields
  | TEnum _ elems => enum elems
  | TFun tparams tret =>
      match tparams with
      | nil => unit -> res (eval_typ am tret)
      | _ => eval_funtyp (eval_typ am) tparams tret
      end
  | TAbs ta => SMap.get ta am 
  end.

(** ** Type cast w.r.t. type equality *)

Definition typ_cast {t1 t2: typ} (am: SMap.t Type) (Heq: t1 = t2) (x: eval_typ am t1) : eval_typ am t2.
Proof.
  subst t1. exact x.
Defined.

(** * Algebraic Data Type definitions for Barocq and typing environments  *)

Inductive adt_definition (A: Type) : Type :=
  | Adt_enum (elems: list ident) : adt_definition A
  | Adt_record (fields: list (ident * A)) : adt_definition A.

Arguments Adt_enum {A}.
Arguments Adt_record {A}.