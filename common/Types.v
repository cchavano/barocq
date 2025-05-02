From Coq Require Import List.
From compcert Require Import Integers.
From BarocqComp Require Import Error Array Struct Ident MapList.

Definition ident := Ident.t.

(* Definition ident := Ident.Extended.t. *)

(** * Syntax of types *)

(** ** Plain types *)

Inductive signedness : Type :=  
  | Signed
  | Unsigned.

Lemma signedness_eq_dec: forall (s1 s2: signedness), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
Defined.

Inductive typ : Type :=
  | TBool : typ
  | TInt32 : signedness -> typ
  | TInt64 : signedness -> typ
  | TArray : typ -> typ
  | TStruct : ident -> list (ident * typ) -> typ
  | TFun : list typ -> typ -> typ.

Fixpoint typ_eq_dec (t1 t2: typ) : { t1 = t2 } + { t1 <> t2 }.
Proof.
  repeat decide equality.
Defined.

(** ** Concrete types *)

Inductive ctyp : Type :=
  | CBool : ctyp
  | CInt32 : signedness -> ctyp
  | CInt64 : signedness -> ctyp
  | CArray : ctyp -> ctyp
  | CStruct : ident -> ctyp
  | CFun : list ctyp -> ctyp -> ctyp.

Definition ctyp_is_prim (ty: ctyp) : bool :=
  match ty with
  | CBool | CInt32 _ | CInt64 _ => true
  | _ => false
  end.

Definition signed_of_int_ctyp (ty: ctyp) : signedness :=
  match ty with
  | CInt32 s
  | CInt64 s => s
  | _ => Signed
  end.

Fixpoint ctyp_eq_dec (t1 t2: ctyp) : { t1 = t2 } + { t1 <> t2 }.
Proof.
  repeat decide equality.
Defined.

Definition cfun_typ (params: list (ident * ctyp)) (tret: ctyp) : ctyp :=
  CFun (map snd params) tret.

(** * Type of a struct field *)

Definition typof_field (k: ident) (fields: list (ident * typ)) : res typ :=
  find_k_err Ident.eq_dec k fields.

Definition ctypof_field (k: ident) (fields: list (ident * ctyp)) : res ctyp :=
  find_k_err Ident.eq_dec k fields.

(** * Conversion of a typ to a Coq Type *)

Section EVALTYP.

  Variable eval_typ : typ -> Type.

  Definition eval_fields_typ (fields: list (ident * typ)) : list (ident * Type) :=
    map_k eval_typ fields.

  Definition eval_structtyp (fields: list (ident * typ)) : Type :=
    struct_t (eval_fields_typ fields).

  Definition eval_funtyp (tparams: list typ) (tret: typ) : Type :=
    fold_right (fun tx acc => (eval_typ tx) -> acc) (res (eval_typ tret)) tparams.

End EVALTYP.

Fixpoint eval_typ (t: typ) : Type :=
  match t with
  | TBool => bool
  | TInt32 _ => int
  | TInt64 _ => int64
  | TArray ta => array (eval_typ ta)
  | TStruct _ fields => eval_structtyp eval_typ fields
  | TFun tparams tret =>
      match tparams with
      | nil => unit -> res (eval_typ tret)
      | _ => eval_funtyp eval_typ tparams tret
      end
  end.

(** ** Type cast w.r.t. type equality *)

Definition typ_cast {t1 t2: typ} (Heq: t1 = t2) (x: eval_typ t1) : eval_typ t2.
Proof.
  subst. exact x.
Defined.