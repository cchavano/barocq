From Coq Require Import List.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Error Array Brecord Ident MapList.

Definition ident := Ident.t.

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
  | TRecord : ident -> list (ident * typ) -> typ
  | TFun : list typ -> typ -> typ
  | TAbs : ident -> typ.

Fixpoint typ_eq_dec (t1 t2: typ) : { t1 = t2 } + { t1 <> t2 }.
Proof.
  repeat decide equality.
Defined.

(** ** Concrete types *)

Inductive btyp : Type :=
  | BBool : btyp
  | BInt32 : signedness -> btyp
  | BInt64 : signedness -> btyp
  | BArray : btyp -> btyp
  | BRecord : ident -> btyp
  | BFun : list btyp -> btyp -> btyp
  | BAbs : ident -> btyp.

Definition btyp_is_prim (ty: btyp) : bool :=
  match ty with
  | BBool | BInt32 _ | BInt64 _ => true
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
  repeat decide equality.
Defined.

Definition mk_fun_btyp {A: Type} (params: list (A * btyp)) (tret: btyp) : btyp :=
  BFun (List.map snd params) tret.

(** * Type of a struct field *)

Definition typof_field (k: ident) (fields: list (ident * typ)) : res typ :=
  find_k_err Ident.eq_dec k fields.

Definition btypof_field (k: ident) (fields: list (ident * btyp)) : res btyp :=
  find_k_err Ident.eq_dec k fields.

(* Type for array indexes *)

Definition arr_index_btyp : btyp :=
  if Archi.ptr64 then BInt64 Unsigned else BInt32 Unsigned.

Definition arr_index_typ : typ :=
  if Archi.ptr64 then TInt64 Unsigned else TInt32 Unsigned.

(** * Conversion of a typ to a Coq Type *)

Section EVALTYP.

  Variable eval_typ : typ -> Type.

  Definition eval_fields_typ (fields: list (ident * typ)) : list (ident * Type) :=
    map_k eval_typ fields.

  Definition eval_recordtyp (fields: list (ident * typ)) : Type :=
    record_t (eval_fields_typ fields).

  Definition eval_funtyp (tparams: list typ) (tret: typ) : Type :=
    fold_right (fun tx acc => (eval_typ tx) -> acc) (res (eval_typ tret)) tparams.

End EVALTYP.

Fixpoint eval_typ (am: PMap.t Type) (t: typ) : Type :=
  match t with
  | TBool => bool
  | TInt32 _ => int
  | TInt64 _ => int64
  | TArray ta => array (eval_typ am ta)
  | TRecord _ fields => eval_recordtyp (eval_typ am) fields
  | TFun tparams tret =>
      match tparams with
      | nil => unit -> res (eval_typ am tret)
      | _ => eval_funtyp (eval_typ am) tparams tret
      end
  | TAbs t => PMap.get t am 
  end.

(** ** Type cast w.r.t. type equality *)

Definition typ_cast {t1 t2: typ} (am: PMap.t Type) (Heq: t1 = t2) (x: eval_typ am t1) : eval_typ am t2.
Proof.
  subst. exact x.
Defined.