From Coq Require Import PArith List String.
From BarocqComp Require Import Error MapList.

Definition key : Type := positive.

Definition key_eq_dec := Pos.eq_dec.

Inductive field (k: key) (A: Type) : Type :=
  Field : forall (a: A), field k A.

Arguments Field k {A}.

Definition type_of_field (k: key) (fields: list (key * Type)) : Type :=
  find_k key_eq_dec k fields unit.

Definition struct_t (fields: list (key * Type)) : Type :=
  fold_right (fun '(k, t) acc => prod (field k t) acc) unit fields.

Fixpoint proj {fields: list (key * Type)} (st: struct_t fields) (k: key) {struct fields} : res (type_of_field k fields).
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in st. destruct st eqn:Est. destruct f.
    unfold type_of_field. unfold find_k. destruct (key_eq_dec x k) as [Ekx | _].
    + apply (ret a).
    + apply (proj fields' s).
Defined.

Fixpoint update {fields: list (key * Type)} (st: struct_t fields) (k: key) (v: type_of_field k fields) {struct fields} : res (struct_t fields).
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in st. destruct st eqn:Est. destruct f.
    simpl. unfold type_of_field in v; unfold find_k in v; simpl in v.
    destruct (key_eq_dec x k) as [Exk | _].
    + rewrite Exk. apply (ret (Field k v, s)).
    + destruct (update fields' s k v) as [s' | e].
      * apply (ret (Field x a, s')).
      * apply (Error e).
Defined.