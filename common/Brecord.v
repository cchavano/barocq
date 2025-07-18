From Coq Require Import PArith List String.
From BarocqComp Require Import Error MapList.

Definition key : Type := positive.

Definition key_eq_dec := Pos.eq_dec.

Inductive field (k: key) (A: Type) : Type :=
  Field : forall (a: A), field k A.

Arguments Field k {A}.

Definition type_of_field (k: key) (fields: list (key * Type)) : Type :=
  find_k key_eq_dec k fields unit.

Definition record (fields: list (key * Type)) : Type :=
  fold_right (fun '(k, t) acc => prod (field k t) acc) unit fields.

Fixpoint proj {fields: list (key * Type)} (rc: record fields) (k: key) {struct fields} : res (type_of_field k fields).
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in rc. destruct rc eqn:Erc. destruct f.
    unfold type_of_field. unfold find_k. destruct (key_eq_dec x k) as [Ekx | _].
    + apply (ret a).
    + apply (proj fields' r).
Defined.

Fixpoint update {fields: list (key * Type)} (rc: record fields) (k: key) (v: type_of_field k fields) {struct fields} : res (record fields).
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in rc. destruct rc eqn:Est. destruct f.
    simpl. unfold type_of_field in v; unfold find_k in v; simpl in v.
    destruct (key_eq_dec x k) as [Exk | _].
    + rewrite Exk. apply (ret (Field k v, r)).
    + destruct (update fields' r k v) as [r' | e].
      * apply (ret (Field x a, r')).
      * apply (Error e).
Defined.