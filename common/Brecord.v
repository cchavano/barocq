From Coq Require Import PArith List String.
From BarocqComp Require Import Error Maps2 Ident.

Definition key : Type := ident.

Definition key_eq := Ident.eq_dec.

Inductive field (k: key) (A: Type) : Type :=
  Field : forall (a: A), field k A.

Arguments Field k {A}.

Definition type_of_field (k: key) (fields: smaplist Type) : Type :=
  MapList.find key_eq k fields unit.

Definition record (fields: smaplist Type) : Type :=
  fold_right (fun kt acc => prod (field (fst kt) (snd kt)) acc) unit fields.

Fixpoint proj {fields: smaplist Type} (rc: record fields) (k: key) {struct fields} : res (type_of_field k fields).
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in rc. destruct rc eqn:Erc. destruct f.
    unfold type_of_field. unfold MapList.find.
    destruct (key_eq x k) as [Ekx | _].
    + apply (ret a).
    + apply (proj fields' r).
Defined.

Fixpoint update {fields: smaplist Type} (rc: record fields) (k: key) (v: type_of_field k fields) {struct fields} : res (record fields).
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in rc. destruct rc eqn:Est. destruct f.
    simpl. unfold type_of_field in v; unfold MapList.find in v; simpl in v.
    destruct (key_eq x k) as [Exk | _].
    + rewrite Exk. apply (ret (Field k v, r)).
    + destruct (update fields' r k v) as [r' | e].
      * apply (ret (Field x a, r')).
      * apply (Error e).
Defined.

Ltac destruct_record r :=
  match type of r with
  | (record _)%type =>
      simpl in r;
      destruct_record r 
  | (field _ _ * _)%type =>
      let f := fresh "f0" in (
      destruct r as [[f] r];
      destruct_record r)
  | unit => destruct r
  end.
