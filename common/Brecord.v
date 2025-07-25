From Coq Require Import PArith List String.
From BarocqComp Require Import Error Maps2 Ident.

Definition key : Type := Ident.t.

Inductive field (k: key) (A: Type) : Type :=
  Field : forall (a: A), field k A.

Arguments Field k {A}.

Definition type_of_field (k: key) (fields: SMapList.t Type) : Type :=
  SMapList.find k fields unit.

Definition record (fields: SMapList.t Type) : Type :=
  fold_right (fun '(k, t) acc => prod (field k t) acc) unit fields.

Fixpoint proj {fields: SMapList.t Type} (rc: record fields) (k: key) {struct fields} : res (type_of_field k fields).
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in rc. destruct rc eqn:Erc. destruct f.
    unfold type_of_field. unfold SMapList.find. destruct (SMapList.key_eq x k) as [Ekx | _].
    + apply (ret a).
    + apply (proj fields' r).
Defined.

Fixpoint update {fields: SMapList.t Type} (rc: record fields) (k: key) (v: type_of_field k fields) {struct fields} : res (record fields).
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in rc. destruct rc eqn:Est. destruct f.
    simpl. unfold type_of_field in v; unfold SMapList.find in v; simpl in v.
    destruct (SMapList.key_eq x k) as [Exk | _].
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