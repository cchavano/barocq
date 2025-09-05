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
  - simpl in rc. destruct rc. destruct f.
    unfold type_of_field. unfold MapList.find.
    destruct (key_eq x k).
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

(** Proof principle to destruct records *)
Fixpoint decomp_fields (fields : smaplist Type)  {struct fields} : forall (P : record fields -> Prop), Prop :=
  match fields as fd' return (record fd' -> Prop) -> Prop with
  | nil => fun P => P tt
  | (i,v)::fields' => fun P => forall v, decomp_fields fields' (fun r' => P (Field i v, r'))
  end.

Lemma decomp_fields_sound : forall fields (P : record fields -> Prop),
    decomp_fields fields P ->
    forall r, P r.
Proof.
  induction fields; simpl.
  - intros. destruct r. apply H.
  -  intros. destruct a.
     destruct r. simpl in f. destruct f.
     apply IHfields with (r:=r); auto.
Qed.

Ltac apply_decomp_field :=
  let b := fresh "R" in
  intro b; pattern b;
  let pred := fresh "PRED" in
  match goal with
  | |- ?P ?X => set (pred := P) ;
                apply decomp_fields_sound;
                match goal with
                | |- decomp_fields ?F ?P =>
                    unfold F;
                    cbv beta iota delta [decomp_fields ];
                    unfold snd ; intros;
                    unfold pred;clear pred
                end
                end.
