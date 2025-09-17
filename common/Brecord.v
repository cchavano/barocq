From Coq Require Import PArith List String.
From BarocqComp Require Import Error Maps2 Ident Utils.

Definition key : Type := ident.

Definition key_eq := Ident.eq_dec.

Inductive field (k: key) (A: Type) : Type :=
  Field : forall (a: A), field k A.

Arguments Field k {A}.

Definition type_of_field (k: key) (fields: smaplist Type) : Type :=
  MapList.find key_eq k fields False.

Definition proj_field {k:key} {T:Type} (fd:field k T) : T :=
  match fd with
  | Field _ x => x
  end.

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


Definition good_proj {A: Type} (k:key) (fields : smaplist A) :=
  existsb (String.eqb k) (map fst fields).

Lemma good_proj_nil : forall {A: Type} {k}, @good_proj A k nil = true -> False.
Proof.
  discriminate.
Qed.

Fixpoint typeof_field (k: key) (fields: smaplist Type) : forall (GP : good_proj k fields = true), Type.
Proof.
  destruct fields.
  - intro. exfalso. apply (good_proj_nil GP).
  - change (good_proj k (p::fields)) with (orb (String.eqb k (fst p)) (good_proj k fields)).
    destruct (String.eqb k (fst p)).
    + intro. exact (snd p).
    + unfold orb.
      apply (typeof_field k fields).
Defined.

Fixpoint project {fields:smaplist Type} (rc:record fields) (k:key) : forall (GP : good_proj k fields = true), typeof_field k fields GP.
Proof.
  destruct fields.
  - intros. exfalso.
    apply (good_proj_nil GP).
  - change (good_proj k (p::fields)) with (orb (String.eqb k (fst p)) (good_proj k fields)).
    unfold typeof_field; fold typeof_field.
    intros GP.
    destruct (k =? fst p)%string.
    + simpl in rc. apply (proj_field (fst rc)).
    + apply (project fields (snd rc) k GP).
Defined.


Fixpoint upd {fields:smaplist Type} (rc: record fields) (k:key)
  (GK :good_proj k fields = true) (v:typeof_field k fields GK) {struct fields} : record fields.
Proof.
  destruct fields.
  - exfalso. clear v. apply good_proj_nil in GK. auto.
  - change (orb (k =? fst p)%string (good_proj  k  fields) = true) in GK.
    simpl in v.
    simpl. destruct (k =? fst p)%string.
    + apply (Field (fst p) v,snd rc).
    + apply (fst rc,upd _ (snd rc) k GK v).
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

Lemma type_of_field_fst : forall k A fields,
    A = type_of_field k ((k, A) :: fields).
Proof.
  unfold type_of_field.
  simpl. intros.
  destruct (key_eq k k); try discriminate.
  reflexivity.
  congruence.
Defined.


Lemma proj_eq : forall (k:key) {A: Type} v (fields: smaplist Type) (r: record fields),
  @proj ((k,A)::fields) (Field k v,r) k = eret (cast (type_of_field_fst k A fields ) v).
Proof.
  simpl.
  intros.
  unfold type_of_field_fst.
  unfold cast; simpl.
  unfold type_of_field.
  simpl.
  unfold eq_rect.
  destruct (key_eq k k). reflexivity.
  congruence.
Qed.

Lemma type_of_field_fst' : forall k k' A fields (EQ: k = k'),
    A = type_of_field k' ((k, A) :: fields).
Proof.
  unfold type_of_field.
  simpl. intros.
  destruct (key_eq k k'); try congruence.
Defined.

Lemma proj_eq' : forall (k k':key) {A: Type} v (fields: smaplist Type) (r: record fields)
                        (EQ: k' = k)
  ,
    @proj ((k',A)::fields) (Field k' v,r) k = eret (cast (type_of_field_fst' k' k A fields EQ) v).
Proof.
  intros.
  subst.
  rewrite proj_eq.
  f_equal.
Qed.

Lemma type_of_field_snd : forall k' k A fields (NEQ: false = String.eqb k k'),
    res (type_of_field k' fields) = res (type_of_field k' ((k, A) :: fields)).
Proof.
  unfold type_of_field.
  simpl. intros.
  destruct (key_eq k k'). subst. rewrite String.eqb_refl in NEQ. discriminate.
  reflexivity.
Defined.

Lemma proj_neq : forall (k k':key) {A: Type} v (fields: smaplist Type) (r: record fields)
                        (NEQ : false = String.eqb k k'),
  @proj ((k,A)::fields) (Field k v,r) k' = (cast (type_of_field_snd k' k A fields NEQ) (proj r k')).
Proof.
  simpl.
  intros.
  unfold type_of_field_snd.
  unfold cast; simpl.
  unfold type_of_field.
  simpl.
  unfold eq_ind.
  destruct (key_eq k k').
  subst.  exfalso. rewrite String.eqb_refl in NEQ. discriminate.
  destruct NEQ.
  reflexivity.
Qed.

Lemma neq_neqb : forall k k',
    k <> k' -> false = String.eqb k' k.
Proof.
  intros.
  destruct (String.eqb k' k) eqn:EQ.
  rewrite eqb_eq in EQ. congruence.
  reflexivity.
Qed.


Lemma proj_spec :
forall (k k':key) {A: Type} v (fields: smaplist Type) (r: record fields),
  @proj ((k,A)::fields) (Field k v,r) k' =
    match key_eq k' k with
    | left EQ => eret (cast (type_of_field_fst' k k' A fields (eq_sym EQ)) v)
    | right NEQ =>
        (cast (type_of_field_snd k' k A fields (neq_neqb _ _ NEQ)) (proj r k'))
    end.
Proof.
  intros.
  destruct (key_eq k' k).
  - erewrite proj_eq'; eauto.
  - erewrite proj_neq; eauto.
Qed.
