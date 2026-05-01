From Stdlib Require Import PArith List String Bool RelationClasses.
From BarocqComp Require Import DList Option Ident Utils.
Local Open Scope option_monad_scope.

Definition key : Type := ident.

Definition key_eq := Ident.eq_dec.

Inductive field (k: key) (A: Type) : Type :=
  Field : forall (a: A), field k A.

Definition field_eq_dec {A: Type} (eq_dec : forall (a1 a2: A), {a1 = a2} + {a1 <> a2})
  (k: key) (f1 : field k A) (f2 : field k A) : { f1 = f2} + {f1 <> f2} .
Proof.
  destruct f1, f2.
  destruct (eq_dec a a0).
  - subst. left ; reflexivity.
  -  right ; congruence.
Qed.

Arguments Field k {A}.

Module SMAPLIST.
  Definition smaplist (A:Type) := list (string * A).

  Definition map {V A: Type} (f: V -> A) (l: smaplist V) : smaplist A :=
    List.map (fun kv => (fst kv, f (snd kv))) l.
End SMAPLIST.


Fixpoint find_type_of_field {A: Type}  (k: key) (fields: SMAPLIST.smaplist A) : option A :=
  match fields with
  | nil => fail
  | e::fields => if (k=?(fst e))%string then Some (snd e) else find_type_of_field k fields
  end.

 Definition gtype_of_field {A: Type} (F: A -> Type) (k:key) (fields : SMAPLIST.smaplist A) :  Type :=
  match find_type_of_field k fields with
  | Some a => F a
  | None => False
  end.

 Definition type_of_field  (k:key) (fields : SMAPLIST.smaplist Type) :  Type :=
   gtype_of_field (fun x => x) k fields.


Definition proj_field {k:key} {T:Type} (fd:field k T) : T :=
  match fd with
  | Field _ x => x
  end.

 Fixpoint grecord {A: Type} (F: A -> Type) (fields: SMAPLIST.smaplist A) : Type :=
  match fields with
  | nil => (unit:Type)
  | kt::fields' => prod (field (fst kt) (F (snd kt))) (grecord F fields')
  end.

Fixpoint grecord_eq_dec {A: Type} {F: A -> Type} (eq_dec : forall (a:A) (e1 e2: F a), {e1 = e2} + {e1 <> e2})
  {fields : SMAPLIST.smaplist A} (r1 r2 : grecord F fields) {struct fields}: {r1 = r2} + {r1 <> r2}.
Proof.
  destruct fields.
  - simpl in *.
    left. destruct r1,r2.
    reflexivity.
  - simpl in *.
    destruct r1,r2.
    destruct (field_eq_dec (eq_dec (snd p)) _ f f0).
    destruct (grecord_eq_dec _ _ eq_dec _ g g0).
    left ; congruence.
    right; congruence.
    right ; congruence.
Defined.

Fixpoint grecord_map {A: Type} (F1 : A -> Type) (F2 : A -> Type) (F : forall (x:A), F1 x -> F2 x)
  (fields : SMAPLIST.smaplist A) : grecord F1 fields -> grecord F2 fields:=
  match fields  with
  | nil => fun r => tt
  | p :: fields' =>
      fun  r => (Field (fst p) (F (snd p) (proj_field (fst r))), grecord_map  F1 F2 F fields' (snd r))
  end.

Fixpoint grecord_mmap {A: Type} (F1 : A -> Type) (F2 : A -> Type) (F : forall (x:A), F1 x -> option (F2 x))
  (fields : SMAPLIST.smaplist A) : grecord F1 fields -> option (grecord F2 fields) :=
  match fields  with
  | nil => fun r => Some  tt
  | p :: fields' =>
      fun  r => let* fd := F (snd p) (proj_field (fst r)) in
                let* rc := grecord_mmap F1 F2 F fields' (snd r) in
                Some  ( Field (fst p) fd, rc)
  end.


Section REL.
  Context {A: Type}.
  Context {F1 : A -> Type}.
  Context {F2 : A -> Type}.
  Variable (R : forall (x:A), F1 x -> F2 x -> Prop).

  Fixpoint grecord_rel {fields : SMAPLIST.smaplist A} : grecord F1 fields -> grecord F2 fields -> Prop :=
  match fields  with
  | nil => fun _ _ => True
  | p :: fields' =>
      fun  r1 r2 => R (snd p) (proj_field (fst r1)) (proj_field (fst r2)) /\
        grecord_rel  (snd r1) (snd r2)
  end.
End REL.

Lemma grecord_rel_refl:
  forall (A: Type) (F: A -> Type) (R: forall x, F x -> F x -> Prop) fields,
    (forall x, Reflexive (R x)) ->
    Reflexive (@grecord_rel _ _ _ R fields).
Proof.
  unfold grecord_rel.
  induction fields; intros.
  - simpl. constructor.
  - destruct a. simpl. constructor.
    + apply H.
    + apply (IHfields H).
Qed.

Lemma grecord_rel_refl_In:
  forall (A: Type) (F: A -> Type) (R: forall x, F x -> F x -> Prop) (fields: SMAPLIST.smaplist A),
    (forall (p: ident * A), List.In p fields -> Reflexive (R (snd p))) ->
    Reflexive (@grecord_rel _ _ _ R fields).
Proof.
  unfold grecord_rel.
  induction fields; intros.
  - simpl. constructor.
  - simpl. constructor.
    + specialize (H a). simpl in H.
      apply H. tauto.
    + apply IHfields. simpl in H.
      auto.
Qed.
  
Inductive sfield {A: Type} (F: A -> Type) :=
  mksfield (s:string) (a:A) (v: F a).

Fixpoint list_of_grecord {A: Type} (F: A -> Type) (fields : SMAPLIST.smaplist A) : grecord F fields ->  list (sfield F) :=
    match fields  with
  | nil => fun _  => nil
  | p :: l => (fun '(fd, r) => mksfield F (fst p) (snd p) (proj_field fd) :: list_of_grecord  F l r)
  end.

Fixpoint dlist_of_grecord {A: Type} {F: A-> Type} {fields : SMAPLIST.smaplist A} : grecord F fields -> DList.dlist F (List.map snd fields) :=
  match fields as l return (grecord F l -> dlist F (map snd l)) with
  | nil => fun _  => DNIL F
  | p :: fields' =>
       fun r  => DCONS F (proj_field (fst r)) (dlist_of_grecord  (snd r))
  end.

Fixpoint Forall {A: Type} {F : A -> Type} (P : forall (x:A), F x ->  Prop) {fields : SMAPLIST.smaplist A}: grecord F fields -> Prop :=
  match fields with
  | nil => fun _ => True
  | p :: l => fun r => P (snd p) (proj_field (fst r)) /\ Forall P (snd r)
  end.

(* Definition record (fields : SMAPLIST.smaplist Type) := grecord (fun x => x) fields.*)

Fixpoint record (fields: SMAPLIST.smaplist Type) : Type :=
  match fields with
  | nil => unit
  | kt::fields' => prod (field (fst kt) (snd kt)) (record fields')
  end.

Fixpoint record_eq (fields : SMAPLIST.smaplist Type) : record fields = grecord (fun (X:Type) => X) fields.
Proof.
  destruct fields.
  - reflexivity.
  - simpl.
    f_equal.
    apply record_eq.
Defined.

Definition cast_record {fields: SMAPLIST.smaplist Type} (r: record fields) : grecord (fun X => X) fields :=
  cast (record_eq  fields) r.

Definition cast_grecord {fields: SMAPLIST.smaplist Type} (r: grecord (fun X => X) fields) : record  fields :=
  cast (eq_sym (record_eq  fields)) r.

Fixpoint gproj {A: Type} (F : A -> Type) {fields: SMAPLIST.smaplist A} (rc: grecord F fields) (k: key) {struct fields} : option (gtype_of_field F k fields).
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in rc. destruct rc. destruct f.
    simpl gtype_of_field.
    unfold gtype_of_field. simpl.
    destruct (k=?x)%string.
    + apply (ret a).
    + apply (gproj A F fields' g).
Defined.

(** [gprojT] has a simpler return type *)
Fixpoint gprojT {A: Type} {F : A -> Type} {fields: SMAPLIST.smaplist A} (rc: grecord F fields) (k: key) {struct fields} :
  option {t: A & F t}.
Proof.
  destruct fields as [| [x tx] fields'].
  - apply fail.
  - simpl in rc. destruct rc as (fd & rc').
    destruct (k=?x)%string.
    + apply (ret (existT _ tx (proj_field fd))).
    + apply (gprojT A F fields' rc' k).
Defined.

Fixpoint gprojt {A: Type} {F : A -> Type} {fields: SMAPLIST.smaplist A} (A_eq_dec: forall (x y: A), {x = y} + {x <> y}) (rc: grecord F fields) (k: key) (t: A) {struct fields}: option (F t).
Proof.
  destruct fields as [|[x tx] fields'].
  - apply fail.
  - simpl in rc. destruct rc.
    destruct (k=?x)%string.
    + destruct (A_eq_dec tx t).
      * subst. destruct f. apply (ret a).
      * apply fail.
    + apply fail.
Defined.

Definition proj {fields: SMAPLIST.smaplist Type} (r:record fields) (k: key) : option (type_of_field k fields) :=
  gproj (fun x => x)  (cast_record r) k.

Fixpoint good_proj {A: Type} (k:key) (fields : SMAPLIST.smaplist A) :=
  match fields with
  | nil => false
  | e::fields' => if String.eqb k (fst e) then true else good_proj k fields'
  end.

Lemma good_proj_nil : forall {A: Type} {k}, @good_proj A k nil = true -> False.
  Proof.
    discriminate.
  Qed.

Fixpoint gtypeof_field {A: Type} (F: A -> Type) (k: key) (fields: SMAPLIST.smaplist A) : forall (GP : good_proj k fields = true), Type.
Proof.
  destruct fields.
  - intro. exfalso. apply (good_proj_nil GP) .
  - change (good_proj k (p::fields)) with (orb (String.eqb k (fst p)) (good_proj k fields)).
    destruct (String.eqb k (fst p)).
    + intro. exact (F (snd p)).
    + unfold orb.
      apply (gtypeof_field A F k fields).
Defined.

Fixpoint gproject {A: Type} (F : A -> Type) {fields:SMAPLIST.smaplist A} (rc:grecord F fields) (k:key) : forall (GP : good_proj k fields = true), gtypeof_field F k fields GP.
Proof.
  destruct fields.
  - intros. exfalso.
    apply (good_proj_nil GP).
  - change (good_proj k (p::fields)) with (orb (String.eqb k (fst p)) (good_proj k fields)).
    simpl.
    intros GP.
    destruct (k =? fst p)%string.
    + simpl in rc. apply (proj_field (fst rc)).
    + apply (gproject A F fields (snd rc) k GP).
Defined.

Definition typeof_field  (k: key) (fields: SMAPLIST.smaplist Type) : forall (GP : good_proj k fields = true), Type :=
  gtypeof_field (fun x => x) k fields.

Definition project  {fields:SMAPLIST.smaplist Type} (rc:record fields) (k:key) : forall (GP : good_proj k fields = true), typeof_field  k fields GP :=
  gproject (fun x => x) (cast_record rc) k.

(*Fixpoint gupd {A: Type} (F: A -> Type) {fields:SMAPLIST.smaplist A} (rc: grecord F fields) (k:key)
  (GK :good_proj k fields = true) (v:gtype_of_field F k fields) {struct fields} : grecord F fields.
Proof.
  destruct fields.
  - exfalso. clear v. apply good_proj_nil in GK. auto.
  - simpl in GK.
    simpl in v.
    unfold gtype_of_field in v. simpl in v.
    destruct (k=? fst p)%string.
    + apply (Field (fst p) v,snd rc).
    + apply (fst rc,gupd _ F _ (snd rc) k GK v).
Defined.
*)
(*Definition upd {fields:SMAPLIST.smaplist Type} (rc: record fields) (k:key)
  (GK :good_proj k fields = true) (v:type_of_field k fields)  : record fields :=
  gupd (fun x => x) rc k GK v.
*)

Lemma Some_inj {A:Type} {r1 r2: A}  (EQ: Some  r1 = Some  r2) : r1 = r2.
Proof.
  injection EQ.
  auto.
Defined.

Fixpoint gupd {A: Type} (F: A -> Type) {fields:SMAPLIST.smaplist A} (rc: grecord F fields) (k:key) (T:A) (v: F T)
  (EQ: find_type_of_field k fields = Some  T)
  {struct fields} : grecord F fields.
Proof.
  destruct fields.
  - exact tt.
  - simpl in EQ.
    destruct (k=? fst p)%string.
    + apply (Field (fst p) (cast (f_equal F (eq_sym (Some_inj EQ))) v),snd rc).
    + apply (fst rc,gupd _ F _ (snd rc) k _ v EQ).
Defined.

Definition upd {fields:SMAPLIST.smaplist Type} (rc: record  fields) (k:key) {T:Type} (v: T)
  (EQ: find_type_of_field k fields = Some  T) : record  fields :=
  cast_grecord (gupd (fun x => x) (cast_record rc) k T v EQ).

Fixpoint mk_recordT {A: Type} (F: A -> Type) {fields:SMAPLIST.smaplist A} (rc : grecord F fields) {struct fields} : record (SMAPLIST.map F fields).
Proof.
  destruct fields.
  - apply tt.
  - simpl in rc. simpl.
    apply (fst rc, mk_recordT _ F _ (snd rc)).
Defined.

Fixpoint map_find_type_of_field {A: Type} (F: A -> Type) (k:key) {fields:SMAPLIST.smaplist A} (T:A) (EQ:find_type_of_field k fields = Some  T) :
  find_type_of_field k (SMAPLIST.map F fields) = Some  (F T).
Proof.
  destruct fields.
  - discriminate.
  - simpl in *.
    destruct (k =? fst p)%string.
    +  apply (f_equal (option_map F)) in EQ.
       simpl in EQ.
       apply EQ.
    + apply map_find_type_of_field.
      apply EQ.
Qed.

(*
Lemma gupd_upd : forall {A: Type} (F: A -> Type) {fields:SMAPLIST.smaplist A} (rc: grecord F fields) (k:key) (T:A) (v: F T)
  (EQ:find_type_of_field k fields = Some  T),
   mk_recordT F (gupd F rc k T v EQ) = @upd (MapList.map F fields) (mk_recordT F rc) k (F T) v (map_find_type_of_field F k T EQ).
Proof.
  unfold upd.
  induction fields.
  - simpl. discriminate.
  - intros.
    simpl in EQ.
    destruct (string_dec k (fst a)).
    + subst.
      assert (Some  (snd a) = Some  T).
      { rewrite String.eqb_refl in EQ.
        apply EQ. }

      rewrite IHfields.
      destruct (k =? fst a)%string.
*)

Fixpoint dyn_upd {A: Type} (F: A -> Type) (eq_dec : forall (x y:A), {x = y} + {x <> y}) {fields:SMAPLIST.smaplist A} (rc: grecord F fields) (k:key)
  (ty:A) (v: F ty) {struct fields} : option (grecord F fields).
Proof.
  destruct fields.
  - exact fail.
  - simpl in rc.
    destruct (k=? fst p)%string.
    + destruct (eq_dec ty (snd p)).
      apply (Some  (Field (fst p) (cast (f_equal F e) v),snd rc)).
      apply fail.
    + eapply bind.
      eapply (dyn_upd _ F eq_dec _ (snd rc) k ty v).
      intro.
      apply (Some  (fst rc,X)).
Defined.









Fixpoint gupdate {A: Type} (F: A -> Type) {fields:SMAPLIST.smaplist A} (rc: grecord F fields) (k:key)
   (v:gtype_of_field F k fields) {struct fields} : option (grecord F fields).
Proof.
  destruct fields.
  - simpl in v.  apply Some . exact tt.
  - unfold gtype_of_field in v. simpl in v.
    simpl.
    destruct (k=? fst p)%string.
    + apply (Some  (Field (fst p) v,snd rc)).
    + eapply bind.
      eapply gupdate. apply (snd rc).
      apply v.
      intro.
      apply (Some  (fst rc,X)).
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
Fixpoint gdecomp_fields {A: Type} (F : A -> Type) (fields : SMAPLIST.smaplist A)  {struct fields} :
  forall (P : grecord F fields -> Prop), Prop :=
  match fields as fd' return (grecord F fd' -> Prop) -> Prop with
  | nil => fun P => P tt
  | (i,v)::fields' => fun P => forall v, gdecomp_fields F fields' (fun r' => P (Field i v, r'))
  end.

Lemma gdecomp_fields_sound : forall {A: Type} (F: A -> Type) fields (P : grecord F fields -> Prop),
    gdecomp_fields F fields P ->
    forall r, P r.
Proof.
  induction fields; simpl.
  - intros. destruct r. apply H.
  -  intros. destruct a.
     destruct r. simpl in f. destruct f.
     apply IHfields with (r:=g); auto.
Qed.

Definition cast_pred {fields} (P : record fields -> Prop) : grecord (fun X => X) fields -> Prop:=
  fun r => P (cast_grecord r).

Lemma cast_record_idem : forall fields (r:record fields),
    cast_grecord (cast_record r) = r.
Proof.
  unfold cast_record. unfold cast_grecord.
  intros.
  generalize (record_eq fields).
  intros.
  destruct e.
  reflexivity.
Qed.

Lemma cast_pred_cast_record : forall fields (P:record fields -> Prop),
    forall r, cast_pred P (cast_record r) <-> P r.
Proof.
  unfold cast_pred.
  intros.
  rewrite cast_record_idem. tauto.
Qed.

Lemma decomp_fields_sound : forall fields (P : record fields -> Prop),
    gdecomp_fields (fun x => x) fields (cast_pred  P) ->
  forall r, P r.
Proof.
  intros.
  apply gdecomp_fields_sound with (r:= (cast_record r)) in H.
  apply cast_pred_cast_record in H; auto.
Qed.


Ltac apply_decomp_field :=
  let b := fresh "R" in
  intro b; pattern b;
  let pred := fresh "PRED" in
  match goal with
  | |- ?P ?X => set (pred := P) ;
                apply decomp_fields_sound;
                match goal with
                | |- gdecomp_fields ?F ?FD ?P =>
                    unfold FD;
                    cbv beta iota delta [gdecomp_fields ];
                    unfold snd ; intros;
                    unfold pred;clear pred
                end
                end.

Lemma field_eq : forall (k:key) (A B: Type) (a1 a2:A) (b1 b2:B),
                        a1 = a2 -> b1 = b2 -> (Field k a1,b1) = (Field k a2,b2).
Proof.
  intros.
  congruence.
Qed.

Ltac findtyp X L :=
  match L with
  | unit => fail
  | ((field ?K ?T) * ?LR)%type =>
      match constr:((X,K)) with
      | (?V, ?V) => exact T
      |    _     => findtyp X LR
      end
  end.

Ltac type_of_field K R :=
  let ty := type of R in
  let ty := eval compute in ty in
    findtyp K ty
.

Notation "X @ K <- V" := (upd (T:= (ltac:(type_of_field K X))) X K V eq_refl) (at level 100).


(*Lemma type_of_field_fst : forall k A fields,
    A = type_of_field k ((k, A) :: fields).
Proof.
  simpl. intros.
  rewrite String.eqb_refl.
  reflexivity.
Defined.


Lemma proj_eq : forall (k:key) {A: Type} v (fields: SMAPLIST.smaplist Type) (r: record fields),
  @proj ((k,A)::fields) (Field k v,r) k = eret (cast (type_of_field_fst k A fields ) v).
Proof.
  simpl.
  intros.
  unfold type_of_field_fst.
  unfold cast; simpl.
  unfold type_of_field.
  simpl.
  unfold eq_rect.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma type_of_field_fst' : forall k k' A fields (EQ: k = k'),
    A = type_of_field k' ((k, A) :: fields).
Proof.
  simpl. intros.
  subst.
  rewrite String.eqb_refl.
  reflexivity.
Defined.

Lemma proj_eq' : forall (k k':key) {A: Type} v (fields: SMAPLIST.smaplist Type) (r: record fields)
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
    option (type_of_field k' fields) = option (type_of_field k' ((k, A) :: fields)).
Proof.
  simpl.
  intros.
  rewrite eqb_sym in NEQ.
  destruct (k' =? k)%string. discriminate. reflexivity.
Defined.

Lemma proj_neq : forall (k k':key) {A: Type} v (fields: SMAPLIST.smaplist Type) (r: record fields)
                        (NEQ : false = String.eqb k k'),
  @proj ((k,A)::fields) (Field k v,r) k' = (cast (type_of_field_snd k' k A fields NEQ) (proj r k')).
Proof.
  simpl.
  intros.
  unfold type_of_field_snd.
  unfold cast; simpl.
  unfold eq_ind.
  destruct (eqb_sym k k').
  destruct (k=?k')%string.
  discriminate.
  reflexivity.
Qed.

Lemma neq_neqb : forall k k',
    k <> k' -> false = String.eqb k' k.
Proof.
  intros.
  destruct (String.eqb k' k) eqn:EQ.
  rewrite String.eqb_eq in EQ. congruence.
  reflexivity.
Qed.


Lemma proj_spec :
forall (k k':key) {A: Type} v (fields: SMAPLIST.smaplist Type) (r: record fields),
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
*)
