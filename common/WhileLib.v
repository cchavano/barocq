(** Various [while] combinators: currified, uncurrified, n-ary
 *)
From Stdlib Require Import List String.
From compcert Require Import Coqlib.
From BarocqComp Require Import Option Brecord While.
From Stdlib Require Import FunctionalExtensionality.
Open Scope option_monad_scope.


(** For the shallow embedding, it is more readable to use n-ary functions.
    The idea is that the while loop iterates over a n-ary tuple.
 *)

(** [mkarrow [t1;...;tn] r] constructs the type [t1 -> t2 -> ... -> tn -> r] *)
Fixpoint mkarrow (l:list Type) (r:Type): Type :=
  match l with
  | nil => r
  | e::l => e -> (mkarrow l r)
  end.

(*Module CURRY. *)
  (* Those are the most "natural" definitions.
     However, the associativity of tuples is not expected (t1 * (t2 * (t3 * ....)))
   *)

(** [mktuple [t1;...;tn]] constructs the type t1 * (... * tn) *)

Definition is_nil_dec (l:list Type) : {l = nil} + {l <> nil}.
Proof.
  destruct l.
  - left. reflexivity.
  - right. discriminate.
Defined.

Fixpoint mktuple (l:list Type) : Type :=
  match l with
  | nil => unit
  | e :: l =>  e * (mktuple l)
  end.

Fixpoint mktuple_rec (l:list Type) (T:Type) :=
  match l with
  | nil => T
  | e::l => mktuple_rec l (T * e)
  end.

Definition mktuplel (l:list Type) : Type :=
  match l with
  | nil => unit
  | e::l => if is_nil_dec l then e else mktuple_rec l e
  end.


Fixpoint conv_tuple_rec {T:Type} {l:list Type} : mktuple (T::l) -> mktuple_rec l T.
Proof.
  simpl.
  simpl in conv_tuple_rec.
  destruct l.
  - simpl. apply (fun X => fst X).
  - simpl.
    intro.
    apply conv_tuple_rec.
    apply ((fst X, fst (snd X)), snd (snd X)).
Defined.

Definition conv_tuple {l:list Type} : mktuple l -> mktuplel l.
Proof.
  destruct l.
  - simpl. auto.
  - simpl.
    specialize (@conv_tuple_rec T l).
    simpl. destruct (is_nil_dec l).
    subst. simpl. auto.
    auto.
Defined.

Definition mktuple_nil {l:list Type} (isN : l = nil) : mktuple l.
Proof.
  destruct l.
  simpl. apply tt.
  discriminate.
Qed.

Definition assoc_prod {A B C: Type} :
  A * B * C -> A * (B * C) :=
  fun x => (fst (fst x) , (snd (fst x),snd x)).


Fixpoint conv_mktuple_rec {l:list Type} {T:Type} :
  mktuple_rec l T -> T * mktuple l.
Proof.
  destruct l.
  - simpl.
    apply (fun t => (t,tt)).
  - simpl.
    intro. apply conv_mktuple_rec in X.
    apply (assoc_prod X).
Defined.


Definition conv_tuplel {l:list Type} : mktuplel l -> mktuple l.
Proof.
  destruct l.
  - simpl. auto.
  - simpl.
    destruct l.
    + simpl.
      apply (fun t => (t,tt)).
    + apply conv_mktuple_rec.
Defined.


Fixpoint uncurry {l: list Type} {r:Type} : mkarrow l r -> mktuple l -> r.
Proof.
  destruct l ; simpl.
  - auto.
  - intros.
    apply (uncurry l r).
    apply (X (fst X0)).
    apply (snd X0).
Defined.

Fixpoint curry {l: list Type} {r:Type} : (mktuple l -> r) -> mkarrow l r.
Proof.
  destruct l ; simpl.
  - apply (fun F => F tt).
  - intros.
    apply (curry l r).
    apply (fun F => X (X0, F)).
Defined.

Lemma uncurry_curry : forall l r (F: mktuple l -> r) a, uncurry (curry F) a = F a.
Proof.
  induction l; simpl; auto.
  - destruct a. reflexivity.
  - intros.
    rewrite IHl.
    destruct a0; reflexivity.
Qed.

Definition uncurryl {l:list Type} {r:Type} : mkarrow l r -> mktuplel l -> r :=
  fun F A => uncurry  F (conv_tuplel A).

(** [nwhile_nn] works for pure [C] and [B]  *)
Fixpoint nwhile_nn' {l:list Type} (C : mkarrow l bool) (B : mkarrow l (mktuplel l)) (fuel:nat) (le : mktuplel l) :=
  if uncurryl C le
  then
    match fuel with
    | O => None
    | S fuel' => nwhile_nn' C B fuel' (uncurryl B le)
    end
  else Some le.


(** [nwhile_cnn] works for pure [C] and [B] - currified version *)
Fixpoint nwhile_cnn {l:list Type} (C : mkarrow l bool) (B : mkarrow l (mktuple l)) (fuel:nat) : mkarrow l (option (mktuple l)) :=
  curry
    (fun le : mktuple l =>
     if uncurry C le
     then match fuel with
          | 0%nat => None
          | S fuel' => uncurry (nwhile_cnn  C B fuel') (uncurry B le)
          end
     else Some le).

(** [nwhilenn] works for pure [C] and [B] - non currified version *)
Fixpoint nwhile_nn {l:list Type} (C : mkarrow l bool) (B : mkarrow l (mktuple l)) (fuel:nat) (le : mktuple l) :=
  if uncurry C le
  then
    match fuel with
    | O => None
    | S fuel' => nwhile_nn C B fuel' (uncurry B le)
    end
  else Some le.

(*Lemma nwhile_eq : forall fuel l (C: mkarrow l bool)  B args,
    uncurry (nwhile_cnn C B fuel) args = nwhile_nn C B fuel args.
Proof.
  induction fuel.
  - simpl.
    intros.
    rewrite uncurry_curry. reflexivity.
  - intros.
    simpl.
    rewrite uncurry_curry.
    destruct (uncurry C args); auto.
Qed.
*)

Fixpoint nwhile_no {l:list Type} (C : mkarrow l bool) (B : mkarrow l (option (mktuple l))) (fuel:nat) (le : mktuple l) : option (mktuple l) :=
  if uncurry C le
  then
    match fuel with
    | O => None
    | S fuel' =>
        let* le' := uncurry B le in
        nwhile_no C B fuel' le'
    end
  else Some le.

Fixpoint nwhile_no' {l:list Type} (C : mkarrow l bool) (B : mkarrow l (option (mktuplel l))) (fuel:nat) (le : mktuplel l) : option (mktuplel l) :=
  if uncurryl C le
  then
    match fuel with
    | O => None
    | S fuel' =>
        let* le' := uncurryl B le in
        nwhile_no' C B fuel' le'
    end
  else Some le.

Definition mkarrow_map {l: list Type} {r r': Type} (B : mkarrow l r) (F: r -> r') : mkarrow l r' :=
curry (fun X  => F (uncurry B X)).

Lemma uncurryl_Cond : forall l (C: mkarrow l bool) le,
    uncurryl C le = uncurry C (conv_tuplel le).
Proof.
  intros.
  reflexivity.
Qed.

Lemma conv_tuple_rec_idem : forall l T
                                   (le : mktuple_rec l T),
  conv_tuple_rec (conv_mktuple_rec le) = le.
Proof.
  induction l; simpl.
  - reflexivity.
  - intros.
    specialize (@IHl _ le).
    destruct (conv_mktuple_rec le).
    simpl. destruct p; simpl.
    auto.
Qed.


Lemma conv_tuple_tuplel_idem : forall l (le: mktuplel l),
    conv_tuple (conv_tuplel le) = le.
Proof.
  destruct l; simpl.
  - reflexivity.
  - intros.
    destruct l.
    + simpl. reflexivity.
    + simpl in *.
      rewrite <- (conv_tuple_rec_idem _ _ le) at 4.
      destruct ((conv_mktuple_rec le)); auto.
      simpl. destruct p; auto.
Qed.

Lemma conv_tuplel_tuple_idem : forall l (le: mktuple l),
    conv_tuplel (conv_tuple le) = le.
Proof.
  destruct l; simpl.
  - reflexivity.
  - intros.
    destruct l.
    + simpl. simpl in le. destruct le. destruct u. reflexivity.
    + simpl in *.
      destruct le. destruct p.
      simpl.
      assert ((conv_mktuple_rec (conv_tuple_rec (t, t0, m)) =
                  (t,t0,m))).
      generalize (t, t0).
      generalize (T * T0)%type.
      { induction l; simpl.
        - destruct m.
          reflexivity.
        - intros.
          destruct m ; simpl.
          rewrite IHl.
          reflexivity.
      }
      rewrite H.
      reflexivity.
Qed.





Fixpoint nwhile_on {l:list Type} (C : mkarrow l (option bool)) (B : mkarrow l (mktuple l)) (fuel:nat) (le : mktuple l) :=
  let* b := uncurry C le in
  if b
  then
    match fuel with
    | O => None
    | S fuel' =>
        nwhile_on C B fuel' (uncurry B le)
    end
  else Some le.

Fixpoint nwhile_on' {l:list Type} (C : mkarrow l (option bool)) (B : mkarrow l (mktuplel l)) (fuel:nat) (le : mktuplel l) :=
  let* b := uncurryl C le in
  if b
  then
    match fuel with
    | O => None
    | S fuel' =>
        nwhile_on' C B fuel' (uncurryl B le)
    end
  else Some le.



(* [nwhile] is more general *)
Fixpoint nwhile {l:list Type} (C : mkarrow l (option bool)) (B : mkarrow l (option (mktuple l))) (fuel:nat) (le : mktuple l) :=
  let* b := uncurry C le in
  if b
  then let* le' := uncurry B le in
       match fuel with
       | O => None
       | S fuel' => nwhile C B fuel' le'
       end
  else Some le.


Fixpoint nwhile' {l:list Type} (C : mkarrow l (option bool)) (B : mkarrow l (option (mktuplel l))) (fuel:nat) (le : mktuplel l) :=
  let* b := uncurryl C le in
  if b
  then let* le' := uncurryl B le in
       match fuel with
       | O => None
       | S fuel' => nwhile' C B fuel' le'
       end
  else Some le.


(** Only [nwhile'] is needed *)


Lemma uncurry_mkarrow_map_eq : forall {l:list Type} {r r':Type} (C: mkarrow l r) (F: r -> r') a,
    uncurry (mkarrow_map C F) a = F (uncurry C a).
Proof.
  induction l; simpl;auto.
  intros.
  destruct a0.
  simpl.
  specialize (IHl _ _ (C a0) F m).
  rewrite <- IHl.
  reflexivity.
Qed.



Lemma nwhile_nn_eq : forall l (C: mkarrow l bool)  (B: mkarrow l (mktuplel l)) fuel le,
    nwhile_nn' C B fuel le =
      nwhile' (mkarrow_map C (fun b => Some b)) (mkarrow_map B (fun x => Some x)) fuel le.
Proof.
  induction fuel.
  - simpl.
    unfold uncurryl. intros.
    rewrite uncurry_mkarrow_map_eq.
    simpl.
    rewrite uncurry_mkarrow_map_eq.
    simpl. reflexivity.
  - intros.
    simpl.
    unfold uncurryl. intros.
    rewrite uncurry_mkarrow_map_eq.
    simpl.
    rewrite uncurry_mkarrow_map_eq.
    simpl. rewrite IHfuel.
    reflexivity.
Qed.

Lemma nwhile_no_eq : forall l (C: mkarrow l bool)  (B: mkarrow l (option (mktuplel l))) fuel le,
    nwhile_no' C B fuel le =
      nwhile' (mkarrow_map C (fun b => Some b)) B fuel le.
Proof.
  induction fuel.
  - simpl.
    unfold uncurryl. intros.
    rewrite uncurry_mkarrow_map_eq.
    simpl.
    destruct (uncurry C (conv_tuplel le)); auto.
    destruct (uncurry B (conv_tuplel le)); auto.
  - intros.
    simpl. unfold uncurryl.
    rewrite uncurry_mkarrow_map_eq.
    simpl.
    destruct (uncurry C (conv_tuplel le)); auto.
    destruct (uncurry B (conv_tuplel le)); auto.
    simpl. auto.
Qed.

Lemma nwhile_on_eq : forall l (C: mkarrow l (option bool))  (B: mkarrow l (mktuplel l)) fuel le,
    nwhile_on' C B fuel le =
      nwhile' C (mkarrow_map B (fun x => Some x)) fuel le.
Proof.
  induction fuel.
  - simpl.
    unfold uncurryl. intros.
    rewrite uncurry_mkarrow_map_eq.
    simpl. reflexivity.
  - intros.
    simpl. unfold uncurryl.
    rewrite uncurry_mkarrow_map_eq.
    simpl.
    destruct (uncurry C (conv_tuplel le)); auto.
    simpl. destruct b; auto.
Qed.


Lemma nwhile_eq : forall l (C: mkarrow l (option bool))  (B: mkarrow l (option (mktuplel l))) fuel le,
    nwhile' C B fuel le =
      option_map conv_tuple (nwhile C (mkarrow_map B (option_map conv_tuplel)) fuel (conv_tuplel le)).
Proof.
  induction fuel.
  - simpl.
    unfold uncurryl. intros.
    destruct (uncurry C (conv_tuplel le)); simpl;auto.
    destruct b; auto.
    +  rewrite uncurry_mkarrow_map_eq.
       destruct (uncurry B (conv_tuplel le)); auto.
    + simpl. rewrite conv_tuple_tuplel_idem. reflexivity.
  - intros.
    simpl. unfold uncurryl.
    rewrite uncurry_mkarrow_map_eq.
    destruct (uncurry C (conv_tuplel le)); auto.
    simpl. destruct b; auto.
    destruct (uncurry B (conv_tuplel le)); auto.
    + simpl.
      apply IHfuel.
    + simpl. rewrite conv_tuple_tuplel_idem. reflexivity.
Qed.

Definition  tuple_lt (lt: list (string * Type)) := WhileLib.mktuple (List.map snd lt).


Fixpoint record_of_tuple (lt: list (string * Type)) (le : tuple_lt lt) : record lt.
Proof.
  destruct lt.
  - exact tt.
  - simpl in le.
    simpl. apply (Field (fst p) (fst le) , record_of_tuple _ (snd le)).
Defined.


Fixpoint tuple_of_record (lt: list (string * Type)) (le : record lt) : tuple_lt lt.
Proof.
  destruct lt.
  - exact tt.
  - simpl in le.
    simpl. apply (proj_field (fst le) , tuple_of_record _ (snd le)).
Defined.

Lemma option_map_tuple_of_record : forall lt F G,
    option_map (fun x => conv_tuple(tuple_of_record lt x)) F = G ->
    option_map
    (WhileLib.tuple_of_record
       lt) F =
  Coqlib.option_map WhileLib.conv_tuplel G.
Proof.
  intros.
  subst.
  destruct F; simpl; auto.
  rewrite conv_tuplel_tuple_idem.
  reflexivity.
Qed.



(*Fixpoint xtuple_of_recordp (lt:list (string * Type)) (le:record lt) (ls : list string)
  (GS  : ls = (List.map fst lt))
  : tuple_lt lt.
Proof.
  unfold tuple_lt.
  destruct ls.
  - destruct lt.
    apply tt.
    discriminate.
  -
    destruct lt.
    + apply tt.
    + split.
      *  assert (GP : Brecord.good_proj s (p::lt) = true).
         { simpl in GS. simpl.
           inversion GS. subst.
           rewrite String.eqb_refl.
           reflexivity.
         }
         specialize (Brecord.project le s GP).
         intro.
         simpl in GP.
         unfold typeof_field in X.
         simpl in X.
         destruct (fst p =? fst p)%string eqn:C.
         inversion GS ; subst.
         destruct (fst p =? fst p)%string.
         apply X.
         discriminate.
         exfalso.
         rewrite String.eqb_refl in C. discriminate.
      * apply xtuple_of_recordp with (ls:=ls).
        apply (snd le).
        eapply DList.inj_list_tl; eauto.
Defined.


Definition tuple_of_recordp (lt:list (string * Type)) (le:record lt) :=
  xtuple_of_recordp lt le (List.map fst lt) eq_refl.

Opaque Brecord.project.

Goal forall x,
 tuple_of_recordp (("a"%string,(nat:Type)) ::("b"%string,(bool:Type)) :: nil) ((Field "a"%string O), (Field "b"%string true, tt)) = x.
Proof.
  unfold tuple_of_recordp.
  unfold xtuple_of_recordp.
  unfold map.
*)



Lemma record_of_tuple_of_record : forall lt (le:record lt),
    record_of_tuple lt (tuple_of_record lt le) = le.
Proof.
  induction lt; simpl; auto.
  - destruct le. reflexivity.
  - intros.
    destruct le ; auto.
    f_equal;auto.
    destruct f. simpl. auto.
Qed.


Lemma while_nwhile : forall lt (C : record lt -> option bool) (B : record lt -> option (record lt))
                            fuel (le: record lt),
    While.while C B fuel le =
      option_map (record_of_tuple lt) (nwhile (curry (fun X => C (record_of_tuple lt X)))
        (mkarrow_map  (curry (fun X => B (record_of_tuple lt X))) (option_map (tuple_of_record lt))) fuel
        (tuple_of_record lt le)).
Proof.
  induction fuel; simpl;auto.
  - intros.
    rewrite uncurry_curry.
    rewrite record_of_tuple_of_record.
    destruct (C le);auto.
    simpl.
    destruct b;auto.
    + rewrite uncurry_mkarrow_map_eq.
      rewrite uncurry_curry.
      rewrite record_of_tuple_of_record.
      destruct (B le); simpl;auto.
    + simpl. rewrite record_of_tuple_of_record.
      reflexivity.
  - intros. rewrite uncurry_curry.
    rewrite record_of_tuple_of_record.
    rewrite uncurry_mkarrow_map_eq.
    rewrite uncurry_curry.
    rewrite record_of_tuple_of_record.
    destruct (C le);auto.
    simpl. destruct b; auto.
    destruct (B le); simpl;auto.
    simpl. rewrite record_of_tuple_of_record. reflexivity.
Qed.

Lemma nwhile_while : forall l (C : mkarrow l (option bool))
                            (B : mkarrow l (option (mktuple l)))
                            fuel (le: mktuple l),
    nwhile C B fuel le =
      While.while (uncurry C) (uncurry B) fuel le.
Proof.
  induction fuel; simpl;auto.
  - intros.
    destruct (uncurry C le);auto.
    simpl. destruct b;auto.
    destruct (uncurry B le);auto.
    simpl. auto.
Qed.

(** Proof rule to compare 2 [while] loops.
    One operating over a record, the other operating over a tuple.
 *)
Definition  tuple_record (lt: list (string * Type)) := mktuple (List.map snd lt).

Definition record_tuple (lt : list (string * Type)) (r : Brecord.record lt) (t: tuple_record lt) :=
  r = WhileLib.record_of_tuple _ t.

Definition compat_fun {r:Type} {lt : list (string * Type)} (F: Brecord.record lt -> r) (G:tuple_record lt -> r) :=
  forall tp,
    F (WhileLib.record_of_tuple _ tp) = G tp.


Definition compat_body  {lt : list (string * Type)} (F: record lt -> option (record lt))
  (G : tuple_record lt -> option (tuple_record lt)) :=
  forall tp,
    option_map (tuple_of_record lt) (F (record_of_tuple _ tp)) =  (G tp).


Lemma compat_while : forall (lt:list (string * Type)) (C1 : Brecord.record lt -> option bool) (C2 : tuple_record lt -> option bool)
  (B1 : Brecord.record lt -> option (Brecord.record lt)) (B2 : tuple_record lt -> option (tuple_record lt)) F1 F2
  (I1 : Brecord.record lt) (I2 : tuple_record lt)
  (EQ : F1 = F2)
  (CI :record_tuple lt I1 I2)
  (CC :compat_fun C1 C2)
  (CB : compat_body B1 B2),
  option_rel (record_tuple lt) (While.while C1 B1 F1 I1) (While.while C2 B2 F2 I2).
Proof.
  intros. subst.
  revert I1 I2 CI.
  induction F2; simpl.
  - intros.
    unfold record_tuple in CI.
    subst.
    rewrite <- CC.
    rewrite <- CB.
    destruct (C1 (record_of_tuple lt I2)).
    + simpl. destruct b; auto.
      destruct (B1 (record_of_tuple lt I2)); simpl.
      constructor.
      constructor.
      constructor; auto.
      reflexivity.
    + simpl. constructor.
  - intros.
    unfold record_tuple in CI.
    subst.
    rewrite <- CC.
    rewrite <- CB.
    destruct (C1 (record_of_tuple lt I2)).
    + simpl. destruct b; auto.
      destruct (B1 (record_of_tuple lt I2)); simpl; auto.
      apply IHF2.
      unfold record_tuple. rewrite record_of_tuple_of_record. reflexivity.
      constructor.
      constructor.
      reflexivity.
    + simpl. constructor.
Qed.

Lemma bind_while :
forall (lt:list (string * Type)) (r:Type) (C1 : Brecord.record lt -> option bool) (C2 : tuple_record lt -> option bool)
  (B1 : Brecord.record lt -> option (Brecord.record lt)) (B2 : tuple_record lt -> option (tuple_record lt)) F1 F2
  (I1 : Brecord.record lt) (I2 : tuple_record lt) (CT1: Brecord.record lt ->  option r)
  (CT2: tuple_record lt ->  option r)
  (EQ : F1 = F2)
  (CI :record_tuple lt I1 I2)
  (CC :compat_fun C1 C2)
  (CB : compat_body B1 B2)
  (CCont : compat_fun CT1 CT2)
,
  (let* W1 := While.while C1 B1 F1 I1 in CT1 W1) =
    (let* W2 := While.while C2 B2 F2 I2 in CT2 W2).
Proof.
  intros.
  apply bind_gequal.
  assert (WW : option_rel (record_tuple lt) (While.while C1 B1 F1 I1) (While.while C2 B2 F2 I2)).
  {
    apply compat_while; auto.
  }
  inv WW.
  constructor.
  constructor.
  unfold compat_fun in CCont.
  rewrite <- CCont.
  unfold record_tuple in H1. congruence.
Qed.


(** Ltac to infer which [while] loop to use depending on the types of the arguments.
    This is useful for the shallow Rocq embedding.
    This could be done in the printer...
 *)

Ltac get_args t :=
  match t with
  | ?A -> ?B => let l := get_args B in
                constr:((A:Type)::l)
  |   _      => constr:(@nil Type)
  end.

Ltac rtyp t :=
  match t with
  | ?A -> ?B => rtyp B
  |   _      => t
  end.


Ltac list_of_pair t :=
  match t with
  | (?A * ?B)%type => let l := list_of_pair B in
               constr:((A:Type) :: l)
  |    _    => constr:((t:Type)::nil)
  end.

Ltac list_of_pairl t :=
  match t with
  | (?A * ?B)%type => let l := list_of_pair A in
                      let r := eval simpl in (List.app l ((B:Type)::nil)) in
                        r
  |    _    => constr:((t:Type)::nil)
  end.

Ltac while_typ A :=
  let t := type of A in
  let ty := list_of_pair t in
  ty.

Ltac while_typl A :=
  let t := type of A in
  let ty := list_of_pairl t in
  ty.



(*Definition option_map {A B:Type} (o:option A) (f: A -> B) : option B :=
  bind o (fun x => Some (f x)).
*)



Ltac choose_while C B V A :=
  let tc := type of C in
  let tb := type of B in
  let rc := rtyp tc in
  let rb := rtyp tb in
  let l  := while_typ A in
  let tv := type of V in
  match constr:((rc , rb)) with
  | (option _ , option _) => constr:(@nwhile l C B V A)
  | (option _ ,  _     )  => constr:(@nwhile_on l C B V A)
  | (  _      , option _) => constr:(@nwhile_no l C B V A)
  | (   _     ,     _   ) => constr:(@nwhile_nn l C B V A)
  end.

Ltac while_tac C B V A :=
  let w := choose_while C B V A in
  exact w.

Notation "'WHILES' ( C , B ,  V ,  A ) " := (ltac:(while_tac C B V A)) (at level 100).


(** We could also just convert at the end i.e. constr:(option_map(@nwhile l C B V A) conv_tuple) *)
Ltac choose_whilel C B V A :=
  let tc := type of C in
  let tb := type of B in
  let rc := rtyp tc in
  let rb := rtyp tb in
  let l  := while_typl A in
  match constr:((rc , rb)) with
  | (option _ , option _) => constr:(@nwhile' l C B V A)
  | (option _ ,  _     )  => constr:(@nwhile_on' l C B V A)
  | (  _      , option _) => constr:(@nwhile_no' l C B V A)
  | (   _     ,     _   ) => constr:(@nwhile_nn' l C B V A)
  end.

Ltac while_tacl C B V A :=
  let w := choose_whilel C B V A in
  exact w.



Notation "'WHILE' ( C , B ,  V ,  A ) " := (ltac:(while_tacl C B V A)) (at level 100).
