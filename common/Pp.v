(** Drawing trees *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List.
From Stdlib Require  Numbers.DecimalString.
From BarocqComp Require Import Unsigned63.
From compcert Require Import Coqlib.

Inductive position :=
| Left (* justify left *)
| Right (* justify right *)
| Middle (* middle *).

Inductive box :=
| Bemp
| Bstr (s:string)
| Bcat (b1 b2:box)  (* b1 left ; b2 right (first lines are aligned *)
| Bstack (b1 b2:box) (p:position) (* b1 on top of b2 *)
| Bframe (t:string) (l:string) (b:box) (* put a frame around b *).

Definition space :=  (Ascii.Ascii false false false false false true false false).

Definition lf := Ascii.ascii_of_byte Byte.x0a.

Definition nl := String lf EmptyString.

Definition string_of_Z (z:Z) :=
  DecimalString.NilZero.string_of_int (Z.to_int z).

Definition string_of_int  (i:int) := string_of_Z (to_Z i).

Definition seq (l:list box) :=
  List.fold_right (fun b1 b => Bcat b1 b) Bemp l.

Definition stack (p:position) (l:list box) :=
  List.fold_right (fun b1 b => Bstack b1 b p) Bemp l.


Module CString.
  (* High level strings, easy to print *)
  Inductive t :=
  | Crep (s:string) (n:N) (* repeat s, n times *)
  | Capp (s1 s2:t) (* append *).

  Definition Cstr (s:string) := Crep s 1%N.

  Fixpoint concatn (s:string) (n:nat) :=
    match n with
    | O => ""%string
    | S n => append s (concatn s n)
    end.

  Fixpoint to_string (s:t) :=
    match s with
    | Crep s n => concatn s (N.to_nat n)
    | Capp s1 s2 => append (to_string s1) (to_string s2)
    end.

  (** [reduce s] removes trailling spaces.
      TODO: avoid generating them *)
  Fixpoint xreduce (s:t) :=
    match s with
    | Crep s1 n => if String.eqb " " s1 then None
                  else Some s
    | Capp s1 s2 => match xreduce s2 with
                    | None => xreduce s1
                    | Some s2 => Some (Capp s1 s2)
                    end
    end.

  Definition reduce (s:t) :=
    match xreduce s with
    | None => Crep "" 0
    | Some s => s
    end.

  Section S.
    Variable Out : Type. (* out_channel *)
    Variable output_string : Out -> string -> Out.

    Fixpoint output_rep (o:Out) (s:string) (n:nat) :=
      match n with
      | O => o
      | S n => let o := output_string o s in
               output_rep o s n
      end.

    Fixpoint output (o:Out) (s:t) :=
      match s with
      | Crep s n   => output_rep o s (N.to_nat n)
      | Capp s1 s2 => output (output o s1) s2
      end.

  End S.

  
  Fixpoint width (s:t) :=
    (match s with
    | Crep s n => (N.to_nat n) * (String.length s)
    | Capp s1 s2 => width s1 + width s2
    end)%nat.

  Lemma length_append : forall s1 s2,
      String.length (s1 ++ s2) =
        (String.length s1 + String.length s2)%nat.
  Proof.
    induction s1.
    - simpl. reflexivity.
    - simpl. intros. rewrite IHs1.
      reflexivity.
  Qed.

  Lemma width_to_string : forall s, width s = String.length (to_string s).
  Proof.
    induction s; simpl.
    - induction (N.to_nat n).
      + simpl. reflexivity.
      + simpl.  rewrite length_append.
        lia.
    -  rewrite length_append.
       lia.
  Qed.

End  CString.

Import CString.

Module Box.

  Record t :=
    mk
      {
        content : list CString.t;  (* each CString.t is just one line (no newline) *)
        height  : N;               (* All the CString.t have the same width *)
        width   : N
      }.

  Record wf (b : t) :=
    {
      wf_h : List.length (content b) = N.to_nat (height b);
      wf_w : Forall (fun s => CString.width s = N.to_nat (width b)) (content b);
    }.

  
  Definition pad n := Crep " " n.

  Definition augment_width_left  (delta:N) (l:list CString.t)  :=
    List.map (fun s => Capp (pad delta) s) l.

  Definition augment_width_right  (l:list CString.t) (delta:N) :=
    List.map (fun s => Capp  s (pad delta)) l.


  Fixpoint cat_content (w1:N) (l1:list CString.t) (w2:N) (l2:list CString.t) :=
    match l1, l2 with
    | nil,nil  => nil
    | nil, _   => augment_width_left w1 l2
    | _  , nil => augment_width_right  l1 w2
    | s1 :: l1', s2:: l2' => Capp s1 s2 :: cat_content w1 l1' w2 l2'
    end.

  Lemma length_augment_width_left : forall w l,
      Datatypes.length (augment_width_left w l) = Datatypes.length l.
  Proof.
    induction l; simpl;auto.
  Qed.

  Lemma length_augment_width_right : forall w l,
      Datatypes.length (augment_width_right l w) = Datatypes.length l.
  Proof.
    induction l; simpl;auto.
  Qed.

  Lemma length_cat_content : forall w1 w2 l1 l2,
      List.length (cat_content w1 l1 w2 l2) =
        Nat.max (List.length l1) (List.length l2).
  Proof.
    induction l1; simpl;auto.
    - destruct l2 ; simpl;auto.
      f_equal.
      apply length_augment_width_left .
    - destruct l2 ; simpl;auto.
      f_equal.
      apply length_augment_width_right.
  Qed.

  Definition cat (p1 p2:t) :=
    mk
      (cat_content (width p1) (content p1) (width p2) (content  p2))
      (N.max (height p1) (height p2))
      (N.add (width p1) (width p2)).

  Lemma wf_cat :
    forall p1 p2
           (WF1 : wf p1)
           (WF2 : wf p2),
      wf (cat p1 p2).
  Proof.
    unfold cat.
    intros.
    constructor; simpl.
    - rewrite length_cat_content.
      destruct WF1; destruct WF2.
      lia.
    - destruct WF1.
      destruct WF2.
      revert wf_w0 wf_w1.
      generalize (content p2) as l2.
      generalize (content p1) as l1.
      intros l1 l2 ALL.
      revert l2.
      induction ALL.
      + intros.
        simpl.
        destruct l2.
        constructor.
        unfold augment_width_left.
        rewrite Forall_map.
        revert wf_w1.
        apply Forall_impl.
        simpl. lia.
      + simpl.
        destruct l2.
        { intros.
        constructor.
        simpl; lia.
        revert ALL.
        unfold augment_width_right.
        rewrite Forall_map.
        apply Forall_impl.
        simpl. lia.
        }
        { intros.
          inv wf_w1.
          constructor;auto.
          simpl. lia.
        }
  Qed.

  Definition augment_width_position (delta:N) (l:list CString.t) (p:position) :=
    match p with
    | Left => augment_width_right l delta
    | Right => augment_width_left delta l
    | Middle => let dl := (N.div2 delta)%N in
                let dr := (dl + N.b2n (N.odd delta))%N in
                List.map (fun s => Capp (pad dl) (Capp s (pad dr))) l
    end.

  Definition stack (p1 p2:t) (p:position) :=
      let c1 := augment_width_position (width p2 - width p1) (content p1) p in
      let c2 := augment_width_position (width p1 - width p2) (content p2) p in
      mk (List.app c1 c2) ((height p1) + (height p2)) (N.max (width p1) (width p2)).

  Lemma length_augment_width_position : forall n l p,
      List.length (augment_width_position n l p) =
        List.length l.
  Proof.
    destruct p; simpl.
    - rewrite length_augment_width_right.
      reflexivity.
    - rewrite length_augment_width_left.
      reflexivity.
    - rewrite length_map.
      reflexivity.
  Qed.

  Lemma N_odd_b2n : forall b,
      N.odd (N.b2n b) = b.
  Proof.
    destruct b; reflexivity.
  Qed.

  
  Lemma wf_stack :
    forall p1 p2 p
           (WF1 : wf p1)
           (WF2 : wf p2),
      wf (stack p1 p2 p).
  Proof.
    unfold stack.
    intros.
    constructor; simpl;auto.
    - rewrite length_app. rewrite! length_augment_width_position.
      destruct WF1 ; destruct WF2. lia.
    - rewrite Forall_app.
      split;auto.
      { destruct p; simpl.
      + apply Forall_map.
        destruct WF1.
        revert wf_w0.
        apply Forall_impl.
        simpl. intros.
        lia.
      + apply Forall_map.
        destruct WF1.
        revert wf_w0.
        apply Forall_impl.
        simpl. intros.
        lia.
      + apply Forall_map.
        destruct WF1.
        revert wf_w0.
        apply Forall_impl.
        intros.
        simpl.
        rewrite H. clear H.
        assert (D2 := N.div2_odd (width p2 - width p1)).
        lia.
      }
      { destruct p; simpl.
      + apply Forall_map.
        destruct WF2.
        revert wf_w0.
        apply Forall_impl.
        simpl. intros.
        lia.
      + apply Forall_map.
        destruct WF2.
        revert wf_w0.
        apply Forall_impl.
        simpl. intros.
        lia.
      + apply Forall_map.
        destruct WF2.
        revert wf_w0.
        apply Forall_impl.
        intros.
        simpl.
        rewrite H. clear H.
        assert (D2 := N.div2_odd (width p1 - width p2)).
        lia.
      }
  Qed.

  
  Fixpoint keep (s:string) (n:nat) :=
    match n with
    | O => EmptyString
    | S n => match s with
             | EmptyString =>  EmptyString
             | String a s => String a (keep s n)
             end
    end.


  Definition dup_until (s:string) (w:N) :=
    let len := N.of_nat (String.length s) in
    let nb := (w / len)%N in
    let rem := (w mod len)%N in
    let rst := keep s (N.to_nat rem) in
    Capp (Crep s nb) (Cstr rst).

  Definition of_empty (s:string) :=
    match s with
    | EmptyString => String space EmptyString
    | _           => s
    end.


  Definition frame (tp:string) (l:string) (b:t) : t :=
    let l := of_empty l in
    let s := of_empty tp in
    let c := List.map (fun s => Capp (Cstr l) (Capp s (Cstr l))) (content b) in
    let w := ((width b) + 2 * (N.of_nat (String.length l)))%N in
    let t := dup_until s w in
    mk (t::(List.app c (t::nil))) w (height b + 2)%N.

  
  Fixpoint pict_of_box (b:box) :=
    match b with
    | Bemp   => mk nil 0%N 0%N
    | Bstr s => mk (Cstr s::nil) 1%N (N.of_nat (String.length s))
    | Bcat b1 b2 => cat (pict_of_box b1) (pict_of_box b2)
    | Bstack b1 b2 p => stack (pict_of_box b1) (pict_of_box b2) p
    | Bframe tp l b   => frame tp l (pict_of_box b)
    end.

  Fixpoint xto_string (s: list CString.t) :=
    match  s with
    | nil => ""%string
    | e::nil => CString.to_string e
    | e1::e2 => String.append (CString.to_string e1) (String lf (xto_string e2))
    end.

  Fixpoint xoutput {Out:Type} (output_string : Out -> string -> Out) (o:Out) (s : list CString.t) :=
    match s with
    | nil => o
    | e::l =>
        let o := (CString.output _ output_string o e) in
        let o1 := output_string o nl in
        xoutput output_string o1 l
    end.

  Definition to_string (s:t) := xto_string (content s).

  Definition output {Out:Type} (output_string : Out -> string -> Out) (o:Out) (s:t) :=
    xoutput output_string o
      (List.map reduce (content s)).

End Box.


Definition pp (b:box) := Box.to_string (Box.pict_of_box b).

Definition output {Out:Type} (output_string : Out -> string -> Out) (o:Out) (b:box) :=
  Box.output output_string o (Box.pict_of_box b).

Section PPLIST.
  Context {A: Type}.
  Variable sep : box.
  Variable pp_elt : A -> box.

  Fixpoint pp_list (l:list A) : box :=
    match l with
    | nil => Bemp
    | e::nil => pp_elt e
    | e1::l  => Bcat (pp_elt e1) (Bcat sep (pp_list l))
    end.

  (** vertical stacking the elements *)
  Fixpoint pp_slist (l:list A) : box :=
    match l with
    | nil => Bemp
    | e::nil => pp_elt e
    | e1::l  => Bstack (pp_elt e1) (pp_slist l) Left
    end.


End PPLIST.

Definition pp_option {A: Type} (pp_elt : A -> box) (v:option A) :=
  match v with
  | None => Bstr "."
  | Some v => pp_elt v
  end.

Definition pp_pair {A B:Type} (sep:box) (pp_A : A -> box) (pp_B: B -> box) (v: A * B): box :=
  Bcat (pp_A (fst v)) (Bcat sep (pp_B (snd v))).

Module Log.
  (** Just named boxed *)

  Definition t:= box.

  Definition empty : t := Bemp.

  Definition add_entry (s:box) (v:box) (l:t) :=
    Bstack
        l (Bstack
             (Bcat s (Bstr ":")) v Left)  Left.

  Definition pp {Out:Type} (output_string : Out -> string -> Out) (o:Out) (l:t) :=
    output output_string o l.
End  Log.
