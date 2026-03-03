(* Imperative Imp1 *)
From Coq Require Import Bool List String PArith Lia.
From compcert Require Import Integers Coqlib.
From BarocqComp Require Import Denot Benum  Barray Brecord OptionMonad Maps2 Utils Syntax Types Typing.
From BarocqComp Require Import Imp1.
From BarocqComp Require Printer Pp.

Section MAPOPT.
  Context {A B: Type}.
  Variable F : A -> option B.

  Fixpoint mapopt (l:list A) : list B :=
    match l with
    | nil => nil
    | e::l => match F e with
              | None => mapopt l
              | Some e' => e'::mapopt l
                  end
    end.
End MAPOPT.


Section Forall2.
  Context {A B: Type}.
  Variable (R : A -> B -> Prop).

  Fixpoint forall2 (l1: list A) (l2:list B) :=
    match l1,l2 with
    | nil , nil => True
    | e1::l1 , e2::l2 => R e1 e2 /\ forall2 l1 l2
    | _   ,  _ => False
    end.
End Forall2.

Section MAPACC.
  Context {A B MEM:Type}.
  Variable F : A -> MEM -> option (B * MEM).

  Fixpoint mmap_fold (l:list A) (m:MEM) : option (list B * MEM) :=
    match l with
    | nil => Some(nil,m)
      | e::l => let* (fe,m1) := F e m in
                let* (l ,mr) := mmap_fold l m1 in
                Some (fe::l,mr)
      end.

End MAPACC.


Inductive cedge :=
  | CField (id:ident)
  | CIndex (i:Integers.Int64.int).

Definition cedge_eqb (ce1 ce2: cedge) : bool :=
  match ce1, ce2 with
  | CField f1, CField f2 =>
      if Ident.eq_dec f1 f2 then true else false
  | CIndex i1, CIndex i2 => Int64.eq i1 i2
  | _, _ => false
  end.

Inductive pval : typ -> Type :=
| PBool  : forall (b:bool), pval TBool
| PInt32 : forall (s:signedness) (i:int), pval (TInt32 s)
| PInt64 : forall (s:signedness) (i:int64), pval (TInt64 s)
| PEnum  : forall (id:ident) (l:list Ident.ident) (c : enum l), pval (TEnum id l)
. (* id should not be there *)

Definition addr := positive.

Inductive ptr : typ -> Type :=
| PtrA : forall (a:addr) (ty:typ), ptr (TArray ty)
| PtrR : forall (a:addr) (id:ident) (l : smaplist typ), ptr (TRecord id l)
| PtrF : forall (id:ident) (l:list typ) (r:typ), ptr (TFun l r)
| PtrAbs : forall (a:addr) (id:ident), ptr (TAbs id).

Definition is_fun_ptr {ty:typ} (p : ptr ty) :=
  match p with
  | PtrA _ _ | PtrR _ _ _ | PtrAbs _ _ => false
  | PtrF _ _ _ => true
  end.

Definition get_addr_of_ptr {ty:typ} (p:ptr ty) : addr + ident :=
  match p with
  | PtrA a _ => inl a
  | PtrR a _ _ => inl a
  | PtrF id _ _ => inr id
  | PtrAbs a _ => inl a
  end.

Definition addr_of_ptr {ty:typ} (p:ptr ty) : option addr :=
  match p with
  | PtrA a _ => Some a
  | PtrR a _ _ => Some a
  | PtrF id _ _ => None
  | PtrAbs a _ => Some a
  end.



Definition set_addr_of_ptr {ty:typ} (p:ptr ty) (i:positive) : ptr ty :=
  match p with
  | PtrA _ ty => PtrA i ty
  | PtrR _ id l => PtrR i id l
  | PtrF id l r   => PtrF id l r
  | PtrAbs _ id => PtrAbs i id
  end.


Section S.
  Variable arch : Target.archi.
  Variable abs : Maps.PMap.t Type.

  Variable abs_dec : forall x,
    forall (v1 v2: SMap.get x abs), {v1 = v2} + {v1 <> v2}.

  (* The semantics is dynamically typed. *)

  Inductive val : typ -> Type :=
  | Vprim  : forall (ty:typ) (p:pval ty), val ty
  | Vptr  : forall (ty:typ) (p:ptr ty), val ty.

  Inductive mval : typ -> Type :=
  | MArray : forall (ty:typ) (a : array (val ty)), mval (TArray ty)
  | MRecord : forall (id:ident) (rty :smaplist typ)
                     (r :grecord val rty), mval (TRecord id rty) (* id should not be there *)
  | MAbs : forall (id:ident),SMap.get id abs -> mval (TAbs id).

  Definition ptr_of_val (ty:typ) (v:val ty) :=
    match v with
    | Vprim _ _ => None
    | Vptr ty ptr => Some (existT _ ty ptr)
    end.

  Definition decompose_mval_t (ty:typ) :=
    match ty with
    | TArray ty' => array (val ty')
    | TRecord i l => grecord val l
    | TAbs   t    => eval_typ abs (TAbs t)
    | _           => (False:Type)
    end.

  Definition decomp_mval (ty: typ) (v:mval ty) : decompose_mval_t ty.
  Proof.
    destruct v.
    - apply a.
    - apply r.
    - apply g.
  Defined.

  Definition decomp_val_t (ty:typ) : Type :=
    match ty with
    | TArray ty' => ptr  ty
    | TRecord i l => ptr ty
    | TFun _ _    => ptr ty
    | TAbs  _     => ptr ty
    | TBool  | TInt32 _ | TInt64 _ | TEnum _ _ => pval ty
    end.

  Definition decomp_val (ty: typ) (v:val ty) : decomp_val_t ty.
  Proof.
    destruct v.
    - destruct ty; auto.
      inv p. inv p.
      inv p. inv p.
    - destruct ty; auto.
      inv p. inv p.
      inv p. inv p.
  Defined.

  Definition decomp_pval_t (ty:typ) : Type :=
    match ty with
    | TBool  => bool
    | TInt32 _ => Int.int
    | TInt64 _ => Int64.int
    | TEnum i l => enum l
    |  _        => (False:Type)
    end.

  Definition decomp_pval (ty: typ) (v:pval ty) : decomp_pval_t ty.
  Proof.
    destruct v.
    - exact b.
    - exact i.
    - exact i.
    - exact c.
  Defined.

  Lemma pval_eq_dec_cast : forall (ty1:typ) (v1: pval ty1)  (ty2:typ) (v2: pval ty2)
                                (EQ: ty2 = ty1), {v1 = cast (f_equal pval EQ) v2 } +
                                                   {v1 <> (cast (f_equal pval EQ) v2)}.
  Proof.
    destruct v1, v2; intros; try discriminate.
    -
      assert (EQ = eq_refl).
      { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst.
      destruct (bool_dec b b0).
      + left.
        subst. reflexivity.
      + right. simpl. congruence.
    - destruct (signedness_eq_dec s0 s); try congruence.
      subst.
      assert (EQ = eq_refl).
      { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst.
      destruct (Int.eq_dec i i0).
      + left.
        subst. reflexivity.
      + right. simpl. congruence.
    - destruct (signedness_eq_dec s0 s); try congruence.
      subst.
      assert (EQ = eq_refl).
      { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst.
      destruct (Int64.eq_dec i i0).
      + left.
        subst. reflexivity.
      + right. simpl. congruence.
    - destruct (Ident.eq_dec id0 id); try congruence.
      destruct (list_eq_dec Ident.eq_dec l0 l); try congruence.
      subst.
      assert (EQ = eq_refl).
      { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst.
      destruct (enum_eq_dec c c0).
      + left. subst ; reflexivity.
      + right ; simpl.  intro.
        inversion H.
        apply Eqdep_dec.inj_pair2_eq_dec in H1.
        congruence.
        apply (list_eq_dec Ident.eq_dec).
  Qed.

  Lemma pval_eq_dec : forall (ty1:typ) (v1 v2 : pval ty1), {v1 = v2 } +
                                                   {v1 <> v2}.
  Proof.
    intros.
    change v2 with (cast (f_equal pval eq_refl) v2).
    apply (pval_eq_dec_cast  _ v1 _ v2 eq_refl).
  Defined.



  Lemma ptr_eq_dec_cast : forall (ty1:typ) (v1: ptr ty1)  (ty2:typ) (v2: ptr ty2)
                                (EQ: ty2 = ty1), {v1 = cast (f_equal ptr EQ) v2 } +
                                                   {v1 <> (cast (f_equal ptr EQ) v2)}.
  Proof.
    destruct v1, v2; intros; try discriminate.
    - assert (ty0 = ty) by congruence ; subst.
      assert (EQ = eq_refl).
      { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst.
      destruct (Pos.eq_dec a a0).
      + left.
        subst. reflexivity.
      + right. simpl. congruence.
    - assert (id0 = id) by congruence.
      assert (l0 = l) by congruence.
      subst.
      assert (EQ = eq_refl).
      { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst.
      destruct (Pos.eq_dec a a0).
      left; simpl. congruence.
      simpl. right ; congruence.
    - assert (l0 = l) by congruence.
      assert (r0 = r) by congruence.
      subst.
      assert (EQ = eq_refl).
      { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst.
      simpl.
      destruct (Ident.eq_dec id id0); subst.
      left ; reflexivity.
      right. congruence.
    - assert (id0 = id) by congruence.
      subst.
      assert (EQ = eq_refl).
      { apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst. simpl.
      destruct (Pos.eq_dec a a0).
      left ; congruence.
      right; congruence.
  Qed.

  Lemma ptr_eq_dec : forall (ty1:typ) (v1: ptr ty1) (v2: ptr ty1)
    , {v1 = v2 } + {v1 <> v2}.
  Proof.
    intros.
    change v2 with (cast (f_equal ptr eq_refl) v2).
    apply (ptr_eq_dec_cast  _ v1 _ v2 eq_refl).
  Defined.

  Lemma val_eq_dec_cast : forall (ty1:typ) (v1: val ty1)  (ty2:typ) (v2: val ty2)
                                (EQ: ty2 = ty1), {v1 = cast (f_equal val EQ) v2 } +
                                                   {v1 <> (cast (f_equal val EQ) v2)}.
  Proof.
    destruct v1, v2; intros; try discriminate.
    - destruct (pval_eq_dec_cast _ p _ p0 EQ).
      + left.
        subst. reflexivity.
      + right.
        subst. simpl in *.
        intro.
        inv H.
        apply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
        apply typ_eq_dec.
    -  subst.
       right. simpl.
       congruence.
    - subst.
      simpl. right ; congruence.
    - subst.
      simpl.
      destruct (ptr_eq_dec _ p p0).
      left ; congruence.
      right. repeat intro.
      inv H.
      apply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
      apply typ_eq_dec.
  Qed.

  Lemma val_eq_dec : forall (ty1:typ) (v1: val ty1) (v2: val ty1)
    , {v1 = v2 } + {v1 <> v2}.
  Proof.
    intros.
    change v2 with (cast (f_equal val eq_refl) v2).
    apply (val_eq_dec_cast  _ v1 _ v2 eq_refl).
  Defined.


  Lemma mval_eq_dec_cast : forall (ty1:typ) (v1: mval ty1)  (ty2:typ) (v2: mval ty2)
                                (EQ: ty2 = ty1), {v1 = cast (f_equal mval EQ) v2 } +
                                                   {v1 <> (cast (f_equal mval EQ) v2)}.
  Proof.
    destruct v1, v2; intros; try discriminate.
    - assert (ty0 = ty) by congruence ; subst.
      assert (EQ = eq_refl).
      {  apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst.
      destruct (list_eq_dec (val_eq_dec _) a a0).
      subst.
      left ; reflexivity.
      right.  simpl.
      intro.
      inv H.
      apply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
      apply typ_eq_dec.
    - assert (id0 = id) by congruence.
      assert (rty = rty0) by congruence.
      subst.
      assert (EQ = eq_refl).
      {  apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst.
      simpl.
      destruct (grecord_eq_dec val_eq_dec r r0).
      left ; congruence.
      right. intro. inv H.
      apply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
      apply list_eq_dec. decide equality.
      apply typ_eq_dec.
      apply string_dec.
    - assert (id0 = id) by congruence ; subst.
      assert (EQ = eq_refl).
      {  apply Eqdep_dec.UIP_dec. apply typ_eq_dec. }
      subst. simpl.
      destruct (abs_dec id g g0).
      left ; congruence.
      right. intro. inv H.
      apply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
      apply Ident.eq_dec.
  Qed.

  Lemma mval_eq_dec : forall (ty1:typ) (v1: mval ty1) (v2: mval ty1)
    , {v1 = v2 } + {v1 <> v2}.
  Proof.
    intros.
    change v2 with (cast (f_equal mval eq_refl) v2).
    apply (mval_eq_dec_cast  _ v1 _ v2 eq_refl).
  Defined.

  Definition memt := addr -> option {ty : typ & mval ty}.

  Record mem : Type := mkmem {
                           _mem  : memt;
                           _fresh : addr;
                           _wf_fresh : (forall a, (_fresh <= a)%positive -> _mem a  = fail);
                         }.

  Definition sig_mval_eq_dec (v1 v2: {ty:typ & mval ty}) : { v1 = v2} + { v1 <> v2}.
  Proof.
    destruct v1, v2.
    destruct (typ_eq_dec x x0).
    - subst.
      destruct (mval_eq_dec _ m  m0).
      left ; congruence.
      right; repeat intro.
      apply Eqdep_dec.inj_pair2_eq_dec in H; auto.
      apply typ_eq_dec.
    - right ; repeat intro.
      destruct m,m0; try congruence.
  Defined.

  Program Fixpoint xeq_mem (f1 f2:memt) (mx:positive) (DEC : Acc Pos.lt mx) : bool:=
    if option_eq_dec sig_mval_eq_dec (f1 mx) (f2 mx)
    then
      if Pos.eq_dec mx xH then true
      else xeq_mem f1 f2 (Pos.pred mx) (Acc_inv DEC _)
    else false.
  Next Obligation.
  lia.
  Defined.

  Definition eq_mem (m1 m2: mem) :=
    xeq_mem (_mem m1) (_mem m2) (Pos.max (_fresh m1) (_fresh m2)) (Plt_wf (Pos.max (_fresh m1) (_fresh m2))).

  Fixpoint typ_of_fun (l:list typ) (r:typ) :=
    match l with
    | nil => unit -> option (val r * mem)
    | tx::tparams' => val tx ->
                      match tparams' with
                      | nil => option (val r * mem)
                      | _ :: _ => typ_of_fun tparams' r
                      end
    end.

  Fixpoint eval_app (tparams:list typ) (r:typ) (f: typ_of_fun tparams r)
    (args: DList.dlist val tparams) {struct args} : option (val r * mem).
  Proof.
    destruct args.
    - simpl in f. apply (f tt).
    - simpl in f.
      destruct l.
      + apply (f e).
      + apply (eval_app _ _ (f e) args).
  Defined.


  Definition Fun (args: list typ) (tret: typ) := mem -> typ_of_fun args tret.

  Inductive gval :=
  | GFun  (args : list typ) (tret : typ) (fct: Fun args tret)
  | GConst  (ty:typ) (v : val ty).


  Definition genv := ident -> option gval.


  Definition  get {ty:typ} (p:ptr ty) (m:mem) : option (mval ty):=
    let* a := addr_of_ptr p in
    let* ma := _mem m a in
    let (tv,v) := ma in
    match typ_eq_dec tv ty with
    | left EQ => Some (cast (f_equal mval EQ) v)
    | _  => fail
    end.

  Definition eval_pval {ty:typ} (p:pval ty) : eval_typ abs ty :=
    match p with
    | PBool b => b
    | PInt32 _ i => i
    | PInt64 _ i => i
    | PEnum _ _ e => e
    end.

  Definition eval_val_pval {ty:typ} (p:val ty) : option (eval_typ abs ty) :=
    match p with
    | Vprim _ pv => Some (eval_pval pv)
    |  _        => fail
    end.


  Definition decomp_ptr_t (ty: typ)  :=
    match ty with
    | TArray ty' => addr
    | TRecord i l => addr
    | TFun _ _    => ident
    | TAbs  _     => addr
    |    _        => (False:Type)
    end.

  Definition decomp_ptr (ty: typ) (v:ptr ty) : decomp_ptr_t ty.
  Proof.
    destruct v; auto.
  Defined.




  Lemma ptr_not_prim : forall ty (p:ptr ty),
      typ_is_prim ty = true -> False.
  Proof.
    intros.
    inv p; simpl in H; discriminate.
  Qed.

  Lemma pval_is_prim : forall ty (p:pval ty),
      typ_is_prim ty = true.
  Proof.
    intros.
    inv p; reflexivity.
  Qed.

  Definition is_primitive_val (ty:typ) (v:val ty) : bool :=
    match v with
    | Vprim _ _ => true
    | Vptr _ _  => false
    end.


  Definition  get_fun {args :list typ} {ret : typ}  (p:ptr (TFun args ret)) (ge:genv) : option (mem -> typ_of_fun args ret).
  Proof.
    apply decomp_ptr in p.
    simpl in p.
    eapply bind.
    apply (ge p).
    intro.
    destruct X as [args' tret' |] ; [|apply fail].
    unfold Fun in fct.
    destruct (typ_eq_dec (TFun args' tret') (TFun args ret)).
    apply Some. inv e. apply fct.
    apply fail.
  Defined.

  (*    (* [eval_mem] recursively builds a value from a val *)
    Fixpoint eval_mem (ge:genv) (m : t) (ty:typ) (p:val ty) (vl : eval_typ abs ty) {struct ty} : Prop.
    Proof.
      destruct ty.
      (* primitive types *)
      { apply eval_val_pval in p. apply (p = OK vl). }
      { apply eval_val_pval in p; apply (p = OK vl). }
      { apply eval_val_pval in p; apply (p = OK vl). }
      { (* array => we have a pointer *)
        apply decomp_val in p.
        simpl in p.
        destruct  (get p m) as [v|]; [|apply False].
        (* We load from memory *)
        specialize (eval_mem ge m ty).
        apply decomp_mval in v.
        simpl in v.
        simpl in vl.
        apply (Forall2 eval_mem v vl).
      }
      { apply eval_val_pval in p ; apply (p = OK vl). }
      { (* a record *)
        apply decomp_val in p.
        simpl in p.
        destruct (get p m) as [r|] ; [| apply False].
        apply decomp_mval in r.
        simpl in r.
        unfold eval_typ in vl. fold eval_typ in vl.
        unfold eval_recordtyp in vl.
        apply (grecord_rel (eval_mem ge m) r vl).
      }
      { (* a function *)
        apply decomp_val in p.
        simpl in p.
        destruct (get_fun p ge)as [f|];[|apply False].
        specialize (f  m).
        unfold eval_typ in vl.
        fold eval_typ in vl.
        exact (forall (a1:DList.dlist val l) (a2:DList.dlist (eval_typ abs) l),
                  DList.forall2 (eval_mem ge m) l a1 a2 ->
                  res_rel (fun v vl => eval_mem ge (snd v) ty (fst v) vl)
                    (eval_app _ _ f a1) (DList.eval_app _ _ vl a2)).
      }
      {
        apply decomp_val in p.
        simpl in p.
        destruct (get p m) as [a|] ; [|apply False].
        apply decomp_mval in a.
        simpl in a. simpl in vl.
        apply (vl = a).
      }
    Defined.
   *)
  (** Well-formedness *)

  Definition ge_has_fun (ge:genv) {ty :typ} (p:ptr ty) : bool:=
    match p with
    | PtrF fid _ _ => match ge fid with
                      | None => false
                      | Some f    =>
                          match f with
                          | GFun _ _ _ => true
                          | _             => false
                          end
                      end
    | _   => false
    end.



  Inductive wf_val (ge:genv) (m:mem) : forall (ty:typ), val ty -> Prop :=
  (** primitive values are well-formed *)
  | WFVprim : forall ty v, wf_val ge m ty (Vprim ty v)
  (* Pointer are well-formed if they are not dangling *)
  | WFVPtr  : forall ty (p:ptr ty), ge_has_fun ge p = true \/ isSome (get p m)  -> wf_val ge m ty (Vptr ty p).


  Definition wf_mval (ge:genv) (m:mem) (ty:typ) (mv:mval ty) :=
    match mv with
    | MArray ty a => List.Forall (wf_val ge m ty) a
    | MRecord id l r => Brecord.Forall (wf_val ge m) r
    | MAbs _ _ => True
    end.

  Definition wf (ge:genv) (m: mem) :=
    forall a ty mv,
      _mem m a = Some (existT _ ty mv) -> wf_mval ge m ty mv.

  Definition defs_has_typ (d:gval) (ty:typ)  : Prop :=
    match d with
    | GFun args tret _ => ty = TFun args tret
    | GConst ty' _      => ty = ty'
    end.


  (*** Wellformed properties *)

  Lemma decomp_mval_eq (ty:typ) (v: mval ty):
    match ty as ty' return ty = ty'-> Prop with
    | TArray ty' => fun EQ => exists a, cast (f_equal mval EQ) v = MArray ty' a
    | TRecord i l =>fun EQ => exists r, cast (f_equal mval EQ) v = MRecord i l r
    | TAbs t      =>fun EQ => exists a, cast (f_equal mval EQ) v = MAbs t a
    | TFun l r    =>  fun _ => False
    | TBool       => fun EQ => False
    | TInt32 s      => fun EQ => False
    | TInt64 s      => fun EQ => False
    | TEnum i l     => fun EQ => False
    end eq_refl .
  Proof.
    destruct v.
    -  eexists ; reflexivity.
    - eexists; reflexivity.
    - eexists ; reflexivity.
  Qed.

  Lemma wf_val_get : forall ge m ty (v:mval ty) p ,
      wf ge m ->
      get p m = Some v -> wf_mval ge m ty v.
  Proof.
    intros.
    unfold wf in H.
    unfold get in H0.
    destruct (addr_of_ptr p) eqn:EQ; try discriminate.
    simpl in H0.
    destruct (_mem m a) eqn:MA; try discriminate.
    simpl in H0. destruct s. destruct (typ_eq_dec x ty); try discriminate.
    subst. inv H0.
    eauto.
  Qed.

  Lemma ptr_array_has_fun : forall ge ty (p:ptr (TArray ty)),
      ge_has_fun ge p = false.
  Proof.
    unfold ge_has_fun.
    intros.
    remember (TArray ty) as tty.
    destruct p; try discriminate.
    reflexivity.
  Qed.

  Lemma ptr_record_has_fun : forall ge id lty (p:ptr (TRecord id lty)),
      ge_has_fun ge p = false.
  Proof.
    unfold ge_has_fun.
    intros.
    remember (TRecord id lty) as tty.
    destruct p; try discriminate.
    reflexivity.
  Qed.

  Lemma decomp_ptr_eq (ty:typ) (v: ptr ty):
    match ty as ty' return ty = ty'-> Prop with
    | TArray ty' => fun EQ => exists a, cast (f_equal ptr EQ) v = PtrA a ty'
    | TRecord i l =>fun EQ => exists a, cast (f_equal ptr EQ) v = PtrR a i l
    | TAbs t      =>fun EQ => exists a, cast (f_equal ptr EQ) v = PtrAbs a t
    | TFun l r    =>  fun EQ => exists id, cast (f_equal ptr EQ) v = PtrF id l r
    | TBool       => fun EQ => False
    | TInt32 s      => fun EQ => False
    | TInt64 s      => fun EQ => False
    | TEnum i l     => fun EQ => False
    end eq_refl .
  Proof.
    destruct v.
    -  eexists. reflexivity.
    -  eexists. reflexivity.
    -  eexists. reflexivity.
    -  eexists. reflexivity.
  Qed.


  (*    Fixpoint eval_mem_ok (ge: genv) (m:t) (WF: wf ge m) (ty:typ) :
      forall  v
             (WFV: wf_val ge m ty v)
      ,
        exists vl, eval_mem ge m ty v vl.
    Proof.
      intros.
      destruct ty; simpl.
      - inv WFV.
        apply Eqdep_dec.inj_pair2_eq_dec in H1;[|apply typ_eq_dec].
        subst. simpl. eexists ; reflexivity.
        inv p.
      - inv WFV.
        apply Eqdep_dec.inj_pair2_eq_dec  in H1;[|apply typ_eq_dec].
        subst. simpl. eexists ; reflexivity.
        inv p.
      - inv WFV.
        apply Eqdep_dec.inj_pair2_eq_dec  in H1;[|apply typ_eq_dec].
        subst. simpl. eexists ; reflexivity.
        inv p.
      - inv WFV.
        inv v0.
        apply Eqdep_dec.inj_pair2_eq_dec  in H;[|apply typ_eq_dec].
        subst. simpl.
        destruct H1 as [H1 | H1].
        rewrite ptr_array_has_fun  in H1. discriminate.
        unfold isSome in H1. destruct H1 as (x & EQ).
        specialize (eval_mem_ok ge m WF ty).
        rewrite EQ.
        specialize (decomp_mval_eq _ x).
        simpl.
        intros (a & EQ1).
        subst.
        simpl.
        unfold wf in WF.
        apply wf_val_get with (ge:=ge) in EQ; auto.
        unfold wf_mval in EQ.
        induction EQ.
        + exists nil. constructor.
        +
        destruct (eval_mem_ok _ H) as (vl & EVAL).
        destruct IHEQ  as (vl1 & ALL).
        intros; auto.
        exists (vl ::vl1).
        constructor ; auto.
      - inv WFV.
        apply Eqdep_dec.inj_pair2_eq_dec in H1;[|apply typ_eq_dec].
        subst. simpl. eexists ; reflexivity.
        inv p.
      - inv WFV.
        inv v0.
        apply Eqdep_dec.inj_pair2_eq_dec  in H;[|apply typ_eq_dec].
        subst. simpl.
        destruct H1 as [H1 | H1].
        rewrite ptr_record_has_fun  in H1. discriminate.
        unfold isSome in H1. destruct H1 as (x & EQ).
        rewrite EQ.
        specialize (decomp_mval_eq _ x).
        simpl.
        intros (a & EQ1).
        subst.
        simpl.
        unfold wf in WF.
        apply wf_val_get with (ge:=ge) in EQ; auto.
        unfold wf_mval in EQ.
        clear p.
        revert a EQ.
        clear i.
        induction l.
        + simpl. exists tt. auto.
        + simpl.
          intros.
          destruct a0 as (fd & g).
          simpl in *.
          intros. destruct EQ as (WFV & ALL).
          destruct (eval_mem_ok ge m WF _ _  WFV) as (vl & EVAL).
          destruct IHl with (a:=g)  as (vl1 & ALL1); auto.
          destruct a as (fid,ty); simpl in *.
          exists (Field fid vl,vl1).
          simpl ; auto.
      - inv WFV.
        inv v0.
        apply Eqdep_dec.inj_pair2_eq_dec in H;[|apply typ_eq_dec].
        subst.
        destruct H1.
        simpl.
        destruct (get_fun p ge) as [fct|] eqn:GF.
        clear p H GF.
        induction l.
        { simpl in *.
          destruct (fct  m tt).



        simpl.
        unfold ge_has_fun in H.
        specialize (decomp_ptr_eq _ p).
        simpl. intros (id & EQ).
        subst.
        unfold get_fun.
        simpl.
        destruct (ge id); try discriminate.
        simpl.
        destruct d; try discriminate.


        unfold decomp_ptr.
        destruct p; try discriminate.



        simpl.
   *)

  Definition _set (a:addr) (ty:typ) (v:mval ty) (m: addr -> option {ty:typ & mval ty}) :=
    fun x => if Pos.eq_dec a x then
               Some (existT _ _ v)
             else m x.

  Lemma set_lt : forall a ty (v:mval ty) m,
      (a < (_fresh m))%positive ->
      forall a1, (_fresh m <= a1)%positive -> _set a ty v (_mem m) a1 = fail.
  Proof.
    unfold _set.
    intros.
    destruct (Pos.eq_dec a a1).
    subst.
    lia.
    apply _wf_fresh. lia.
  Qed.

  Definition set {ty: typ} (p:ptr ty) (v:mval ty) (m:mem) : option mem :=
    let* a := addr_of_ptr p
    in match Coqlib.plt a (_fresh m) with
       | left LT => Some {| _mem := _set a ty v (_mem m); _fresh := _fresh m; _wf_fresh := set_lt a ty v m LT |}
       | right _ => fail
       end.

  Lemma alloc_lt : forall m a,
      (Pos.succ (_fresh m) <= a)%positive -> _mem m a = fail.
  Proof.
    intros.
    apply _wf_fresh.
    lia.
  Qed.

  Definition alloc (m:mem) : mem * positive :=
    (mkmem (_mem m) (Pos.succ (_fresh m)) (alloc_lt m), _fresh m).

  Definition empty : mem :=
    mkmem (fun _ => fail) xH (fun _ _ => eq_refl).

  Definition empty_fr (fr:positive) : mem :=
    mkmem (fun _ => fail) fr (fun _ _ => eq_refl).


  Section CPYREC.
    Variable copy_ptr : forall  (ty:typ) (pty: ptr ty) (cmem:mem), option mem.

    Definition copy_val  {ty:typ} (v:val ty) (cmem:mem) : option mem :=
      match v in val ty' return ty' = ty -> option mem with
      | Vprim _ _ => fun _ => Some cmem (* nothing to copy *)
      | Vptr ty' p => fun EQ => copy_ptr ty (cast (f_equal ptr EQ) p) cmem
      end eq_refl.

    Fixpoint copy_array  {ty:typ} (a : array (val ty)) (cmem:mem) : option mem :=
      match a with
      | nil     => Some cmem
      | v1::vls => let* cmem := copy_val v1 cmem in
                   copy_array vls cmem
      end.

    Fixpoint copy_record (lty:smaplist typ) : grecord val lty -> mem -> option mem :=
      match lty as l return (grecord val l -> mem -> option mem) with
      | nil => fun _  cmem => Some cmem
      | p :: lty =>
          fun gr cmem =>
            let* cmem := copy_val (proj_field (fst gr)) cmem
            in copy_record lty (snd gr) cmem
      end.
  End CPYREC.

  Fixpoint xcopy (m:mem) {ty:typ} (p : ptr ty) (cmem:mem) {struct ty}: option mem.
  Proof.
    destruct ty.
    (* Pointer to primitive is not possible *)
    - exfalso. apply (decomp_ptr _ p).
    - exfalso. apply (decomp_ptr _ p).
    - exfalso. apply (decomp_ptr _ p).
    - (* pointer to an array *)
      eapply bind.
      apply (get p m).
      intro mvA.
      eapply bind.
      apply (copy_array (xcopy m) (decomp_mval _ mvA) cmem).
      apply (fun cmem => set p mvA cmem).
    - exfalso. apply (decomp_ptr _ p).
    - (* pointer to a record *)
      eapply bind.
      apply (get p m).
      intro mvA.
      eapply bind.
      apply (copy_record (xcopy m) _ (decomp_mval _ mvA) cmem).
      apply (fun cmem => set p mvA cmem).
    - apply (Some cmem).
    - (* pointer to a abstract object *)
      eapply bind.
      apply (get p m).
      intro mvA.
      apply (set p mvA cmem).
  Defined.

  Definition copy  (m:mem) {ty:typ} (pty : ptr ty)   : option mem :=
    xcopy m pty (empty_fr (_fresh m)).

  Fixpoint copy_list (m:mem) (l : list {ty:typ & val ty}) : option mem :=
    match l with
    | nil =>  Some (empty_fr (_fresh m))
    | v ::l => let* cpm := copy_list m l in
               copy_val (@xcopy m) (projT2 v) cpm
    end.

  Fixpoint copy_args (m:mem) {tparams:list typ} (args : DList.dlist (DList.resFtyp val) tparams)  : option mem :=
    match args with
    | DList.DNIL _ => Some (empty_fr (_fresh m))
    | @DList.DCONS _ _ ty v l dl =>
        let* cpm := copy_args m dl in
        let* v := v in
        copy_val (@xcopy m) v cpm
    end.
  (** preservation of well-formedness *)
  Lemma wf_empty : forall ge, wf ge empty.
  Proof.
    unfold empty,wf.
    simpl. discriminate.
  Qed.


  (*        Lemma wf_set : forall (ge:genv) ty (p:ptr ty) (mv:mval ty) (m m':t),
            wf ge m -> wf_mval ge m _ mv ->
            set p mv m = Some m' ->
            wf ge m'.
        Proof.
          intros. unfold wf in *.
          intros.
          destruct (addr_of_ptr p)eqn:A ; try discriminate.
          (* We have an addoption *)
          destruct (Pos.eq_dec a a0).
          + subst.





          simpl in H1.
          destruct (Coqlib.plt a (_fresh m)); try discriminate.
          inv H1. simpl. unfold _set.
          intros.

          - inv H1.
            apply Eqdep_dec.inj_pair2_eq_dec in H4;[|apply typ_eq_dec].
            subst.
            destruct mv0; simpl in *.
            unfold wf_mval.


            + discriminate.
            + unfold wf_mval in H0.
              eapply H0; eauto.
          - destruct (Pos.eq_dec a a').
            discriminate.
            eapply H; eauto.
        Qed.

        Definition pred (F1 F2: typ -> Type) (P : forall  (ty:typ) (v1: F1 ty) (v2 : F2 ty),Prop)
          (v1: {ty:typ & F1 ty}) (v2: {ty:typ & F2 ty}) : Prop :=
          match v1 , v2 with
          | existT _ t1 v1' , existT _ t2 v2' =>
              match typ_eq_dec t1 t2 with
              | left EQ => P t2 (cast (f_equal F1 EQ) v1') v2'
              | _       => False
              end
          end.
   *)

  Definition cast_pval {ty}  (pv : pval ty) (ty':typ): option (pval ty') :=
    match typ_eq_dec ty ty' with
    | left EQ => Some (cast (f_equal pval EQ) pv)
    | _ => fail
    end.

  Definition cast_mval {ty}  (pv : mval ty) (ty':typ): option (mval ty') :=
    match typ_eq_dec ty ty' with
    | left EQ => Some (cast (f_equal mval EQ) pv)
    | _ => fail
    end.

  Definition cast_val {ty:typ} (v: val ty) (ty':typ) : option (val ty') :=
    match typ_eq_dec ty ty' with
    | left EQ => Some (cast (f_equal val EQ) v)
    | right _ => fail
    end.

  Definition env := ident -> option {ty & val ty}.

  Definition get_signed (is32:bool) (b:btyp) :=
    if is32 then
      match b with
      | BInt32 s => Some s
      |  _       => None
      end
    else
      match b with
      | BInt64 s => Some s
      | _        => None
      end.

  Definition get_enum (ty:typ) :=
    match ty with
    | TEnum i l => Some (i,l)
    | _         => None
    end.


  Definition pval_of_typ (ty:typ) : eval_typ abs ty -> option (pval ty) :=
    match ty with
    | TBool => fun b => Some (PBool b)
    | TInt32 s => fun i => Some (PInt32 s i)
    | TInt64 s => fun i => Some (PInt64 s i)
    | TEnum i l => fun e => Some (PEnum i l e)
    |  _        => (fun _ => fail)
    end.

  Definition val_of_pval {ty:typ} (pv: option (pval ty)) : option (val ty) :=
    let* v := pv in
    Some (Vprim _ v).


  Definition typof_atom (te:tenv) (a: atom) : option typ :=
    btyp_to_typ te (typof_atom a).

  Definition eval_val {ty:typ} (v : val ty) : option (eval_typ abs ty) :=
    match v with
    | Vprim _ v => Some (eval_pval v)
    | _  => fail
    end.

  Definition val_of_eval_typ {ty:typ} (v : eval_typ abs ty) : option (val ty) :=
    match pval_of_typ ty v with
    | Some v => Some (Vprim _ v)
    | _    => fail
    end.

  Definition index_of_pval {ty:typ} (v:pval ty) : option int64 :=
    if arch
    then
      match v with
      | PInt32 Unsigned i =>  Some (Intop.U64.of_u32 i)
      | _          => fail
      end
    else
      match v with
      | PInt64 Unsigned i =>  Some i
      | _          => fail
      end.

  Definition index_of_val {ty :typ} (v:val ty) : option int64 :=
    match v with
    | Vprim _ pv => index_of_pval pv
    | _       => fail
    end.

  Definition isptr {ty:typ} (v:val ty) : option (ptr ty) :=
    match v with
    | Vptr _ p => Some p
    | _        => fail
    end.

  Definition eval_array_get {ty: typ} (m:mval ty) (i:Integers.Int64.int) (tr:typ) : option (val tr) :=
    match m with
    | MArray _ l =>  let* v := Barray.get l i in cast_val v tr
    | _ => fail
    end.

  Definition ecast_val  (v:option {ty:typ & val ty}) (tyr:typ) : option (val tyr) :=
    match v with
    | Some (existT _ ty v) =>  cast_val v tyr
    | _ => fail
    end.

  Definition eval_record_proj {ty: typ} (m:mval ty) (k:ident) (tr:typ) : option (val tr) :=
    match m with
    | MRecord id fields r =>
        ecast_val (gprojT r k) tr
    | _ => fail
    end.

  Definition eval_mem_access (m:mem) {ta:typ} (v1:val ta) (ce:cedge) (tr:typ) : option (val tr) :=
    let* p := isptr v1 in
    let* mv := get p m in
    match ce with
    | CIndex i => eval_array_get mv  i tr
    | CField fd => eval_record_proj mv fd tr
    end.

  Definition cast_function {a1 a2:list typ} {r1 r2:typ} (Eq : TFun a1 r1 = TFun a2 r2) (f : mem -> typ_of_fun a1 r1) :
    mem -> typ_of_fun a2 r2.
  Proof.
    injection Eq.
    intros E1 E2.
    rewrite E2 in f.
    rewrite E1 in f.
    apply f.
  Defined.

  Definition load_fun (ge:genv) {args:list typ} {ret:typ} (v :val (TFun args ret)) : option (mem -> typ_of_fun args ret) :=
    let fid := decomp_ptr _ (decomp_val _ v) in
    let* f := ge fid in
    match f with
    | GConst _ _ => fail
    | GFun args' ret' fc =>
        match typ_eq_dec (TFun args' ret') (TFun args ret)  with
        | left EQ => Some (cast_function EQ fc)
        | _  => fail
        end
    end.

  Fixpoint eval_rapp (tparams : list typ) (tret : typ)
    (args : DList.dlist (DList.resFtyp val) tparams) : forall (f: typ_of_fun tparams tret), option (val tret * mem).
  Proof.
    destruct args.
    - simpl. apply (fun f => f tt).
    - simpl.
      intro f.
      eapply bind.
      apply e.
      intro e1.
      specialize (f e1).
      destruct l. apply f.
      apply (eval_rapp _ _ args f).
  Defined.

  Definition mk_fptr (id:ident) (args: list typ) (r:typ) : val (TFun args r) :=
    Vptr (TFun args r) (PtrF id args r).

  Definition ecast {ty:typ} (v: val ty) (tyr: typ): option (val tyr) :=
    match typ_eq_dec ty tyr with
    | left EQ => Some (cast (f_equal val EQ) v)
    | right _ => fail
    end.

  Definition get_lvar  (e:env) (id:ident) (tyr:typ) : option (val tyr) :=
    match e id with
    | Some (existT _ ty' v') => ecast v' tyr
    | None => None
    end.

  Definition get_gvar (ge:genv) (id:ident) (tyr: typ) : option (val tyr) :=
    let* d := ge id in
    match d with
    | GFun args tret _ => match typ_eq_dec (TFun args tret) tyr with
                             | left EQ => Some (cast (f_equal val EQ) (mk_fptr id args tret))
                             | _  => None
                             end
    | GConst ty v => match typ_eq_dec ty tyr with
                      | left EQ => Some (cast (f_equal val EQ) v)
                      | right _ => None
                     end
    end.

  Definition get_var (te:tenv) (ge:genv) (e:env) (id:ident) (bt:btyp) (tyr:typ) : option (val tyr) :=
    let* ty := btyp_to_typ te bt in
    if typ_eq_dec ty tyr
    then
      match e id with
      | Some (existT _ ty' v') => ecast v' tyr
      | None => get_gvar ge id tyr
      end
    else fail.

  Definition get_function (ge:genv) (e:env) (id:ident) (tyr: typ) : option (val tyr) :=
    match e id with
    | Some _ => fail (* shadowing, we do not do that *)
    |  _    =>
         let* d := ge id in
         match d with
         | GFun args tret _ =>
             match typ_eq_dec (TFun args tret) tyr with
             | left EQ => Some (cast (f_equal val EQ) (mk_fptr id args tret))
             | _  => fail
             end
         | _ => fail
         end
    end
  .

  Section S.
    Variable eval_atom :  tenv -> genv -> env -> mem -> forall (tyr: typ), atom -> option (val tyr).

    Definition eval_call (te:tenv) (ge:genv) (e:env) (m:mem) (f:ident)
      (btf:btyp) (args: list atom) (tyr:typ) : option (val tyr * mem) :=
        let* tyf := btyp_to_typ te btf in
        match tyf with
        | TFun tparams tret =>
            (* A bit weird to bypass the local environment *)
            let* f := get_function ge e f (TFun tparams tyr) in
            let* f := load_fun ge f in
            let* vargs := DList.map2 _ (eval_atom te ge e m) args tparams in
            eval_rapp tparams tyr vargs (f m)
        | _  => fail
        end.

  End S.

  Fixpoint eval_atom (te: tenv) (ge: genv) (e:env) (m: mem) (tyr:typ) (a:atom) {struct a} : option (val tyr) :=
    match a with
    | ATrue => val_of_pval (cast_pval (PBool true) tyr)
    | AFalse => val_of_pval (cast_pval (PBool false) tyr)
    | AInt32 i s => val_of_pval (cast_pval (PInt32 s i) tyr)
    | AInt64 i s  => val_of_pval (cast_pval (PInt64 s i) tyr)
    | AConstr s _ bt =>
        let* td := btyp_to_typ te bt  in
        match get_enum td with
        | None => fail
        | Some (i,l) => let* e :=  make_enum l s in
                        val_of_pval (cast_pval (PEnum i l e) tyr)
        end
    | AVar id bt => get_var te ge e id bt tyr
    | ACast a1 tr =>
        let* tr := btyp_to_typ te tr in
        let* te1 := typof_atom te a1 in
        let* v1  := eval_atom te ge e m te1 a1   in
        match v1 with
        | Vprim ty' pv =>
            let* f := get_cast abs ty' tr in
            let* v' := f (eval_pval pv)  in
            let* pv := pval_of_typ _ v' in val_of_pval (cast_pval pv tyr)
        | _ => fail
        end
    | AUnaryOp op a1 bt =>
        let* tye := btyp_to_typ te bt in
        let* v := eval_atom te ge e m tye a1  in
        let* v := eval_val v in
        let* r := eval_unary_op abs op tye v tyr in
        val_of_eval_typ r
    | ABinaryOp op a1 a2 bt =>
        let* tye1 := typof_atom te a1 in
        let* tye2  := typof_atom te a2 in
        let* v1 := eval_atom te ge e m tye1 a1 in
        let* v2 := eval_atom te ge e m tye2 a2 in
        let* v1 := eval_val v1 in
        let* v2 := eval_val v2 in
        let* option := eval_binary_op abs op tye1 tye2 v1 v2 tyr in
        let* pv := pval_of_typ _ option in val_of_pval (cast_pval pv tyr)
    | AArrayGet a1 i _ bt =>
        let* tya1 := typof_atom te a1 in
        let* v1 := eval_atom te ge e m tya1 a1 in
        let* v2 := eval_atom te ge e m (typof_index arch) i  in
        let* i  := index_of_val v2 in
        eval_mem_access m v1 (CIndex i) tyr
    | ARecordProj r id _ bt =>
        let* t := typof_atom te r in
        let* r := eval_atom te ge e m t r in
        eval_mem_access m r (CField id) tyr
    | APureCall f btf args bt =>
        let*(vret,m') := eval_call eval_atom te ge e m f btf args tyr in
        if eq_mem m m'
        then ret vret else fail
    end.

  Definition eval_array_set (m:mem) {ta:typ} (a:val ta) {ti:typ} (i:val ti) {te:typ} (v:val te): option mem :=
    let*  i := index_of_val i in
    let*  p := isptr a in
    let* arr := get p m in
    match arr in mval t return  t = ta -> option mem with
    | MArray te' l => fun EQ =>
                        let* v := cast_val v te' in
                        let* l' := Barray.set l i v in
                        set p (cast (f_equal mval EQ) (MArray _ l'))  m
    | _ => fun _ => fail
    end eq_refl.

  Definition eval_record_update (m:mem) {tr:typ} (r:val tr) (k:ident) {te:typ} (v:val te): option mem :=
    let* p := isptr r in
    let* rc := get p m in
    match rc in mval t return  t = tr -> option mem with
    | MRecord id fields r => fun EQ =>
                               let* r1 := dyn_upd val typ_eq_dec r k  _ v in
                               set p (cast (f_equal mval EQ) (MRecord _ _ r1))  m
    | _ => fun _ => fail
    end eq_refl.

  Definition eval_comp (te:tenv) (ge:genv) (e:env) (m:mem) (c:comp) (tr:typ) : option (val tr  * mem) :=
    match c with
    | CpAtom a => let* va := eval_atom te ge e m tr a in
                     Some (va,m)
    | CpArraySet a i v bt =>
        let* tv := typof_atom te v in
        let* a := eval_atom te ge e m tr a in
        let* i := eval_atom te ge e m (typof_index arch) i in
        let* v := eval_atom te ge e m tv v in
        let* m := eval_array_set m a i v  in
        Some (a,m)
    | CpRecordUpdate r id v bt =>
        let* trec := typof_atom te r in
        let* tv   := typof_atom te v in
        let* r := eval_atom te ge e m tr r in
        let* v := eval_atom te ge e m tv v in
        let* m := eval_record_update m r id v in
        Some(r,m)
    | CpCall f btf args _ =>
        eval_call eval_atom te ge e m f btf args tr
    end.

  Definition typof_comp (te:tenv) (c: comp) : option typ :=
    btyp_to_typ te (typof_comp c).

  Definition env_set (id:ident) {ty:typ} (v:val ty) (e:env) : env :=
    fun x => if Ident.eq_dec x id then Some (existT _ ty v) else e x.


  Definition typ_of_statement (ty:option typ) :=
    match ty with
    | None => env
    | Some ty => val ty
    end.

  Definition eval_match (tv:typ) (v: val tv) (ty: option typ) (cases: list (pattern * (option (typ_of_statement ty * mem)))) :
    option (typ_of_statement ty * mem) :=
    match v with
    | Vptr _ _ => fail
    | Vprim _ e => match e with
                   | PEnum id l en => match_with_err en cases
                   |  _  => fail
                   end
    end.

  Definition bool_of_valbool (v: val TBool) : bool:=
    match v with
    | Vprim _ (PBool b) => b
    | _               => false (* cannot happen *)
    end.

  Fixpoint eval_statement (te:tenv) (ge:genv) (e:env) (m:mem) (ty:option typ) (s:statement)  : option (typ_of_statement ty * mem) :=
    match s with
    | StSkip   => match ty with
                  | None => Some (e,m)
                  | Some _ => fail
                  end
    | StSet id c =>
        match ty with
        | None =>
            let* tyid := typof_comp te c in
            let*(r,m') := eval_comp te ge e m c tyid in
            Some (env_set id r e,m')
        | _ => fail
        end
    | StIfThenElse a s1 s2 =>
        let* v := eval_atom te ge e m TBool a in
        eval_statement te ge e m ty (if bool_of_valbool v then s1 else s2)
    | StSwitch a l =>
        let* ta := typof_atom te a in
        let* va  := eval_atom te ge e m ta a  in
        let vcases :=  MapList.map (eval_statement te ge e m ty) l in
        eval_match ta va ty vcases
    | StSequence s1 s2 =>
        let* (e1,m1) := eval_statement te ge e m None s1 in
        eval_statement te ge e1 m1 ty s2
    | StReturn a =>
        match ty with
        | None => fail
        | Some ty =>
            let* va := eval_atom te ge e m ty a in
            Some (va,m)
        end
    | StAttr a s => eval_statement te ge e m ty s
    end.



  Fixpoint eval_fun_rec (te: tenv) (ge: genv)  (e: env) (params: smaplist typ) (tret: typ)  (s: statement) :
    mem -> typ_of_fun (List.map snd params) tret.
  Proof.
    destruct params.
    - simpl.
      apply (fun m _ => eval_statement te ge e m (Some tret) s).
    - simpl.
      intros m v.
      specialize (eval_fun_rec te ge (env_set (fst p) v e) params tret s m).
      destruct (List.map snd params).
      + simpl in *. apply (eval_fun_rec tt).
      + simpl in *. apply eval_fun_rec.
  Defined.

  Definition env_empty : env := fun _ => fail.




  Definition build_Fun (te:tenv) (ge:genv) (params:smaplist btyp) (tret:btyp) (s:statement) : option gval  :=
    if MapList.nodup Ident.eq_dec params
    then
      let* tret' := btyp_to_typ te tret in
      let* params' := Denot.map_err (btyp_to_typ te) params in
      Some (GFun (List.map snd params') tret' (eval_fun_rec te ge  env_empty params' tret' s))
    else fail.

  Fixpoint array_of_values (l :list {ty:typ & val ty}) (ty:typ) : option (array (val ty)) :=
    match l with
    | nil => Some nil
    | e::l => let* a := array_of_values l ty in
              let (te,ve) := e in
              let* ve' := cast_val ve ty in
              Some (ve' :: a)
    end.


  Fixpoint eval_record_lit (lv: smaplist {ty:typ & val ty}) (fields: smaplist typ) : option (eval_recordtyp val fields).
    destruct lv as [|[x [tv v]] lv']; destruct fields as [| [y t] fields'].
    - apply (Some tt).
    - apply fail.
    - apply fail.
    - destruct (Ident.eq_dec x y).
      + eapply bind.
        apply (cast_val v t).
        intro cv.
        eapply bind.
        apply (eval_record_lit lv' fields').
        intro rc.
        unfold eval_recordtyp in *. simpl in *.
        apply (Some (Field y cv, rc)).
      + apply fail.
  Defined.


  (* Like Barocq, the semantics is not typed *)

  Fixpoint eval_literal (te: tenv)  (l: literal)  (m:mem): option ({ty:typ & val ty} * mem) :=
    match l with
    | LTrue => Some  (existT _ _ (Vprim _ (PBool true)),m)
    | LFalse => Some (existT _ _ (Vprim _ (PBool false)), m)
    | LInt32 i s => Some (existT _ _  (Vprim _ (PInt32 s i)),m)
    | LInt64 i s => Some (existT _ _ (Vprim _ (PInt64 s i)),m)
    | LArray a bt _ =>
        let* ta := btyp_to_typ te bt in
        match ta with
        | TArray elt =>
            let* (av,m) := mmap_fold (eval_literal te) a m in
            let* av := array_of_values av elt in
            let (m2,fa) := alloc m in
            let ptr     := PtrA fa elt in
            let* m := set ptr (MArray _ av) m2 in
            Some(existT _ _ (Vptr _ ptr),m)
        |  _         => fail
        end
    | LRecord rc ub rid =>
        let* tr := btyp_to_typ te (BRecord rid ub) in
        match tr with
        | TRecord id l =>
            let* (r,m) := mmap_fold (fun x m => let* (v,m) := eval_literal te (snd x) m in
                                                Some ((fst x,v),m)) rc m in
            let* r := eval_record_lit r l in
            let (m1,fa) := alloc m in
            let ptr     := PtrR fa id l in
            let* m2 := set ptr (MRecord id l r) m1 in
            Some(existT _ _ (Vptr _ ptr),m2)
        |  _         => fail
        end
    end.

End S.

