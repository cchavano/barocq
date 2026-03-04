(** Must alias for imp1 *)
From compcert Require Import Maps.
Require Import Uint63.
Require Import String FMapInterface FMapList ZArith Int ListSet.
From BarocqComp Require Import OptionMonad Error Maps2 Types Syntax Imp1 Graph Typing Utils Pp.
From Coq Require Import FMapPositive.
Open Scope error_monad_scope.


(** WARNING: Known limitations.
    - The use of global variables is limited to primitive types.
    For instance, there is no support for reading a global array.
    This would be doable but would require consider all the global variables as (implicit) arguments of the function.
    - Function pointers cannot be stored in memory (arrays or records).
    This would be doable but require either more precise typing of function arguments
    or put a default contract on function pointers.
 *)

Module EdgeLabel <: OrderedType.

Inductive edge :=
| Field (id:Syntax.ident)
| Index (a:atom)
| Top.

Definition pp (e:edge) :=
  match e with
  | Field id => Bcat (Bstr ".") (Bstr id)
  | Index a  => Bcat (Bstr "[") (Bcat (Printer.pp_atom a)
                                   (Bstr "]"))
  | Top      => Bstr "T"
  end.


Definition next_label (t:typ) (e:edge) :=
  match t, e with
  | TArray ty , (Index _ | Top) => OK ty
  | TRecord _ l  , Field fd => err_of_opt (Brecord.find_type_of_field fd l)
  | _  , _ => fail
  end.




Definition edge_compare (e1 e2:edge) : comparison :=
  match e1, e2 with
  | Field i1 , Field i2 => Ident.compare i1 i2
  | Field _  , _        => Lt
  | _        , Field _  => Gt
  | Index a1 , Index a2 => Syntax.AtomOrdered.atom_compare a1 a2
  | Index _  , _        => Lt
  | _        , Index _  => Gt
  |  Top     , Top      => Eq
  end.

Definition t := edge.
Definition eq : t -> t -> Prop := @eq t.

Definition lt : t -> t -> Prop := fun x y => edge_compare x y = Lt.

Lemma eq_refl : forall (x:t), x = x.
Proof. reflexivity. Qed.

Lemma eq_sym : forall (x y:t), x = y -> y = x.
Proof. congruence. Qed.

Lemma eq_trans : forall (x y z:t), x = y -> y = z -> x = z.
Proof. congruence. Qed.

Lemma edge_compare_eq : forall x y,
    edge_compare x y = Eq <-> x = y.
Proof.
  destruct x, y; simpl; try intuition congruence.
  - rewrite ExtOrdered.string_compare_eq_iff. intuition congruence.
  - rewrite AtomOrdered.atom_compare_eq. intuition congruence.
Qed.
  Lemma edge_compare_refl : forall x,
      edge_compare x x = Eq.
  Proof.
    intros.
    rewrite edge_compare_eq.
    reflexivity.
  Qed.

  Lemma edge_compare_trans : forall x y z c,
      edge_compare x y = c -> edge_compare y z = c -> edge_compare x z = c.
  Proof.
    destruct x,y,z; simpl ; try intuition congruence.
    apply ExtOrdered.string_compare_trans.
    apply AtomOrdered.atom_compare_trans.
  Qed.

  Lemma edge_compare_antisym  : forall (x y:t), edge_compare x y = CompOpp (edge_compare y x).
  Proof.
    destruct x,y; simpl; try intuition congruence.
    - apply String.compare_antisym.
    - apply AtomOrdered.atom_antisym.
  Qed.


  Definition lt_trans  (x y z:t): lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    apply edge_compare_trans.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> eq x y -> False.
  Proof.
    unfold lt. intros.
    unfold eq in H0. subst.
    rewrite edge_compare_refl in H. discriminate.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    destruct (edge_compare x y) eqn:TC.
    - apply EQ. rewrite edge_compare_eq in TC. apply TC.
    - apply LT;auto.
    - apply GT.
      rewrite edge_compare_antisym in TC.
      unfold lt.
      destruct (edge_compare y x); try discriminate.
      reflexivity.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {x <> y}.
  Proof.
    destruct (edge_compare x y) eqn:EQB.
    - left. apply edge_compare_eq in EQB. auto.
    - right. intro.
      subst. rewrite edge_compare_refl in EQB. discriminate.
    - right. intro.
      subst. rewrite edge_compare_refl in EQB. discriminate.
  Qed.

  (** Consider edge as a (flat lattice) lattice. *)
  Definition join (e1 e2: t) : t :=
    match edge_compare e1 e2 with
    | Eq => e1
    |  _ => Top
    end.

  Definition classify_edge (e1 e2:EdgeLabel.t) :=
    match e1 , e2 with
    | EdgeLabel.Field x , EdgeLabel.Field y => if Ident.eq_dec x y then MUST else NOTMAY
    | _ , EdgeLabel.Field _ | EdgeLabel.Field _ , _ => NOTMAY
    | EdgeLabel.Index a1 , EdgeLabel.Index a2 => if AtomOrdered.eq_dec a1 a2 then MUST else MAY
    |  _ , _ => MAY
    end.

  Definition le_edge (e1 e2: EdgeLabel.t) :=
    match e1, e2 with
    | EdgeLabel.Field x, EdgeLabel.Field y => x = y
    | EdgeLabel.Index _ , EdgeLabel.Top    => True
    | EdgeLabel.Index i , EdgeLabel.Index  j      => i = j (* Could try to do better *)
    | _ , _ => False
    end.




End EdgeLabel.

Module G := Make(TypOrdered)(EdgeLabel).

Fixpoint subst_atom (env : smaplist atom) (a:atom): res atom :=
  match a with
  | AVar id bt =>
      match MapList.find_err string_dec id env with
      | OK a => OK a
      | Error _ => Error (MSG id :: nil)
      end
  | ACast a bt => let* a := subst_atom env a in
                  OK (ACast a bt)
  | AUnaryOp o a bt => let* a := subst_atom env a in
                       OK (AUnaryOp o a bt)
  | ABinaryOp o a1 a2 bt =>
      let* a1 := subst_atom env a1 in
      let* a2 := subst_atom env a2 in
      OK (ABinaryOp o a1 a2 bt)
  | AArrayGet a i ly bt =>
      let* a := subst_atom env a in
      let* i := subst_atom env i in
      OK (AArrayGet a i ly bt)
  | ARecordProj a fd ly bt =>
      let* a := subst_atom env a in
      OK (ARecordProj a fd ly bt)
  | APureCall id bt1 la bt2 =>
      let* l := mmap (subst_atom env) la in
      OK (APureCall id bt1 l bt2)
  | ATrue | AFalse | AInt32 _ _ | AInt64 _ _ | AConstr _ _ _  => OK a
  end.

Definition subst_edge (env : smaplist atom) (e: EdgeLabel.t) :=
  match e with
  | EdgeLabel.Top => Error (MSG "index is unknown" :: nil)
  | EdgeLabel.Field fd => OK (EdgeLabel.Field fd)
  | EdgeLabel.Index i  => let* a := subst_atom env i in
                          OK (EdgeLabel.Index a)
  end.

Module GEXPR.
  (* Restricted form of expressions.
     Due to typing issues, it is not straightforward to reconstruct an atom... *)

  Inductive t :=
  (*| Atm (a:atom) *)
  | Var (id:ident)
  | Get (e:t) (field : EdgeLabel.t).


  Fixpoint incl_idents (l1 l2 :list ident) : res (unit:Type) :=
    match l1 with
    | nil => OK tt
    | e::l1' => if List.existsb (String.eqb e) l2
                then incl_idents l1' l2
                else Error (MSG "Variable " :: MSG e :: MSG " would escape its scope." :: nil)
    end.

  Definition check_edge (args:list ident) (e:EdgeLabel.t) : res unit :=
    match e with
    | EdgeLabel.Top => Error (MSG "Expression cannot contain an unknown indexe." :: nil)
    | EdgeLabel.Field fd => OK tt
    | EdgeLabel.Index e  => let v := AtomOrdered.vars_of_atom e in
                            incl_idents v args
    end.

  Fixpoint check_expr (args:list ident) (e:t) : res unit :=
    match e with
    (*| Atm a => let v := AtomOrdered.vars_of_atom a in
               incl_idents v args *)
    | Var i => incl_idents (i::nil) args
    | Get e fd => let* _ := check_expr args e in
                  check_edge args fd
    end.


  Definition eq_dec (e1 e2:t) : {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality.
    (*apply AtomOrdered.eq_dec.*)
    apply string_dec.
    apply EdgeLabel.eq_dec.
  Qed.

(*  Fixpoint subst_expr (env : smaplist atom) (e:t) : res t :=
    match e with
    (*| Atm a => let* a := subst_atom env a in
               OK (Atm a) *)
    | Var  id  =>  match MapList.find_err string_dec id env with
                   | OK a => OK (Atm a)
                   | Error _ => Error (MSG id :: nil)
                  end
    | Get e fd => let* e := subst_expr env e in
                  let* fd := subst_edge env fd in
                  OK (Get e fd)
    end.
*)

  Fixpoint pp (e:t) :=
    match e with
    (*| Atm a => Printer.pp_atom a*)
    | Var id => Bstr id
    | Get e fd => Bcat (pp e) (EdgeLabel.pp fd)
    end.

(*  Definition typof (te:tenv) (e:t) : res typ :=
    match e with
    | Atm a => btyp_to_typ te a
    | Get e fd =>
        let* bt := typof te e in
        match fd with
        | EdgeLabel.Field fd =>
*)
End GEXPR.

Inductive sfunction  :=
| RPrim  (* return a primitive value *)
| RDeep (e:GEXPR.t).

Definition sfunction_eq_dec  (s1 s2:sfunction) : {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
  apply GEXPR.eq_dec.
Defined.

Definition afunction := Syntax.function (sfunction*bool) typ.

Definition afunction_eq_dec (f1 f2:afunction) : {f1 = f2} + {f1 <> f2}.
apply function_dec.
decide equality.
apply bool_dec.
apply sfunction_eq_dec.
apply typ_eq_dec.
Defined.

Inductive alit := | IsPrim (b:bool).

Inductive aglobdef :=
| ALit (b:bool) (* Is-it primitive ? *)
| AFun (f:afunction).

Inductive KVar :=
| KDead (* Dead variable - may point anywhere *)
| KPrim (* Primitive type - no alias *)
| KNode (n:int) (* Reference in the alias graph *)
| KFun  (f:afunction) (* a function pointer *).

Definition get_node (k:KVar) : option int :=
  match k with
  | KNode n => Some n
  | _       => None
  end.

Definition is_dead (k:KVar) : bool :=
  match k with
  | KDead => true
  | _ => false
  end.

Definition is_primitive (k:KVar) : bool :=
  match k with
  | KPrim => true
  | _ => false
  end.





Module Vars.
  (* Mapping and reverse mapping *)

  Record t := mk
    {
      Vars : STree.t KVar;
      RVar : IntMap.t (list ident);
    }.

  Definition fold_dead {A: Type} (F : string -> A -> A) (acc:A) (vrs:t) :=
    STree.fold (fun acc x k => if is_dead k then F x acc else acc) (Vars vrs) acc.

  Definition empty := mk STree.empty (IntMap.empty _).

  Definition get (x:ident) (m:t) := STree.get x (Vars m).

  Definition of_vars (vrs: STree.t KVar) : t :=
    let rvar :=
      STree.fold (fun 'acc k v => match get_node v with
                                  | None => acc
                                  | Some n => IntMap.addl n k acc
                                  end) vrs (IntMap.empty _) in
    mk vrs rvar.

  Definition rev_add (x:ident) (v:KVar) (rm : IntMap.t (list ident)) :=
    match v with
    | KNode n => IntMap.addl n x rm
    | _       => rm
    end.

  Definition set (x:ident) (v:KVar) (m:t) :=
    mk (STree.set x v (Vars m))
       (rev_add x v
          match STree.get x (Vars m) with
          | None =>   (RVar m)
          | Some v =>
              match v with
              | KNode n =>  (IntMap.remove_from_list String.eqb n x (RVar m))
              |  _      =>  (RVar m)
              end
          end).

  Record wf (m:t) :=
    {
      Vars_RVar : forall x n, STree.get x (Vars m) = Some (KNode n) <->
                              In x (IntMap.findl n (RVar m));
    }.

  Lemma wf_empty : wf empty.
  Proof.
    constructor.
    unfold empty.
    simpl.
    intros.
    rewrite STree.gempty. intuition congruence.
  Qed.

  Lemma kvar_case : forall k, (exists n, k = KNode n) \/
                               (forall n, k <> KNode n).
  Proof.
    destruct k.
    - right;intros.
      congruence.
    - right;intros.
      congruence.
    - left. exists n; reflexivity.
    - right;intros.
      congruence.
  Qed.

  Lemma List_remove_eq : forall k l,
      In k (List_remove String.eqb k l) <-> False.
  Proof.
    intros.
    rewrite List_remove_not_In; try tauto.
    repeat intro. subst.
    rewrite String.eqb_refl in H.
    discriminate.
  Qed.

  Lemma List_remove_neq : forall k k' l,
      k <> k' ->
      In k (List_remove String.eqb k' l) <-> In k l.
  Proof.
    intros.
    rewrite List_remove_neq; try tauto.
    repeat intro.
    apply String.eqb_eq in H0.
    auto.
  Qed.

  Lemma okvar_case : forall k, (exists n, k = Some (KNode n)) \/
                               (forall n, k <> Some (KNode n)).
  Proof.
    destruct k.
    - destruct (kvar_case k).
      destruct H. left. exists x. congruence.
      right. intros. specialize (H n). congruence.
    - right.
      congruence.
  Qed.



  Lemma wf_set : forall m v k, wf m -> wf (set k v m).
  Proof.
    intros.
    destruct H.
    constructor.
    unfold set; simpl.
    intros.
    rewrite STree.gsspec.
    unfold rev_add.
    destruct (okvar_case (STree.get k (Vars m))).
    - destruct H as (n1 & H).
      rewrite H.
      destruct (kvar_case v).
      + destruct H0 as (n2 & H0).
         subst.
         destruct (Int.eq_dec n n2).
         rewrite IntMap.findl_eq by auto.
         rewrite IntMap.findl_remove.
         destruct (IntMap.Facts.eq_dec n n1).
         destruct (STree.elt_eq x k); subst.
         simpl. intuition congruence.
         simpl.
         rewrite List_remove_neq by auto.
         rewrite <- Vars_RVar0.
         intuition congruence.
         simpl.
         rewrite <- Vars_RVar0.
         destruct (STree.elt_eq x k); intuition congruence.
         rewrite IntMap.findl_neq by auto.
         rewrite IntMap.findl_remove.
         destruct (IntMap.Facts.eq_dec n n1);
           destruct (STree.elt_eq x k); subst.
         rewrite List_remove_eq by auto.
         intuition congruence.
         rewrite List_remove_neq by auto.
         rewrite <- Vars_RVar0.
         intuition congruence.
         rewrite <- Vars_RVar0.
         intuition congruence.
         rewrite <- Vars_RVar0.
         intuition congruence.
       +  assert (REW: match v with
                       | KNode n0 => IntMap.addl n0 k (IntMap.remove_from_list String.eqb n1 k (RVar m))
                       | _ => IntMap.remove_from_list String.eqb n1 k (RVar m)
                       end = IntMap.remove_from_list String.eqb n1 k (RVar m)).
          {
            destruct v;auto.  specialize (H0 n0). congruence.
          }
          change ident with string in *.
          rewrite REW. clear REW.
          rewrite IntMap.findl_remove.
         destruct (IntMap.Facts.eq_dec n n1);
           destruct (STree.elt_eq x k); subst.
         rewrite List_remove_eq by auto.
         intuition congruence.
         rewrite List_remove_neq by auto.
         rewrite <- Vars_RVar0.
         intuition congruence.
         rewrite <- Vars_RVar0.
         intuition congruence.
         rewrite <- Vars_RVar0.
         intuition congruence.
    -  assert (REW :  match STree.get k (Vars m) with
             | Some (KNode n1) => IntMap.remove_from_list String.eqb n1 k (RVar m)
             | _ => RVar m
             end = RVar m).
       { destruct (STree.get k (Vars m)); auto.
         destruct k0; auto.
         specialize (H n0) ; congruence.
       }
       rewrite REW ; clear REW.
       destruct (kvar_case v).
       + destruct H0 as (n2 & H0).
         subst.
         destruct (Int.eq_dec n n2).
         rewrite IntMap.findl_eq by auto.
         destruct (STree.elt_eq x k); subst.
         simpl. intuition congruence.
         simpl.
         rewrite <- Vars_RVar0.
         intuition congruence.
         rewrite IntMap.findl_neq by auto.
         rewrite <- Vars_RVar0.
         destruct (STree.elt_eq x k); intuition congruence.
       +  assert (REW: match v with
                       | KNode n0 => IntMap.addl n0 k (RVar m)
                       | _ => RVar m
                       end = RVar m ).
          {
            destruct v;auto.  specialize (H0 n0). congruence.
          }
          rewrite REW ; clear REW.
          rewrite <- Vars_RVar0.
          destruct (STree.elt_eq x k); intuition congruence.
  Qed.

  Definition vars_of_node (vrs:t) (n:int) := IntMap.findl n (RVar vrs).

(*Maps.PTree.elements_correct:
  forall [A : Type] (m : Maps.PTree.t A) (i : positive) [v : A], Maps.PTree.get i m = Some v -> In (i, v) (Maps.PTree.elements m)
Maps.PTree.elements_complete:
  forall [A : Type] (m : Maps.PTree.t A) (i : positive) (v : A), In (i, v) (Maps.PTree.elements m) -> Maps.PTree.get i m = Some v



  Lemma wf_of_vars : forall vrs, wf (of_vars vrs).
  Proof.
    constructor.
    unfold of_vars; simpl.
    unfold STree.fold.
    match goal with
    | |- context [Maps.PTree.fold ?G] => set (F:=G)
    end.
    rewrite Maps.PTree.fold_spec.

    Locate PTree.fold.
*)
  
Definition pp_kvar (k:KVar) : box :=
    match k with
    | KDead => Bstr "ko"
    | KPrim => Bstr "p"
    | KNode n => (Bstr (string_of_int n))
    | KFun f  => Bstr "fptr"
    end.

   Definition pp (s:t) : box := STree.pp (Bstr " -> ") pp_kvar (Vars s).





End Vars.





Record domain := mkdom
    {
      Vars : Vars.t;
      Pto  : G.t;
      Atoms: SMap.t (list atom); (* Atoms[x] = a1,...,an -> x is a variable of ai
                                      This is used to invalidate atoms in the graph
                                    *)
      IsPure: bool (* No side-effect *)
    }.





Definition pp_domain (d:domain) :=
  Bstack (Bstr "") (Bcat (Bframe "_" "|"  (Vars.pp (Vars d))) (G.pp (Pto d))) Middle.


Definition aenv := STree.t aglobdef.


Definition forget_var (x:ident)  (d:domain) :=
  mkdom (Vars.set x KDead (Vars d))
           (List.fold_right (fun a g => G.update_edgelabel (EdgeLabel.Index a) EdgeLabel.Top g) (Pto d) (SMap.get x (Atoms d)))
           (SMap.set x nil (Atoms d)) (IsPure d).

Definition is_prim_literal (env:aenv) (x:ident) :=
  match STree.get x env with
  | Some (ALit b) => b
  | _             => false
  end.

Definition eval_var (env:aenv) (vars:Vars.t) (id:ident) (*(bt:btyp)*) :=
  match Vars.get id vars with
  | Some v => OK v
  | None   => match STree.get id env with
              | Some v =>
                  match v with
                  ALit b =>
                    if b then OK KPrim
                    else
                      (* We could do better and return a node *)
                      fail
                  | AFun f => OK (KFun f)
                  end
              | None => Error (MSG "Unbound variable " :: MSG id :: nil)
              end
  end.

  Definition set_pto (g:G.t) (d:domain) :=
  mkdom (Vars d) g (Atoms d) (IsPure d).

  Definition set_pure (pure:bool) (d:domain) :=
    mkdom (Vars d) (Pto d) (Atoms d) pure.


  Definition set_atom (a:SMap.t (list atom)) (d:domain) :=
    mkdom (Vars d) (Pto d) a (IsPure d).

  Definition SMap_setl  (s:string) (e:atom) (m:SMap.t (list atom)) : SMap.t (list atom) :=
    SMap.set s (e::SMap.get s m) m.


  Definition register_vars_of_atom (a:atom) (m: SMap.t (list atom)) :=
    List.fold_right (fun id acc => SMap_setl id a acc) m (AtomOrdered.vars_of_atom a).

  Definition register_vars_of_edge (e:EdgeLabel.t) (m : SMap.t (list atom)) :=
    match e with
    | EdgeLabel.Field _ | EdgeLabel.Top => m
    | EdgeLabel.Index a => register_vars_of_atom a m
    end.

  Definition bind_path (d:domain) (o:int) (acc: EdgeLabel.t) : res (domain * KVar) :=
    if Int.eq_dec o (G.root (Pto d))
    then Error (MSG "(bug) trying to bind a path to the root node."::nil)
    else
    match G.create_edge EdgeLabel.next_label o acc (Pto d) with
    | Error m => Error (MSG "bind_path: errror" :: nil)
    | OK (g,n'_ty) =>
        if typ_is_prim (snd n'_ty)
        then OK (d,KPrim) (* Do not record primitive access *)
        else
          let atoms :=  register_vars_of_edge acc (Atoms d) in
          OK (set_pto g (set_atom atoms d),KNode (fst n'_ty))
    end.


Section EVALATOM.
  Variable aeval_atom : tenv -> aenv -> domain -> atom -> res (domain * KVar).

  Definition array_get (te:tenv) (env:aenv) (d:domain) (ar:atom) (id:atom) (*(bt:btyp)*)  :=
    match aeval_atom te env d ar  with
    | Error e  => Error (MSG "Wrong array :" :: MSG (Pp.pp (Printer.pp_atom ar)) :: MSG Pp.nl :: e)
    | OK (d,vr) =>
        match aeval_atom te env d id with
        | Error e => Error (MSG "Wrong array index:" :: MSG (Pp.pp (Printer.pp_atom id)) :: MSG Pp.nl :: e)
        | OK (d,idx) =>
            match vr with
            | KDead => Error (MSG "(dead) This should be a reference " :: nil)
            | KPrim => Error (MSG "(primitive) This should be a reference ":: nil)
            | KFun _ => Error (MSG "(function) This should be a reference ":: nil)
            | KNode n =>
                match idx with
                | KDead   => Error (MSG "(dead) This should be an array index " :: nil)
                | KNode n => Error (MSG "(reference) This should be an array index " :: nil)
                | KFun _ => Error (MSG "(function) This should be an array index " :: nil)
                | KPrim   => bind_path d n (EdgeLabel.Index id)
                end
            end
        end
    end.

  Definition record_proj_get (te:tenv) (env:aenv) (d:domain) (ar:atom) (fd:ident) (*(bt:btyp)*)  :=
    match aeval_atom te env d ar  with
    | Error e  => Error (MSG "Wrong record :" :: MSG (Pp.pp (Printer.pp_atom ar)) :: MSG Pp.nl :: e)
    | OK (d,vr) =>
            match vr with
            | KDead => Error (MSG "(dead) This should be a reference " :: nil)
            | KPrim => Error (MSG "(primitive) This should be a reference ":: nil)
            | KFun _ => Error (MSG "(function) This should be a reference ":: nil)
            | KNode n => bind_path d n (EdgeLabel.Field fd)
                end
    end.

  
End EVALATOM.



Definition aget_function (env:aenv) (vars: Vars.t) (id:ident) :=
  match Vars.get id vars with
  | Some _ => fail (* We have shadowing, that looks bad *)
  | None   =>
      match STree.get id env with
      | None => fail
      | Some ad => match ad with
                   | AFun af => OK af
                   |  _      => fail
                   end
      end
  end
  .

Definition typ_of_afunction (a:afunction) : typ :=
  TFun (List.map snd (fn_params a)) (fn_return a).

Definition compat_typ (d:domain) (k:KVar) (ty:typ) :=
  match k with
  | KDead   => OK false (* We have no idea of the type - we could keep it *)
  | KPrim   => OK (typ_is_prim ty)
  | KFun a  => OK (if typ_eq_dec ty (typ_of_afunction a) then true else false)
  | KNode n => let* ty' := G.get_node_label (Pto d) n in
               OK (if typ_eq_dec ty ty' then true else false)
  end.



Section CALL.
  Variable aeval_atom : tenv -> aenv -> domain -> atom -> res (domain * KVar).

  Fixpoint bind_args (te:tenv) (env:aenv) (d:domain) (args: list atom) (params : list (ident * typ)) {struct args} :=
  match args with
  | nil => match params with
           | nil => OK (d,nil,nil)
           |  _  => fail
           end
  | a1::args1 => match params with
                | nil => fail
                | (i1,ty)::params1 =>
                    match aeval_atom te env d a1 with
                    | Error _ =>
                        Error (MSG (Pp.pp (seq (Bstr "Expression ":: Printer.pp_atom a1:: Bstr " is invalid."::nil))) ::nil)
                    | OK (d,k) =>
                        let* b := compat_typ d k ty in
                        let* (d,bargs,bargs_a) := bind_args te env d args1 params1 in
                        if b
                        then OK (d, (i1,k)::bargs,(i1,a1)::bargs_a)
                        else
                          Error (MSG (Pp.pp (seq (Bstr "Expression " :: Printer.pp_atom a1 ::
                                                    Bstr " has incompatible types."::nil))) :: nil)
                    end
                 end
  end.

Definition no_alias_node (d:domain) (n:int) (arg:ident * KVar) : res unit :=
  match snd arg with
  | KDead => Error (MSG "Arguments ":: MSG (fst arg) :: MSG " is  a dead variable." :: nil)
  | KPrim => OK tt
  | KFun _ => OK tt
  | KNode n' =>
      let* a := G.may_alias (Pto d) n n' in
      if a then Error (MSG (fst arg) :: nil)
      else OK tt
  end.

Fixpoint no_alias (d:domain) (l : list (ident * KVar)) : res unit :=
  match l with
  | nil => OK tt
  | (id1,v1)::l =>
      match v1 with
      | KDead => Error (MSG " argument " :: MSG id1 :: MSG " is a dead variable." :: nil)
      | KPrim => no_alias d l
      | KFun _ => no_alias d l
      | KNode n => match forall_check (no_alias_node d n) l with
                   | Error m => Error (MSG " argument " :: MSG id1 :: MSG " has a potential alias with " :: m ++ MSG "." ::nil)
                   | OK  _ => no_alias d l
                   end
      end
  end.

Fixpoint aeval_expr (te:tenv) (env:aenv) (vars : smaplist KVar) (vars_a: smaplist atom) (d:domain) (e:GEXPR.t) : res (domain * KVar) :=
  match e with
  (*| GEXPR.Atm a => aeval_atom te env d a - to prevent a recursive call *)
  | GEXPR.Get e fd => let* (d,v) := aeval_expr te env vars vars_a d e in
                      match v with
                      | KDead => Error (MSG "(bug) Return expression is dead" :: nil)
                      | KPrim => Error (MSG "(bug) Return expression - cannot dereference a primitive type" :: nil)
                      | KFun _ => Error (MSG "(bug) Return expression - cannot dereference a function" :: nil)
                      | KNode n =>
                          let* fd := subst_edge vars_a fd in
                          bind_path d n fd
                      end
  | GEXPR.Var id    => match MapList.find_err string_dec id vars with
                       | OK kv => OK (d,kv)
                       | Error _ => Error (MSG id :: nil)
                       end
  end.

Definition aeval_call(te:tenv) (env: aenv) (d:domain) (id:ident) (bt: btyp) (args:list atom) : res (domain* KVar) :=
  match aget_function env (Vars d) id with
    | OK af =>
        let fret := fn_body af in
        match bind_args te env d args (fn_params af) with
        | OK (d,params,params_a) =>
            match no_alias d params with
            | OK _ =>
                (* Apply the function summary *)
                match fret with
                | (RPrim,pure) => OK (set_pure pure d,KPrim)
                | (RDeep e,pure) =>
                    aeval_expr te env params params_a (set_pure pure d) e
                end
            | Error m => Error (MSG "function " :: MSG id :: m)
            end
        | Error err =>
            Error (MSG "function " :: MSG id :: MSG " mismatch arguments" :: MSG nl :: err)
        end
    | Error _ => Error (MSG "function " :: MSG id :: MSG " Not_found" :: nil)
    end.

End CALL.


Fixpoint aeval_atom (te:tenv) (env:aenv) (d:domain) (a:atom) {struct a} :=
  match a with
  | AVar id bt    =>
      let* v := eval_var env  (Vars d) id (*bt*) in
      OK (d,v)
  | AArrayGet ar i _ bt => array_get aeval_atom te env d ar i (*bt*)
  | ARecordProj ar fd _ bt => record_proj_get aeval_atom te env d ar fd (*bt*)
  | APureCall id btf l _   =>
      let* (d,v) := aeval_call aeval_atom te env d id btf l in
      if IsPure d
      then OK (d,v)
      else Error (MSG "Function " :: MSG id :: MSG " is not pure." :: nil)
  | _ => OK (d,KPrim)
  end.

Definition set_variable (v:ident) (k:KVar) (d:domain) :=
  mkdom (Vars.set v k (Vars d)) (Pto d) (Atoms d) (IsPure d).

(* Could try to normalise the expression e.g. 1 + 1 -->  2
   Also, identify injective operations
 *)

(* Definition classify_atom (a1 a2:atom) : cedge :=
  match a1 , a2 with
  | ATrue, ATrue => MUST
  | AFalse, AFalse => MUST
  | AInt32 i _ , AInt32 j _ => if Integers.Int.eq i j then MUST else NOTMAY
  | AInt64 i _ , AInt64 j _ => if Integers.Int64.eq i j then MUST else NOTMAY
  | AConstr i _, AConstr j _ => if String.eqb i j then MUST else NOTMAY
  | AVar i _ , AVar j _      => if String.eqb i j then MUST else MAY
  | _ , _ =>  match Syntax.AtomOrdered.atom_compare a1 a2 with
              | Eq => MUST
              | _  => MAY
              end
end. *)



Definition may_atom (a1 a2:atom) : bool :=
  match a1 , a2 with
  | ATrue, ATrue => true
  | AFalse, AFalse => true
  | ATrue, AFalse | AFalse, ATrue => false
  | AInt32 i _ , AInt32 j _ => if Integers.Int.eq i j then true else false
  | AInt64 i _ , AInt64 j _ => if Integers.Int64.eq i j then true else false
  | AConstr i _ _, AConstr j _ _ => if String.eqb i j then true else false
  | _ , _ => true
  end.

Definition may_edge (e1 e2:EdgeLabel.t) :=
  match e1 , e2 with
  | EdgeLabel.Top , EdgeLabel.Top => true
  | EdgeLabel.Index _ , EdgeLabel.Top | EdgeLabel.Top , EdgeLabel.Index _ => true
  | EdgeLabel.Field x , EdgeLabel.Field y => if Ident.eq_dec x y then true else false
  | EdgeLabel.Index a1, EdgeLabel.Index a2 => may_atom a1 a2
  | _ , _ => true (* cannot happen, don't care *)
  end.


Definition update_var (l:list int) (k:KVar)  :=
  match k with
  | KDead => KDead
  | KPrim => KPrim
  | KFun f => KFun f
  | KNode n => if List.in_dec Int.eq_dec n l then KDead else KNode n
  end.

(*Definition update_vars (d:domain) (l:list int)  :=
  mkdom (STree.map (fun _ x => (update_var l) x) (Vars d)) (Pto d) (Atoms d). *)

Definition pp_write (a:atom) (l:list EdgeLabel.t) (vl:atom) :=
  Pp.seq (Printer.pp_atom a :: (pp_list (Bstr ".") EdgeLabel.pp l) :: Bstr " <- " :: Printer.pp_atom vl :: nil).


Definition write (te:tenv) (env:aenv) (d:domain) (a:atom) (l:list EdgeLabel.t) (vl:atom)  : res (domain * KVar * bool) :=
  let* (d,ea) := aeval_atom te env d a in
  let* (d,v) := aeval_atom te env d vl  in
  match ea with
  | KDead | KPrim | KFun _ => fail (* We could give error messages *)
  | KNode n => (* this is a reference *)
      match v  with
      | KDead => (* want to write an arbitrary value - this is bad - let's stop *)
            fail
      | KPrim => OK (d,KNode n, false) (* This is not an alias *)
      | KFun _ => OK (d,KNode n, false) (* This is not an alias *)
      | KNode n' => let* f := G.depth (Pto d) in
                    match G.check_must_alias  f n l n' (Pto d) with
                    | OK _ =>  OK (d,KNode n,true)
                    | Error _ =>
                        let reason := Bstr "The written value is a reference but no MUST alias is found." in
                        let l1 := Pp.seq (Printer.pp_atom a ::
                                            Bstr " is mapped to node n" :: Bstr (string_of_int n) :: nil) in
                        let l2 := Pp.seq (Printer.pp_atom vl ::
                                            Bstr " is mapped to node n" :: Bstr (string_of_int n') :: nil) in
                        Error (msg (Pp.pp (Pp.stack Left (reason :: l1 :: l2 :: pp_domain d :: nil))))
                    end
      end
  end.





Definition array_set (te:tenv) (env:aenv) (d:domain) (a:atom) (i:atom) (vl:atom)  : res (domain * KVar) :=
  (* Some write are pure, somehow, if this is a nop *)
  let* (r,_) := write te env d a (cons (EdgeLabel.Index i) nil) vl in
  let (d,kv) := r in
  OK (set_pure false d,kv).


Definition record_set (te:tenv) (env:aenv) (d:domain) (a:atom) (fd:ident) (vl:atom) : res (domain * KVar) :=
  let* (r,_) := write te env d a (cons (EdgeLabel.Field fd) nil) vl  in
  let (d,kv) := r in
  OK (set_pure false d,kv).






(*
Definition deep_access (env:aenv) (d:domain) (a:atom) (acc : list EdgeLabel.t)  : res (domain * KVar) :=
  let* (d,v) := aeval_atom env d a in
  match v with
  | KDead => fail
  | KPrim => fail
  | KFun _ => fail (* Shouldn't happen - typing *)
  | KNode n => bind_path d n acc
  end.
 *)





Definition eval_comp (te:tenv) (env : aenv) (d:domain) (c:comp)  : res (domain * KVar) :=
  match c with
  | CpAtom a => aeval_atom te env d a
  | CpArraySet a i vl _ => array_set te env d a i vl
  | CpRecordUpdate a fd vl _ => record_set te env d a fd vl
  | CpCall f btf args _  => aeval_call aeval_atom te env d f btf args
  end.

Definition is_pure_function (env:aenv) (f:ident) : res bool :=
  match STree.get f env with
  | None => fail
  | Some v =>
      match v with
      | ALit _ => fail
      | AFun f => OK (snd (fn_body f))
      end
  end.

Definition inter_pto (g1 g2: G.t) : res (G.t * (IntMap.t int *  IntMap.t int)) :=
  let* lb1 := G.get_node_label g1 (G.root g1)  in
  let* lb2 := G.get_node_label g2 (G.root g2) in
  if typ_eq_dec lb1 lb2 then
    G.inter (TypOrdered.depth lb1) (G.root g1) g1 (G.root g2) g2 (G.mkroot lb1,(IntMap.empty _,IntMap.empty _))
  else fail.



Definition merge_var (m1: IntMap.t int) (m2:IntMap.t int) (k1 k2:KVar)  :=
  match k1 , k2 with
  | KDead , _ | _ , KDead => KDead
  | KPrim , KPrim => KPrim
  | KPrim , _| _ , KPrim =>  KDead (* Should not happen. *)
  | KFun a , KFun b  => if afunction_eq_dec a b then KFun a else KDead
  | KFun _ , _ | _ , KFun _ => KDead
  | KNode n1 , KNode n2 =>
      match IntMap.find n1 m1 , IntMap.find n2 m2 with
      | Some n1' , Some n2' =>
          if Int.eq_dec n1' n2' then KNode n1'
          else KDead
      |  _       ,  _        => KDead
      end
  end.

Definition merge_ovar (m1 m2:IntMap.t int) (k1 k2 : option KVar) :=
  match k1 , k2 with
  | None , None => None
  | None , _ | _ , None => None
  | Some k1, Some k2 => Some (merge_var m1 m2 k1 k2)
  end.

(*
  x -> v1   x -> v2
  => KNode n1, KNode n2

------------------------
   [n1 -> n] |
              =>
   [n2 -> n] |
*)


Definition merge_vars (m1 m2: IntMap.t int) (v1 v2 : STree.t KVar) :=
  STree.combine  (merge_ovar m1 m2) v1 v2.

Definition merge_atoms (m1 m2:SMap.t (list atom)) :=
  PMap.combine (ListSet.set_inter Syntax.AtomOrdered.eq_dec) m1 m2.

Definition merge_domain (d1 d2:domain) : res domain :=
  let (v1,pt1,at1,p1) := d1 in
  let (v2,pt2,at2,p2) := d2 in
  let* (pto,m) := inter_pto pt1 pt2 in
  let v := Vars.of_vars (merge_vars (fst m) (snd m) (Vars.Vars v1) (Vars.Vars v2)) in
  let atm := merge_atoms at1 at2 in
  OK (mkdom v pto atm (p1 && p2)).


Definition join_sfunction (s1 s2:sfunction)  : res sfunction :=
  match s1 , s2 with
  | RPrim , RPrim => OK RPrim
  | RPrim , RDeep e | RDeep e , RPrim => efail (* Or maybe e is just an atom ... *)
  | RDeep e1 , RDeep e2 => if GEXPR.eq_dec  e1 e2
                           then OK (RDeep e1)
                           else fail
  end.


(*Definition join_sfunction (s1 s2:sfunction) : res sfunction :=
  match s1 , s2 with
  | RPrim , RPrim => OK RPrim
  | RPrim , RDeep e | RDeep e , RPrim =>
                        if btyp_is_prim (GEXPR.btyp_of_gexpr e)
                        then OK RPrim else efail
  | RDeep e1 , RDeep e2 => if GEXPR.eq_dec e1 e2
                          then OK (RDeep e1)
                           else
                             if btyp_is_prim (GEXPR.btyp_of_gexpr e1) &&
                                  btyp_is_prim (GEXPR.btyp_of_gexpr e2)
                             then OK RPrim
                             else efail
  end.
*)





Definition merge  (v1 v2 : domain + (sfunction * bool) ) :=
  match v1 , v2 with
  | inl d1 , inl d2 => let* d := merge_domain d1 d2 in
                       OK (inl d)
  | inr (sf1,p1) , inr (sf2,p2) => let* sf := join_sfunction sf1 sf2 in
                         OK (inr (sf,p1 && p2))
  | _ , _ => fail
  end.




Definition update_variable (v:ident) (d:domain) (kv:KVar) :=
  set_variable v kv (forget_var v d).



Fixpoint expr_of_list (e:GEXPR.t) (l:list EdgeLabel.t) :=
  match l with
  | nil => e
  | fd::l => expr_of_list (GEXPR.Get e fd) l
  end.


Definition expr_of_path (l : list EdgeLabel.t) :=
  match l with
  | nil => Error (MSG "Invalid path expression" :: nil)
  | e::l => match e with
            | EdgeLabel.Field fd => OK (expr_of_list (GEXPR.Var fd) l)
            |  _                 => Error (MSG "Invalid path expression" :: nil)
            end
  end.

Fixpoint eval_statement (te:tenv) (env: aenv) (s:statement) (d:domain) : res (domain + (sfunction * bool)) :=
  match s with
  | StSkip    => OK (inl d)
  | StSet v c => match eval_comp te env d c  with
                 | OK (d,k) =>  OK (inl (update_variable v d k))
                 | Error m  => Error (MSG "In statement " ::
                                        MSG (Pp.pp (Pp.pp_statement s)) ::
                                        MSG " " :: m)
                 end
  | StIfThenElse a s1 s2 =>
      (* I don't care about the conditional *)
      let* _  := aeval_atom  te env d a in
      let* d1 := eval_statement te env s1 d in
      let* d2 := eval_statement te env s2 d in
      merge d1 d2
  | StSwitch a l => let ld := List.map (fun x => eval_statement te env (snd x) d) l in
                    merge_list merge ld
  | StSequence s1 s2 => let* d1 := eval_statement te env s1 d in
                        match d1 with
                        | inr _ => Error (MSG "sequence is not well-typed" :: nil)
                        | inl d2 => eval_statement te env s2 d2
                        end
  | StReturn a =>
      (* If [a] is an arithmetic expression, we could alsoe return it *)
      let* (d,v) :=  aeval_atom te env d a in
      match v with
      | KDead => Error (MSG "return of a dead expression" :: nil)
      | KFun _ => Error (MSG "return of a function pointer" :: nil)
      | KPrim => OK(inr (RPrim,IsPure d))
      | KNode n =>
          let* p := G.get_path (Pto d) n in
          let* e := expr_of_path p in
          OK (inr (RDeep e,IsPure d))
      end
  | StAttr a s => if String.eqb "mustalias" a then Error (msg (Pp.pp (pp_domain d)))
                  else eval_statement te env s d
  end.

Definition path_of_list (l:list ident) : STree.t (list EdgeLabel.t) :=
  List.fold_right (fun e acc => STree.set e nil acc) STree.empty l.


Fixpoint join_edges {A: Type} (e:EdgeLabel.t) (l:list (EdgeLabel.t * A)) : EdgeLabel.t  :=
  match l with
  | nil => e
  | (e1,_) :: l => join_edges (EdgeLabel.join e e1) l
  end.

Definition union_path (p1 p2 : option (list EdgeLabel.t)) :=
  match p1, p2 with
  | None , x | x , None => x
  | Some p1 , Some p2 => None (* This is not possible *)
  end.

Fixpoint xpath_above_alias (d:domain) (fuel:nat) (n:int) :=
  (* Direct aliases *)
  let p := path_of_list (Vars.vars_of_node (Vars d) n) in
  match G.get_parent n (Pto d) with
  | None => OK p
  | Some (e,n') =>
      match fuel with
      | O =>  Error (msg "Not enough fuel")
      | S fuel => let* a := xpath_above_alias d fuel n' in
                  let l := G.get_successors (Pto d) n' in
                  let l := List.filter (fun x => may_edge e (fst x)) l in
                  let e := join_edges e l in
                  OK (STree.combine union_path p (STree.map (fun x p => e::p) a))
      end
  end.

(** [path_above_alias] returns paths in reverse order *)
Definition path_above_alias (te:tenv) (env:aenv) (d:domain) (a:atom) :=
  let* (d,v) := aeval_atom te env d a in
  match v with
  | KNode n =>
      let* f := G.depth (Pto d) in
      xpath_above_alias d f n
  | KPrim    => OK (STree.empty)
  | KFun _   => OK (STree.empty)
  | KDead    => Error  (msg "path_above_alias: atom is dead - aliased with anything")
  end.

Fixpoint flat_map_err {A B: Type} (F : A -> res (list B)) (l:list A) : res (list B) :=
  match l with
  | nil => OK nil
  | e::l' => let* le := F e in
             let* ll' := flat_map_err F l' in
             OK (le ++ ll')
  end.

Fixpoint xpath_below_alias (d:domain) (fuel:nat) (n:int) :=
  let p := List.map (fun id => (nil,id)) (Vars.vars_of_node (Vars d) n) in
  match fuel with
  | O => Error (msg "Not enough fuel")
  | S fuel => let l := G.get_successors (Pto d) n in
              let* a := flat_map_err (fun '(e,n') => let* l := xpath_below_alias d fuel n' in
                                                OK (List.map (fun '(p,v) => (e::p,v)) l)) l in
              OK (p ++ a)
  end.

Definition path_below_alias (te:tenv) (env:aenv) (d:domain) (a:atom) :=
  let* (d,v) := aeval_atom te env  d a in
  match v  with
  | KNode n =>
      let* f := G.depth (Pto d) in
      xpath_below_alias d f n
  | KPrim    => OK nil
  | KFun _   => OK nil
  | KDead    => Error  (msg "path_above_alias: atom is dead - aliased with anything")
  end.

Definition any_alias (env:aenv) (d:domain)  :=
  STree.map (fun _ v => if is_dead v then true else false) (Vars.Vars (Vars d)).

(*Definition may_alias (env:aenv) (d:domain) (a1 a2:atom) :=
  match eval_atom env (Vars d) a1 , eval_atom env (Vars d) a2 with
  | KPrim , _ | _ , KPrim => false (* primitive values are not in alias *)
  | KDead , _ | _ , KDead => true  (* dead variables point anywhere *)
  | KNode n1 , KNode n2   => (* not totally obvious *)
*)


Fixpoint assigned (s:statement) : SSet.t :=
  match s with
  | StSkip     => SSet.empty
  | StSet id _ => SSet.add id  SSet.empty
  | StIfThenElse _ s1 s2 => SSet.union (assigned s1) (assigned s2)
  | StSwitch _ l => List.fold_right (fun e acc => SSet.union (assigned (snd e)) acc) SSet.empty l
  | StSequence s1 s2 => SSet.union (assigned s1) (assigned s2)
  | StReturn _ => SSet.empty
  | StAttr _ s => assigned s
  end.

Definition bind_param (v: Vars.t) (g:G.t) (p:ident * typ)  :=
  if typ_is_prim (snd p)
  then OK (Vars.set (fst p) KPrim v , g)
  else (* add a path in the graph *)
    let* (g1,n) := G.create_path EdgeLabel.next_label (G.root g) (EdgeLabel.Field (fst p) :: nil) g in
    let (n,ty) := n in
    if typ_eq_dec ty (snd p)
    then  OK (Vars.set (fst p) (KNode n) v,g1)
    else fail (* Cannot happen *).

Fixpoint bind_params (v:Vars.t) (g:G.t) (l :list (ident * typ)) :=
  match l with
  | nil => OK(v,g)
  | p::l => let* (v,g) := bind_params v g l in
            bind_param v g p
  end.

Definition init_domain (l:list (ident * typ)) :=
  (* We make a dummy record which field are the parameters *)
  let rec := TRecord "root"%string l in
  let g := G.mkroot rec in
  (* We bind each of the parameter in the graph *)
  bind_params (Vars.empty) g l.




(*Definition path_to_expr (params:smaplist btyp) (l:list EdgeLabel.t) :=
  match l with
  | nil => fail (* This is not possible *)
  | EdgeLabel.Field p :: l =>
      let* i := find_index p params in

      OK (RDeep i l)
  | _ => fail
  end.
 *)

Definition domain_of_function (te:tenv) (f:function) : res domain :=
  let* params := err_of_opt (Denot.map_err (btyp_to_typ te) (fn_params f)) in
  if MapList.nodup  Ident.eq_dec params
  then let modified := assigned (fn_body f) in
       if List.forallb (fun i_t => negb (SSet.mem (fst i_t) modified)) params
       then let* (v,pto) := init_domain params in
            OK (mkdom v pto (SMap.init nil) true)
       else fail
  else fail.




Definition sfunction_of_path (params: list (ident * btyp)) (r : sfunction ) : res sfunction :=
  let params := List.map fst params in
  match r with
  | RPrim => OK RPrim
  | RDeep e => match GEXPR.check_expr params e with
               | OK _ => OK (RDeep e)
               | Error m => Error (MSG "Symbolic expression ":: MSG (Pp.pp (GEXPR.pp e)) :: MSG " is invalid. " :: MSG nl :: m)
               end
  end.

Definition eval_function (te:tenv) (env:aenv) (f:function) : res afunction :=
  let* d := domain_of_function te f in
  let* d := eval_statement te env (fn_body f) d in
  match d with
  | inr (r,pure) =>
      let* r := sfunction_of_path (fn_params f) r in
      let* tr := err_of_opt (btyp_to_typ te (fn_return f)) in
      let* params := err_of_opt (Denot.map_err (btyp_to_typ te) (fn_params f)) in
      OK (mk_function tr params (r,pure))
  |  _    => fail
  end.


Definition literal_is_primitive (l:literal) :=
  match l with
  | LTrue | LFalse | LInt32 _ _ | LInt64 _ _ => true
  | _ => false
  end.

Fixpoint get_write_arg (l:list (param_attr * btyp)) : res positive :=
  match l with
  | nil => fail
  | (attr,_) ::l =>
      match attr with
      | AttrWrite    => OK xH
      | _ => let* i := get_write_arg l in
             OK (Pos.succ i)
      end
  end.

Definition get_return (te:tenv)(l:list (param_attr * btyp)) (r:btyp) : res sfunction  :=
  let* ty := err_of_opt (btyp_to_typ te r) in
  if typ_is_prim ty then OK RPrim
  else let* i := get_write_arg l  in
       OK (RDeep (GEXPR.Var (Printer.string_of_positive i) )).

Fixpoint xmapi {A B:Type} (F: positive -> A -> B) (i:positive) (l:list A) : list B :=
  match l with
  | nil => nil
  | e::l => F i e :: xmapi F (Pos.succ i) l
  end.

Definition mapi {A B:Type} (F: positive -> A -> B) (l:list A) := xmapi F xH l.

Definition afunction_of_sfunction (l:list (param_attr * typ)) (r:typ) (s:sfunction):=
  mk_function r (mapi (fun i e => (Printer.string_of_positive i,snd e)) l) (s,true).

Definition eval_globdef (te:tenv) (env:aenv) (gd:globdef) : res aenv :=
  match gd with
  | DefConst id l t => OK (STree.set id (ALit (literal_is_primitive l)) env)
  | DefFun id f     => match eval_function te env f with
                       | OK f => OK (STree.set id (AFun f) env)
                       | Error e => Error (MSG "Must alias analysis:" ::
                            MSG "cannot analyze function " ::
                            MSG id :: MSG nl :: e)
                       end
  | DeclConst id t  => let* ty := err_of_opt (btyp_to_typ te t) in
                       OK (STree.set id (ALit (typ_is_prim ty )) env)
  | DeclFun id params r => let* ret := get_return te params r in
                           let* params := err_of_opt (mmap_assoc (btyp_to_typ te) params) in
                           let* r      := err_of_opt (btyp_to_typ te r) in
                           OK (STree.set id (AFun (afunction_of_sfunction params r ret)) env)
  end.

Fixpoint eval_globdefs (te: tenv) (env:aenv) (l:list globdef) : res aenv :=
  match l with
  | nil => OK env
  | gd:: l => let* env' := eval_globdef te env gd in
              eval_globdefs te env' l
  end.

Definition transl_comp (te:tenv) (env:aenv) (d:domain) (c:comp) : res comp :=
  match c with
  | CpArraySet a i v bt =>
      match write te env d a (cons (EdgeLabel.Index i) nil) v  with
      | Error m => Error m
      | OK(_,b) =>
          OK (if b then CpAtom a
              else c)
      end
  | CpRecordUpdate a i v bt =>
      match write te env d a (cons (EdgeLabel.Field i) nil) v  with
      | Error m =>  let err := Pp.pp (pp_domain d) in
                    Error (MSG err :: nil)
      | OK(_,b) => if b then OK (CpAtom a)
                   else OK c
      end
  | _  => OK c
  end.


Definition comp_has_update (c:comp) :=
  match c with
  | CpArraySet a i v bt => true
  | CpRecordUpdate a i v bt => true
  | _  => false
  end.

Fixpoint statement_has_update (s:statement) :=
  match s with
  | StSkip     => false
  | StSet id c => comp_has_update c
  | StIfThenElse a s1 s2 => statement_has_update s1 || statement_has_update s2
  | StSwitch a l =>
      List.existsb (fun x => statement_has_update (snd x)) l
  | StSequence s1 s2 =>
      statement_has_update s1 || statement_has_update s2
  | StReturn a => false
  | StAttr _ s => statement_has_update s
  end.

Fixpoint atom_is_var (id:ident) (a:atom) :=
  match a with
  | AVar id' _ => if Ident.eq_dec id id' then true else false
  | AUnaryOp UopPlus a _ => atom_is_var id a
  | ACast a _    => atom_is_var id a
  | _          => false
  end.

Definition comp_is_var (id:ident) (c:comp) :=
  match c with
  | CpAtom a => atom_is_var id a
  | _ => false
  end.






Definition is_nop (s:statement) :=
  match s with
  | StSet id c => comp_is_var id c
  | StSkip     => true
  | _          => false
  end.

Definition mk_seq (s1 s2:statement) :=
  if is_nop s1 then s2
  else if is_nop s2 then
         s1
       else StSequence s1 s2.

Fixpoint has_nop (s:statement) :=
  match s with
  | StSkip           => true
  | StSequence s1 s2 => has_nop s1 || has_nop s2
  | StIfThenElse _ s1 s2 =>
      (if is_nop s1 then false else has_nop s1)
      ||
      (if is_nop s2 then false else has_nop s2)
  | StSwitch a l => List.existsb (fun x => has_nop (snd x)) l
  | StReturn _   => false
  | StSet id c   => is_nop s
  | StAttr _ s   => has_nop s
  end.



Fixpoint transl_statement (te:tenv) (env: aenv) (d:domain) (s:statement) : res statement :=
  match s with
  | StSkip     => OK StSkip
  | StSet id c => let* c' := transl_comp te env d c in
                  OK (StSet id c')
  | StIfThenElse a s1 s2 =>
      let* s1' := transl_statement te env d s1 in
      let* s2' := transl_statement te env d s2 in
      OK (StIfThenElse a s1' s2')
  | StSwitch a l => let* l' := MapList.map_err (transl_statement te env d) l in
                    OK (StSwitch a l')
  | StSequence s1 s2 =>
      let* s1' := transl_statement te env d s1 in
      let* d'  := eval_statement te env s1 d in
      match d' with
      | inl d1 => let* s2' := transl_statement te env d1 s2 in
                  OK (mk_seq s1' s2')
      | inr _  => fail
      end
  | StReturn a => OK (StReturn a)
  | StAttr a s => let* s := transl_statement te env d s in
                  OK (StAttr a s)
  end.




Definition transl_function (te:tenv) (env:aenv) (f:function) :=
  let* d := domain_of_function te f in
  let* s' := transl_statement te env d (fn_body f) in
  if has_nop s'
  then Error (msg (Pp.pp (Pp.pp_statement s')))
  else OK (mk_function (fn_return f) (fn_params f) s').

Definition transl_globdef (te:tenv) (env:aenv) (g:globdef) :=
  match g with
  | DefFun id f =>
      match transl_function te env f with
      | OK f' => OK (DefFun id f')
      | Error m => Error (MSG "PASS elim alias:" ::
                            MSG "cannot compile function " ::
                            MSG id :: MSG "\n" :: m)
      end
  | _      => OK g
  end.

Fixpoint transl_globdefs (te:tenv) (env: aenv) (l:list globdef) : res (list globdef) :=
  match l with
  | nil => OK l
  | gd::l => let* env' := eval_globdef te env gd in
             let* gd'  := transl_globdef te env gd in
             let* gds := transl_globdefs te env' l in
             OK (gd'::gds)
  end.

Definition transl_program (te:tenv)  (p: program) : res program :=
  let* te := err_of_opt (tenv_of_type_defs (prog_types p)) in
  let* gds :=  transl_globdefs te STree.empty (prog_defs p) in
  OK (mk_program gds (prog_types p) (prog_tabs p)).
