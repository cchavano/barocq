(** Must alias for imp1 *)
From compcert Require Import Maps.
Require Import Uint63.
Require Import String FMapInterface FMapList ZArith Int ListSet.
From BarocqComp Require Import Error Maps2 Types Imp1 Graph Typing Utils Draw.
From Coq Require Import FMapPositive.
Require Import Syntax.
Import Typed.
Import Imp1.Typed.

Module Pp.
  Import String.
  Import ListNotations.

  Fixpoint appendl (l:list string) : string :=
    match l with
    | nil => ""
    | e::l => append e (appendl l)
    end.

  Fixpoint pp_atom (a:atom) :=
    match a with
    | ATrue _ => Bstr "true"%string
    | AFalse _ => Bstr "false"%string
    | AInt32 i _ => Bstr "int"%string
    | AInt64 i _ => Bstr "int64"%string
    | AConstr s  _ => Bstr s
    | AVar s _     => Bstr s
    | ACast a bt   => Bcat (Bstr "(btyp)"%string) (pp_atom a)
    | AUnaryOp o a _ => Bcat (Bstr "op"%string) (pp_atom a)
    | ABinaryOp o a1 a2 _ => Bcat (pp_atom a1)
                             (Bcat (Bstr "op"%string) (pp_atom a2))
    end.

  Definition array_index {A: Type} (f:A -> box) (v:A) :=
    Bcat (Bstr "[") (Bcat (f v) (Bstr "]")).

  Definition pp_comp (c:comp) :=
    match c with
    | CpAtom a _ => pp_atom a
    | CpArrayGet a i _ _ => Bcat (pp_atom a )
                                 (array_index pp_atom i)
    | CpRecordProj a i _ _ => Bcat (pp_atom a)
                              (Bcat (Bstr ".") (Bstr i))
    | CpRecordUpdate a f v _ => Bcat (pp_atom a)
                                (Bcat
                                   (Bcat (Bcat (Bstr "<-") (Bstr f)) (Bstr ":="))
                                   (pp_atom v))
    | CpArraySet a i v _    => Bcat (pp_atom a)
                                      (Bcat
                                         (Bcat (array_index pp_atom i)
                                            (Bstr ":=")) (pp_atom v))
    | CpDeepAccess a l _ => Bcat (pp_atom a) (Bstr "...")
    | CpCall a l _ => Bcat (pp_atom a) (Bcat (Bstr "(")
                                          (Bstr ")"))
  end.

  Fixpoint pp_statement (s:statement) :=
    match s with
    | StSet i c => Bcat (Bstr i) (Bcat (Bstr "=") (pp_comp c))
    | StIfThenElse a s1 s2 =>
        let s1 := Bcat (Bstr " then ") (pp_statement s1) in
        let s2 := Bcat (Bstr " else ") (pp_statement s2) in
        let c  := pp_atom a in
        let cd := Bcat (Bstr "if ") c in
        Bstack cd (Bstack s1 s2 Left) Left
    | StSwitch a l => Bstr "case..."
    | StSequence s1 s2 =>
        let s1 := pp_statement s1 in
        let s2 := pp_statement s2 in
        Bstack (Bcat s1 (Bstr ";"))
               s2 Left
    | StReturn a => Bcat (Bstr "return ") (pp_atom a)
    end.

End Pp.

Inductive KVar :=
| KDead (* Dead variable - may point anywhere *)
| KPrim (* Primitive type - no alias *)
| KNode (n:int) (* Reference in the alias graph *).

Module EdgeLabel <: OrderedType.

Inductive edge :=
| Field (id:Syntax.ident)
| Index (a:atom)
| Top.

Definition pp (e:edge) :=
  match e with
  | Field id => Bcat (Bstr ".") (Bstr id)
  | Index a  => Bcat (Bstr "[") (Bcat (Pp.pp_atom a)
                                   (Bstr "]"))
  | Top      => Bstr "T"
  end.


Definition next_label (t:typ) (e:edge) :=
  match t, e with
  | TArray ty , (Index _ | Top) => OK ty
  | TRecord _ l  , Field fd => MapList.find_err Ident.eq_dec fd l
  | _  , _ => fail
  end.




Definition edge_compare (e1 e2:edge) : comparison :=
  match e1, e2 with
  | Field i1 , Field i2 => String.compare i1 i2
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

End EdgeLabel.

Module G := Make(TypOrdered)(EdgeLabel).

Record domain := mkdom
    {
      Vars : STree.t KVar;
      Pto  : G.t;
      Atoms: SMap.t (list atom); (* Atoms[x] = a -> x is a variable of a *)
    }.

Definition pp_kvar (k:KVar) : box :=
    match k with
    | KDead => Bstr "dead"
    | KPrim => Bstr "primitive"
    | KNode n => Bcat (Bstr "n") (Bstr (string_of_int n))
    end.

Definition pp_vars (s:STree.t KVar) : box :=
  STree.fold (fun acc k v => Bstack acc (Bcat (Bstr k)
                                           (Bcat
                                              (Bstr "->") (pp_kvar v))) Left) s Bemp.

Definition pp_domain (d:domain) :=
  Bstack (Bstr "") (Bcat (Bframe "_" "|"  (pp_vars (Vars d))) (G.pp (Pto d))) Middle.



Inductive sfunction :=
| RPrim (* return a primitive value *)
| RDeep (id:nat) (acc : list EdgeLabel.t)
| RAny.

Definition sfunction_eq_dec (s1 s2:sfunction) : {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
  apply (List.list_eq_dec EdgeLabel.eq_dec acc acc0).
  apply Nat.eq_dec.
Defined.

Definition afunction := Syntax.function sfunction btyp .

Inductive alit := | IsPrim (b:bool).

Inductive aglobdef :=
| ALit (b:bool) (* Is-it primitive ? *)
| AFun (f:afunction).

Definition aenv := STree.t aglobdef.

Definition forget_var (x:ident)  (d:domain) :=
  mkdom (STree.set x KDead (Vars d))
           (List.fold_right (fun a g => G.update_edgelabel (EdgeLabel.Index a) EdgeLabel.Top g) (Pto d) (SMap.get x (Atoms d)))
           (SMap.set x nil (Atoms d)).

Definition is_prim_literal (env:aenv) (x:ident) :=
  match STree.get x env with
  | Some (ALit b) => b
  | _             => false
  end.

Definition eval_atom (env:aenv) (vars: STree.t KVar) (a:atom)  :=
  match a with
  | AVar i _    => match STree.get i vars with
                   | Some v => v
                   | None   => if is_prim_literal env i
                               then KPrim
                               else KDead
                   end
  |  _          => KPrim (** not well-typed !!! *)
  end.



Definition set_variable (v:ident) (k:KVar) (d:domain) :=
  mkdom (STree.set v k (Vars d)) (Pto d) (Atoms d).

Definition set_pto (g:G.t) (d:domain) :=
  mkdom (Vars d) g (Atoms d).


Definition edge_of_access (a:Typed.access) : EdgeLabel.t :=
  match a with
  | AcRecordField id _ _ => EdgeLabel.Field id
  | AcArrayIndex a   _ _ => EdgeLabel.Index a
  end.

Definition bind_path (d:domain) (o:int) (acc:list EdgeLabel.t) : res (domain * KVar) :=
  let* (g,n'_ty) := G.create_path EdgeLabel.next_label o acc (Pto d) in
  if typ_is_prim (snd n'_ty)
  then OK (d,KPrim) (* Do not record primitive access *)
  else OK (set_pto g d,KNode (fst n'_ty)). (* TODO update Atomes *)


Definition deep_access (env:aenv) (d:domain) (a:atom) (acc : list EdgeLabel.t)  : res (domain * KVar) :=
  match eval_atom env (Vars d) a  with
  | KDead =>  OK(d,KDead)
  | KPrim => fail (* Shouldn't happen - typing *)
  | KNode n => bind_path d n acc
  end.

Definition array_get  (env:aenv) (d:domain) (a:atom) (i:atom)  : res (domain * KVar) :=
  deep_access env d a (cons (EdgeLabel.Index i) nil).

Definition record_get (env:aenv) (d:domain) (a:atom) (fd:ident)  : res (domain * KVar) :=
  deep_access env d a (cons (EdgeLabel.Field fd) nil).

(* Could try to normalise the expression e.g. 1 + 1 -->  2
   Also, identify injective operations
 *)

Definition classify_atom (a1 a2:atom) : cedge :=
  match a1 , a2 with
  | ATrue _ , ATrue _ => MUST
  | AFalse _ , AFalse _ => MUST
  | AInt32 i _ , AInt32 j _ => if Integers.Int.eq i j then MUST else NOTMAY
  | AInt64 i _ , AInt64 j _ => if Integers.Int64.eq i j then MUST else NOTMAY
  | AConstr i _, AConstr j _ => if String.eqb i j then MUST else NOTMAY
  | AVar i _ , AVar j _      => if String.eqb i j then MUST else MAY
  | _ , _ =>  match Syntax.AtomOrdered.atom_compare a1 a2 with
              | Eq => MUST
              | _  => MAY
              end
end.

Definition classify_edge (e1 e2:EdgeLabel.t) :=
  match e1 , e2 with
  | EdgeLabel.Top , EdgeLabel.Top => MAY
  | EdgeLabel.Index _ , EdgeLabel.Top | EdgeLabel.Top , EdgeLabel.Index _ => MAY
  | EdgeLabel.Field x , EdgeLabel.Field y => if Ident.eq_dec x y then MUST else NOTMAY
  |  _ , _ => NOTMAY
  end.

Definition update_var (l:list int) (k:KVar)  :=
  match k with
  | KDead => KDead
  | KPrim => KPrim
  | KNode n => if List.in_dec Int.eq_dec n l then KDead else KNode n
  end.

Definition update_vars (d:domain) (l:list int)  :=
  mkdom (STree.map (fun _ x => (update_var l) x) (Vars d)) (Pto d) (Atoms d).


Definition write (env:aenv) (d:domain) (a:atom) (l:list EdgeLabel.t) (vl:atom)  : res (domain * KVar * bool) :=
    match eval_atom env (Vars d) a  with
    | KDead | KPrim => fail (* We could give error messages *)
    | KNode n => (* this is a reference *)
        match eval_atom env (Vars d) vl  with
        | KDead => (* want to write an arbitrary value - this is bad - let's stop *)
            fail
        | KPrim => OK (d,KNode n, false) (* This is not an alias *)
        | KNode n' => let* f := G.depth (Pto d) in
                      let* _ := G.check_must_alias  f n l n' (Pto d) in
                      (* We have a must alias *)
                      OK (d,KNode n,true)
        end
    end.

Definition array_set (env:aenv) (d:domain) (a:atom) (i:atom) (vl:atom)  : res (domain * KVar) :=
  let* (r,_) := write env d a (cons (EdgeLabel.Index i) nil) vl in
  OK r.


Definition record_set (env:aenv) (d:domain) (a:atom) (fd:ident) (vl:atom) : res (domain * KVar) :=
  let* (r,_) := write env d a (cons (EdgeLabel.Field fd) nil) vl  in
  OK r.





Definition compat_typ (d:domain) (k:KVar) (ty:typ) :=
  match k with
  | KDead   => OK false (* We have no idea of the type - we could keep it *)
  | KPrim   => OK (typ_is_prim ty)
  | KNode n => let* ty' := G.get_label (Pto d) n in
               OK (if typ_eq_dec ty ty' then true else false)
  end.



Fixpoint bind_args (te:tenv) (env:aenv) (d:domain) (args: list atom) (params : list (ident * btyp)) :=
  match args with
  | nil => match params with
           | nil => OK nil
           |  _  => fail
           end
  | a1::args1 => match params with
                | nil => fail
                | (i1,bt1)::params1 =>
                    let* ty := btyp_to_typ te bt1 in
                    let k := eval_atom env (Vars d) a1  in
                    let* b := compat_typ d k ty in
                    let* bargs := bind_args te env d args1 params1 in
                    if b
                    then OK ((i1,k)::bargs)
                    else fail
                 end
  end.

Definition no_alias_node (d:domain) (n:int) (arg:ident * KVar) :=
  match snd arg with
  | KDead => OK false
  | KPrim => OK true
  | KNode n' => let* p := G.is_parent (Pto d) n n' in
                if p then OK false else G.is_parent (Pto d) n' n
  end.

Fixpoint forall_err {A: Type} (P : A -> res bool) (l:list A) : res bool :=
  match l with
  | nil => OK true
  | e::l => let* b := P e in
            let* b1 := forall_err P l in
            OK (b && b1)
  end.



Fixpoint no_alias (d:domain) (l : list (ident * KVar)) :=
  match l with
  | nil => OK true
  | (id1,v1)::l => match v1 with
                   | KDead => OK false
                   | KPrim => no_alias d l
                   | KNode n => let* b := no_alias d l in
                                if b then forall_err (no_alias_node d n) l
                                else OK false
                   end
  end.

Definition get_function (env:aenv) (vars: STree.t KVar) (id:ident) :=
  match STree.get id vars with
  | Some _ => fail
  | None   => match STree.get id env with
              | None => fail
              | Some ad => match ad with
                           | AFun af => OK af
                           |  _      => fail
                           end
              end
  end.

Definition call (te:tenv) (env: aenv) (d:domain) (a:atom) (args:list atom) : res (domain* KVar) :=
  match a with
  | AVar id bt =>
      match get_function env (Vars d) id with
      | OK af =>
          let fret := fn_body af in
          match bind_args te env d args (fn_params af) with
          | OK params =>
              match no_alias  d params with
              | OK no_alias =>
                  if no_alias
                  then (* Apply the function summary *)
                    match fret with
                    | RPrim => OK (d,KPrim)
                    | RDeep n acc =>
                        match List.nth_error args n with
                        | None => fail
                        | Some a =>
                            deep_access env d a acc
                        end
                    | RAny => OK(d,KDead)
                    end
                  else fail
              | Error _ => Error (MSG "function " :: MSG id :: MSG "arguments may be aliased" :: nil)
              end
          | Error _ =>
              Error (MSG "function " :: MSG id :: MSG "mismatch arguments" :: nil)
          end
      | Error _ => Error (MSG "function " :: MSG id :: MSG "Not_found" :: nil)
  end
  | _ => Error (MSG "call is not a function identifier" :: nil)
  end.



Definition eval_comp (te:tenv) (env : aenv) (d:domain) (c:comp)  : res (domain * KVar) :=
  match c with
  | CpAtom a _ => OK (d, eval_atom env (Vars d) a )
  | CpArrayGet a i _ _   => array_get env d a i
  | CpArraySet a i vl _ => array_set env d a i vl
  | CpRecordProj a fd _ _ =>  record_get env d a fd
  | CpRecordUpdate a fd vl _ => record_set env d a fd vl
  | CpDeepAccess a acc _   => deep_access env d a (List.map edge_of_access acc)
  | CpCall a args _  => call te env d a args
  end.

Definition inter_pto (g1 g2: G.t) : res (G.t * (IntMap.t int *  IntMap.t int)) :=
  let* lb1 := G.get_label g1 (G.root g1)  in
  let* lb2 := G.get_label g2 (G.root g2) in
  if typ_eq_dec lb1 lb2 then
    G.inter (TypOrdered.depth lb1) (G.root g1) g1 (G.root g2) g2 (G.mkroot lb1,(IntMap.empty _,IntMap.empty _))
  else fail.



Definition merge_var (m1: IntMap.t int) (m2:IntMap.t int) (k1 k2:KVar)  :=
  match k1 , k2 with
  | KDead , _ | _ , KDead => KDead
  | KPrim , KPrim => KPrim
  | KPrim , _| _ , KPrim =>  KDead (* Should not happen. *)
  | KNode n1 , KNode n2 => match IntMap.find n1 m1 , IntMap.find n2 m2 with
                           | Some n1' , Some n2' => if Int.eq_dec n1' n2'
                                                    then KNode n1'
                                                    else  KDead
                           |  _       ,  _        => KDead
                           end
  end.

Definition merge_ovar (m1 m2:IntMap.t int) (k1 k2 : option KVar) :=
  match k1 , k2 with
  | None , None => None
  | None , _ | _ , None => None
  | Some k1, Some k2 => Some (merge_var m1 m2 k1 k2)
  end.


Definition merge_vars (m1 m2: IntMap.t int) (v1 v2 : STree.t KVar) :=
  STree.combine  (merge_ovar m1 m2) v1 v2.

Definition merge_atoms (m1 m2:SMap.t (list atom)) :=
  PMap.combine (ListSet.set_inter Syntax.AtomOrdered.eq_dec) m1 m2.

Definition merge_domain (d1 d2:domain) : res domain :=
  let (v1,pt1,at1) := d1 in
  let (v2,pt2,at2) := d2 in
  let* (pto,m) := inter_pto pt1 pt2 in
  let v := merge_vars (fst m) (snd m) v1 v2 in
  let atm := merge_atoms at1 at2 in
  OK (mkdom v pto atm).

Definition merge (v1 v2 : domain + list EdgeLabel.edge) :=
  match v1 , v2 with
  | inl d1 , inl d2 => let* d := merge_domain d1 d2 in
                       OK (inl d)
  | inr sf1 , inr sf2 => if List.list_eq_dec EdgeLabel.eq_dec sf1 sf2
                         then OK (inr sf1)
                         else fail
  | _ , _ => fail
  end.

Fixpoint merge_list_rec (acc : domain + list EdgeLabel.edge) (l:list (res (domain + list EdgeLabel.edge))) : res (domain + list EdgeLabel.edge) :=
  match l with
  | nil => OK acc
  | e::l => let* e := e in
            let* m := merge e acc in
            merge_list_rec m l
  end.

Definition merge_list (l: list (res (domain + list EdgeLabel.edge))) : res (domain + list EdgeLabel.edge) :=
  match l with
  | nil => fail
  | acc :: l => let* acc := acc in
                merge_list_rec acc l
  end.


Definition update_variable (v:ident) (d:domain) (kv:KVar) :=
  set_variable v kv (forget_var v d).

Fixpoint eval_statement (te:tenv) (env: aenv) (s:statement) (d:domain) : res (domain + list EdgeLabel.edge) :=
  match s with
  | StSet v c => match eval_comp te env d c  with
                 | OK (d,k) =>  OK (inl (update_variable v d k))
                 | Error m  => Error (MSG "In statement " ::
                                        MSG (Draw.pp (Pp.pp_statement s)) ::
                                        MSG " " :: m)
                 end
  | StIfThenElse a s1 s2 =>
      (* I don't care about the conditional *)
      let* d1 := eval_statement te env s1 d in
      let* d2 := eval_statement te env s2 d in
      merge d1 d2
  | StSwitch a l => let ld := List.map (fun x => eval_statement te env (snd x) d) l in
                    merge_list ld
  | StSequence s1 s2 => let* d1 := eval_statement te env s1 d in
                        match d1 with
                        | inr _ => Error (MSG "sequence is not well-typed" :: nil)
                        | inl d2 => eval_statement te env s2 d2
                        end
  | StReturn a => match eval_atom env (Vars d) a  with
                  | KDead => Error (MSG "return of a dead expression" :: nil)
                  | KPrim => OK(inr nil)
                  | KNode n =>
                      let* p := G.get_path (Pto d) n in
                      OK (inr p)
                  end
  end.

Fixpoint assigned (s:statement) : SSet.t :=
  match s with
  | StSet id _ => SSet.add id  SSet.empty
  | StIfThenElse _ s1 s2 => SSet.union (assigned s1) (assigned s2)
  | StSwitch _ l => List.fold_right (fun e acc => SSet.union (assigned (snd e)) acc) SSet.empty l
  | StSequence s1 s2 => SSet.union (assigned s1) (assigned s2)
  | StReturn _ => SSet.empty
  end.

Definition bind_param (v: STree.t KVar) (g:G.t) (p:ident * typ)  :=
  if typ_is_prim (snd p)
  then OK (STree.set (fst p) KPrim v , g)
  else (* add a path in the graph *)
    let* (g1,n) := G.create_path EdgeLabel.next_label (G.root g) (EdgeLabel.Field (fst p) :: nil) g in
    let (n,ty) := n in
    if typ_eq_dec ty (snd p)
    then  OK (STree.set (fst p) (KNode n) v,g1)
    else fail (* Cannot happen *).

Fixpoint bind_params (v:STree.t KVar) (g:G.t) (l :list (ident * typ)) :=
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
  bind_params (STree.empty) g l.


Fixpoint find_index {A: Type} (i:ident) (params : smaplist A) :=
  match params with
  | nil => fail
  | (i',_)::params' => if Ident.eq_dec i i' then OK O
                       else
                         let* j := find_index i params' in
                         OK (S j)
  end.

Definition sfunction_of_path (params:smaplist btyp) (l:list EdgeLabel.t) :=
  match l with
  | nil => OK RPrim
  | EdgeLabel.Field p :: l =>
      let* i := find_index p params in
      OK (RDeep i l)
  | _ => fail
  end.

Definition domain_of_function (te:tenv)(f:function) : res domain :=
  let* params := MapList.map_err (btyp_to_typ te) (fn_params f) in
  if MapList.nodup  Ident.eq_dec params
  then let modified := assigned (fn_body f) in
       if List.forallb (fun i_t => negb (SSet.mem (fst i_t) modified)) params
       then let* (v,pto) := init_domain params in
            OK (mkdom v pto (SMap.init nil))
       else fail
  else fail.


Definition eval_function (te:tenv) (env:aenv) (f:function) : res afunction :=
  let* d := domain_of_function te f in
  let* d := eval_statement te env (fn_body f) d in
  match d with
  | inr r =>
      let* r := sfunction_of_path (fn_params f) r in
      OK (mk_function (fn_return f) (fn_params f) r)
  |  _    => fail
  end.


Definition literal_is_primitive (l:literal) :=
  match l with
  | LTrue | LFalse | LInt32 _ _ | LInt64 _ _ => true
  | _ => false
  end.

Fixpoint get_write_arg (l:list (param_attr * btyp)) : res nat :=
  match l with
  | nil => fail
  | (attr,_) ::l =>
      match attr with
      | AttrWrite    => OK O
      | _ => let* i := get_write_arg l in
             OK (S i)
      end
  end.

Definition get_return (te:tenv)(l:list (param_attr * btyp)) (r:btyp) : res sfunction :=
  let* ty := btyp_to_typ te r in
  if typ_is_prim ty then OK RPrim
  else let* i := get_write_arg l  in
       OK (RDeep i nil).

Fixpoint xmapi {A B:Type} (F: positive -> A -> B) (i:positive) (l:list A) : list B :=
  match l with
  | nil => nil
  | e::l => F i e :: xmapi F (Pos.succ i) l
  end.

Definition mapi {A B:Type} (F: positive -> A -> B) (l:list A) := xmapi F xH l.

Definition afunction_of_sfunction (l:list (param_attr * btyp)) (r:btyp) (s:sfunction):=
  mk_function r (mapi (fun i e => (string_of_positive i,snd e)) l) s.

Definition eval_globdef (te:tenv) (env:aenv) (gd:globdef) : res aenv :=
  match gd with
  | DefConst id l t => OK (STree.set id (ALit (literal_is_primitive l)) env)
  | DefFun id f     => match eval_function te env f with
                       | OK f => OK (STree.set id (AFun f) env)
                       | Error e => Error (MSG "PASS elim alias:" ::
                            MSG "cannot analyze function " ::
                            MSG id :: MSG "\n" :: e)
                       end
  | DeclConst id t  => let* ty := btyp_to_typ te t in
                       OK (STree.set id (ALit (typ_is_prim ty )) env)
  | DeclFun id params r => let* ret := get_return te params r in
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
      match write env d a (cons (EdgeLabel.Index i) nil) v  with
      | Error m => Error m
      | OK(_,b) =>
          OK (if b then CpAtom a bt
              else c)
      end
  | CpRecordUpdate a i v bt =>
      match write env d a (cons (EdgeLabel.Field i) nil) v  with
      | Error m =>  let err := Draw.pp (pp_domain d) in
                    Error (MSG err :: nil)
      | OK(_,b) => if b then OK (CpAtom a bt)
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
  | StSet id c => comp_has_update c
  | StIfThenElse a s1 s2 => statement_has_update s1 || statement_has_update s2
  | StSwitch a l =>
      List.existsb (fun x => statement_has_update (snd x)) l
  | StSequence s1 s2 =>
      statement_has_update s1 || statement_has_update s2
  | StReturn a => false
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
  | CpAtom a _ => atom_is_var id a
  | _ => false
  end.






Definition is_nop (s:statement) :=
  match s with
  | StSet id c => comp_is_var id c
  | _          => false
  end.

Definition mk_seq (s1 s2:statement) :=
  if is_nop s1 then s2
  else if is_nop s2 then
         s1
       else StSequence s1 s2.

Fixpoint has_nop (s:statement) :=
  match s with
  | StSequence s1 s2 => has_nop s1 || has_nop s2
  | StIfThenElse _ s1 s2 =>
      (if is_nop s1 then false else has_nop s1)
      ||
      (if is_nop s2 then false else has_nop s2)
  | StSwitch a l => List.existsb (fun x => has_nop (snd x)) l
  | StReturn _   => false
  | StSet id c   => is_nop s
  end.



Fixpoint transl_statement (te:tenv) (env: aenv) (d:domain) (s:statement) : res statement :=
  match s with
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
  end.




Definition transl_function (te:tenv) (env:aenv) (f:function) :=
  let* d := domain_of_function te f in
  let* s' := transl_statement te env d (fn_body f) in
  if has_nop s'
  then Error (msg (Draw.pp (Pp.pp_statement s')))
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

Definition transl_program (p: program) : res program :=
  let* te := tenv_of_type_defs (prog_types p) in
  let* gds :=  transl_globdefs te STree.empty (prog_defs p) in
  OK (mk_program gds (prog_types p) (prog_tabs p)).
