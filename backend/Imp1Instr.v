From Stdlib Require Import Bool List PArith Lia.
From BarocqComp Require Import Maps2 Utils DList Types Intop Syntax Benum Typing Imp1 Imp1Imp  Option.
Local Open Scope option_monad_scope.

(* Instrumented in-place semantics of Imp1 with invalid paths *)

(* A partial path is a list of cedges + a type *)

Definition ppath : Type := (list cedge) * typ.

Definition ppath_edges (pp: ppath) : list cedge :=
  fst pp.

Definition ppath_typ (pp: ppath) : typ :=
  snd pp.

Definition ppath_prefix_with (pre: list cedge) (pp: ppath) : ppath :=
  (pre ++ (ppath_edges pp), ppath_typ pp).

Definition ppath_prefixed_with (pre: list cedge) (pp: ppath) : bool :=
  let fix aux pre edges :=
    match pre, edges with
    | nil, _ => true
    | x1 :: pre', x2 :: edges' =>
        if cedge_eqb x1 x2 then aux pre' edges'
        else false
    | _, _ => false
    end
  in
  aux pre (ppath_edges pp).
  
Module PPathSet.

  Parameter t : Type.

  Parameter top : t.

  Parameter singleton : ppath -> t.

  Parameter add : ppath -> t -> t.

  Parameter mem : ppath -> t -> bool.

  Parameter union : t -> t -> t.

  Parameter fold : forall {A: Type},  (A -> ppath -> A) -> t -> A -> A.

  Definition union_opt (pps1 pps2: option t) : option t :=
    match pps1, pps2 with
    | Some pps1, Some pps2 => Some (union pps1 pps2)
    | Some pps, _
    | _, Some pps => Some pps
    | None, None => None
    end.

  Parameter prefixed_with : list cedge -> t -> t.

  Parameter prefix_with : list cedge -> t -> t.

  Parameter filter : (ppath -> bool) -> t -> t. 

  Axiom prefixed_with_SPEC :
    forall pp pre s,
      mem pp (prefixed_with pre s) = true <->
      PPathSet.mem (ppath_prefix_with pre pp) s = true.
      
End PPathSet.

Parameter path : Type.

Parameter mk_path : ident -> ppath -> path.

Parameter path_typ : path -> typ.

Parameter path_pp : path -> ppath.

Parameter path_var : path -> ident.

Module InvSet.

  Parameter t : Type.

  Parameter empty : t.

  Parameter mem : path -> t -> bool.

  Parameter get : ident -> t -> option PPathSet.t.

  Parameter add : path -> t -> t.

  Parameter add_ppset : ident -> PPathSet.t -> t -> t.

  Parameter singleton_ppset : ident -> PPathSet.t -> t.

  Parameter suffix_with : list cedge -> typ -> t -> t.

  Parameter union : t -> t -> t.

  Definition valid_var (x: ident) (inv: t) : bool :=
    match get x inv with
    | Some _ => false
    | None => true
    end.

  Axiom get_mem_None :
    forall x inv,  
      get x inv = None <->
      (forall pp, mem (mk_path x pp) inv = false).

End InvSet.

Section SEM.

  Variable abs : Maps.PMap.t Type.

  Variable abs_dec : forall x,
    forall (v1 v2: SMap.get x abs), {v1 = v2} + {v1 <> v2}.

  Local Notation mem := (Imp1Imp.mem abs).

  Local Notation mval := (Imp1Imp.mval abs).

  (* =============== Memory API =============== *)

  Definition load : forall {ty}, ptr ty -> mem -> option (mval ty) :=
    @Imp1Imp.get abs.

  Definition store : forall {ty}, ptr ty -> mval ty -> mem -> option mem :=
    @Imp1Imp.set abs.

  (** [paths_to_mval e m a] returns the map of all paths pointing
      to the memory value located at address [a]. *)
  Parameter paths_to_mval : env -> mem -> addr -> InvSet.t.

  Parameter follow_ppath : mem -> addr -> (forall (pp: ppath), option (val (ppath_typ pp))).

  Parameter follow_path : env -> mem -> ident -> (forall (pp: ppath), option (val (ppath_typ pp))).

  Parameter paths_aliased_with : env -> mem -> addr -> ppath -> InvSet.t.

  Parameter paths_aliased_below : env -> mem -> addr -> ppath -> InvSet.t.

  (* ====================================================== *)

  Fixpoint typ_of_fun (l:list typ) (r:typ) :=
    match l with
    | nil => unit -> option (val r * mem * list (option PPathSet.t))
    | tx::tparams' => val tx ->
                      match tparams' with
                      | nil => option (val r * mem * list (option PPathSet.t))
                      | _ :: _ => typ_of_fun tparams' r
                      end
    end.

  Definition Fun (tparams: list typ) (tret: typ) := mem -> typ_of_fun tparams tret.

  Inductive gval : Type :=
    | GFun (tparams: list typ) (tret: typ) (fct: Fun tparams tret)
    | GConst (ty: typ) (v: val ty).

  Definition typof_glob (g: gval) : typ :=
    match g with
    | GFun tparams tret _ => TFun tparams tret
    | GConst ty _ => ty
    end.

  Definition genv : Type := ident -> option gval.

  Definition get_gvar (ge: genv) (x: ident) (tx: typ) : option (val tx) :=
    let* g := ge x in
    match g with
    | GFun tparams tret _ => cast_val (mk_fptr x tparams tret) tx
    | GConst tv v => cast_val v tx
    end.

  Definition get_var (ge: genv) (e: env) (x: ident) (tx: typ) : option (val tx) :=
    match e x with
    | Some (existT _ _ v) => cast_val v tx
    | None => get_gvar ge x tx
    end.

  (** [inv_arg_aliases_after_call e m inv ty arg pps_arg] computes the set of invalid paths after a function call
      involving argument [arg]. [pps_arg] is the set of partial paths of [arg] that the callee invalidated. *)
  Definition inv_arg_aliases_after_call (e: env) (m: mem) (inv: InvSet.t) (ty: typ) (arg: val ty) (pps_arg: option PPathSet.t) : option InvSet.t :=
    match arg with
    | Vprim _ _ => ret inv
    | Vptr _ ptr =>
        let* a := addr_of_ptr ptr in
        match pps_arg with
        | Some pps =>
            let inv' :=
              PPathSet.fold
                (fun (acc: InvSet.t) (pp: ppath) =>
                  let ppw := paths_aliased_with e m a pp in
                  let ppb := paths_aliased_below e m a pp in
                  InvSet.union acc (InvSet.union ppw ppb))
                pps
                inv
            in
            ret inv'
        | None => ret inv
        end
    end.

  Fixpoint inv_after_call (e: env) (m: mem) (inv: InvSet.t) (tparams: list typ) (tret: typ)
                          (args: DList.dlist val tparams)
                          (pps_args: list (option PPathSet.t))
                          : option InvSet.t :=
    match args, pps_args with
    | DNIL _, nil => ret inv
    | @DCONS _ _ ta a tparams' args', pps_a :: pps_args' =>
        let* inv' := inv_arg_aliases_after_call e m inv ta a pps_a in
        inv_after_call e m inv' tparams' tret args' pps_args'
    | _, _ => fail
    end.


  Fixpoint eval_call (tparams : list typ) (tret : typ)
      (args : DList.dlist val tparams) (f: typ_of_fun tparams tret)
      {struct args} : option (val tret * mem * list (option PPathSet.t)).
  Proof.
    destruct args as [| ta a tparams args]; simpl in f.
    - apply (f tt).
    - specialize (f a).
      destruct tparams.
      + apply f.
      + apply (eval_call _ _ args f).
  Defined.

  Definition cast_function {t1 t2: list typ} {tr1 tr2: typ} (EQ: TFun t1 tr1 = TFun t2 tr2) (f : Fun t1 tr1)
      : Fun t2 tr2.
  Proof.
    inversion EQ. rewrite H0, H1 in f. apply f.
  Defined.

  Lemma cast_function_id:
    forall tparams tret (f: Fun tparams tret), cast_function eq_refl f = f.
  Proof.
    intros. unfold cast_function.
    simpl. reflexivity.
  Qed.

  Definition ieval_call (ge: genv) (e: env) (m: mem) (fid: ident)  
      (tparams: list typ) (tret: typ) (args: DList.dlist val tparams)
      (ty: typ) : option (val tret * mem * InvSet.t) :=
    match ge fid with
    | Some (GFun tparams' tret' f) =>
        match typ_eq_dec (TFun tparams' tret') (TFun tparams tret) with
        | left EQ =>
            let f := cast_function EQ f in
            let* (vr, mr, pps_args) := eval_call tparams tret args (f m) in
            let* invr := inv_after_call e m InvSet.empty tparams tret args pps_args in
            ret (vr, mr, invr)
          | _ => fail
          end
    | _ => fail
    end.

  Definition inv_get_field (pps: option PPathSet.t) (ce: cedge) : option PPathSet.t :=
    match pps with
    | None => None
    | Some pps => Some (PPathSet.prefixed_with (ce :: nil) pps)
    end.

  Definition ieval_prim {tv: typ} (pv: pval tv) (ty: typ) : option (val ty * option PPathSet.t) :=
    let* v := cast_pval pv ty in
    ret (Vprim ty v, None).

  Section CALL_ARGS.

    Variable ieval_atom : tenv -> genv -> env -> mem -> InvSet.t -> forall (ty: typ), atom -> option (val ty * option PPathSet.t).

    Definition ieval_args (te: tenv) (ge: genv) (e: env) (m: mem) (inv: InvSet.t)
        (targs: list typ) (args: list atom)
        : option (DList.dlist val targs) :=
      DList.mmap _
        (fun t a =>
          let* (va, pps_a) := ieval_atom te ge e m inv t a in
          match pps_a with
          | None => ret va
          | _ => fail (* invalid argument *)
          end)
        args targs.

  End CALL_ARGS.

  Fixpoint ieval_atom (te: tenv) (ge: genv) (e: env) (m: mem) (inv: InvSet.t) (ty: typ) (a: atom) : option (val ty * option PPathSet.t) :=
    match a with
    | ATrue => ieval_prim (PBool true) ty
    | AFalse => ieval_prim (PBool false) ty
    | AInt32 i s => ieval_prim (PInt32 s i) ty
    | AInt64 i s => ieval_prim (PInt64 s i) ty
    | AConstr c _ _ =>
        match ty with
        | TEnum eid elems =>
            let* e := make_enum elems c in
            ieval_prim (PEnum eid elems e) ty
        | _ => fail
        end
    | AVar x _ =>
        let* vx := get_var ge e x ty in
        ret (vx, InvSet.get x inv)
    | ACast a1 bt =>
        let* t := btyp_to_typ te bt in
        let* t1 := typof_atom te a1 in
        let* (v1, pps1) := ieval_atom te ge e m inv t1 a1 in
        let* v1 := eval_val abs v1 in     
        let* fcast := Denot.get_cast abs t1 t in
        let* v1' := fcast v1 in
        let* pvr := pval_of_typ abs _ v1' in
        let* vr := cast_val (Vprim t pvr) ty in
        ret (vr, pps1)
    | AUnaryOp op a1 _ =>
        let* t1 := typof_atom te a1 in
        let* (v1, pps1) := ieval_atom te ge e m inv t1 a1 in
        let* v1 := eval_val abs v1 in
        let* vr := Denot.eval_unary_op abs op t1 v1 ty in
        let* vr := val_of_eval_typ abs vr in
        ret (vr, pps1)
    | ABinaryOp op a1 a2 _ =>
        let* t1 := typof_atom te a1 in
        let* t2 := typof_atom te a2 in
        let* (v1, pps1) := ieval_atom te ge e m inv t1 a1 in
        let* (v2, pps2) := ieval_atom te ge e m inv t2 a2 in
        let* v1 := eval_val abs v1 in
        let* v2 := eval_val abs v2 in
        let* vr := Denot.eval_binary_op abs op t1 t2 v1 v2 ty in
        let* vr := val_of_eval_typ abs vr in
        ret (vr, PPathSet.union_opt pps1 pps2)
    | AArrayGet a1 i _ _ =>
        let* t1 := typof_atom te a1 in
        let* (v1, pps1) := ieval_atom te ge e m inv t1 a1 in
        let* ti := typof_atom te i in
        let* (vi, ppsi) := ieval_atom te ge e m inv ti i in
        let* ci := index_of_val vi in
        let* vr := eval_mem_access abs m v1 (CIndex ci) ty in
        let ppsr :=
          match ppsi with
          | Some _ => Some PPathSet.top
          | None => inv_get_field pps1 (CIndex ci)
          end
        in
        ret (vr, ppsr)
    | ARecordProj a1 fd _ _ =>
        let* t1 := typof_atom te a1 in
        let* (v1, pps1) := ieval_atom te ge e m inv t1 a1 in
        let* vr := eval_mem_access abs m v1 (CField fd) ty in
        ret (vr, inv_get_field pps1 (CField fd))
    | APureCall f btf args _ =>
        let* tf := btyp_to_typ te btf in
        if InvSet.valid_var f inv then
          let* vf := get_var ge e f tf in
          match vf with
          | Vptr _ (PtrF fid tparams tret) =>
              (* let* vargs := DList.mmap _ (fun t a => ieval_atom te ge e m inv t a) args tparams in *)
              let* vargs := ieval_args ieval_atom te ge e m inv tparams args in
              let* (vr, _, _) := ieval_call ge e m fid tparams tret vargs ty in
              (* Pure calls do not modify the memory nor invalidate their arguments,
                so we can "safely" ignore the new memory and new set of invalid paths. *)
              let* vr := cast_val vr ty in
              ret (vr, None)
          | _ => fail
          end
        else fail
    end.

  (** [inv_aliases te ge e m a i t] returns the set of all paths directly aliased to the
      memory value [v], suffixed by [i].*)
  Definition inv_aliases (e: env) (m: mem) {tv: typ} (v: val tv) (ce: cedge) (ty: typ) : option InvSet.t :=
    match v with
    | Vptr t ptr =>
        let* addr := addr_of_ptr ptr in
        let paths_to_a := paths_to_mval e m addr in 
        ret (InvSet.suffix_with (ce :: nil) ty paths_to_a)
    | _ => fail
    end.

  Definition eval_array_set (m: mem) {ta: typ} (a: val ta) (i: usize) {tv: typ} (v: val tv) : option mem :=
    let* p := isptr a in
    let* a := load p m in
    match a with
    | MArray _ ta' l =>
        let* v := cast_val v ta' in
        let* l' := Barray.set l i v in
        let* mv := cast_mval abs (MArray _ ta' l') ta in
        store p mv m
    | _ => fail
    end.

  (** [inv_set_field te ge e m inv a ce v ty] adds to [inv] the set of invalid paths resulting from
      updating the 'field' [ce] of [a] with [v], and returns the set of invalid partial paths
      that the variable assigned to this computation inherits from.*)
  (* TODO: check for no-op assignment *)
  Definition ieval_set_field (te: tenv) (ge: genv) (e: env) (m: mem) (inv: InvSet.t)
      (a: atom) (ce: cedge) (v: atom) (ty: typ) : option (val ty * mem * option PPathSet.t * InvSet.t) :=
    let* ta := typof_atom te a in
    let* (va, ppsa) := ieval_atom te ge e m inv ta a in
    let* tv := typof_atom te v in
    let* (vv, ppsv) := ieval_atom te ge e m inv tv v in
    let* m' :=
      match ce with
      | CField fd => eval_record_update abs m va fd vv
      | CIndex i => eval_array_set m va i vv
      end
    in
    let pps_ce :=
      match ppsv with
      | Some pps => Some (PPathSet.prefix_with (ce :: nil) pps)
      | None => None
      end
    in
    let pps_ce' :=
      match ppsa with
      | Some pps => Some (PPathSet.filter (fun pp => negb (ppath_prefixed_with (ce :: nil) pp)) pps)
      | None => None
      end
    in
    let ppsr := PPathSet.union_opt pps_ce pps_ce' in
    let* inv_a_i := inv_aliases e m vv ce tv in
    let inv' := InvSet.union inv inv_a_i in
    let* va := cast_val va ty in
    ret (va, m', ppsr, inv').

  Definition ieval_comp (te: tenv) (ge: genv) (e: env) (m: mem) (inv: InvSet.t) (c: comp) (ty: typ) : option (val ty * mem * option PPathSet.t * InvSet.t) :=
    match c with
    | CpAtom a =>
        let* (va, ppsa) := ieval_atom te ge e m inv ty a in
        ret (va, m, ppsa, inv)
    | CpRecordUpdate r fd v _ =>
        ieval_set_field te ge e m inv r (CField fd) v ty
    | CpArraySet a i v _ =>
        let* ti := typof_atom te i in
        let* (vi, ppsi) := ieval_atom te ge e m inv ti i in
        match ppsi with
        | Some _ => fail
        | None =>
            let* i := index_of_val vi in
            ieval_set_field te ge e m inv a (CIndex i) v ty
        end
    | CpCall f btf args _ =>
        let* tf := btyp_to_typ te btf in
        if InvSet.valid_var f inv then
          let* vf := get_var ge e f tf in
          match vf with
          | Vptr _ (PtrF fid tparams tret) =>
              let* vargs := ieval_args ieval_atom te ge e m inv tparams args in
              let* (vr, mr, invr) := ieval_call ge e m fid tparams tret vargs ty in
              let* vr := cast_val vr ty in
              ret (vr, mr, None, InvSet.union inv invr)
          | _ => fail
          end
        else fail
    end.

  Definition typ_of_statement (ty: option typ) : Type :=
    match ty with
    | Some t => val t * option PPathSet.t
    | None => env
    end.

  Definition ieval_match (tv:typ) (v: val tv) (ty: option typ) (cases: list (pattern * (option (typ_of_statement ty * mem * InvSet.t)))) :
    option (typ_of_statement ty * mem * InvSet.t) :=
    match v with
    | Vptr _ _ => fail
    | Vprim _ e => match e with
                   | PEnum id l en => match_with_err en cases
                   |  _  => fail
                   end
    end.

  Fixpoint ieval_statement (te: tenv) (ge: genv) (e: env) (m: mem) (inv: InvSet.t) (ty: option typ) (s: Imp1.statement) : option (typ_of_statement ty * mem * InvSet.t) :=
    match s with
    | StSkip    => match ty with
                   | Some _ => fail
                   | None   => Some (e,m,inv)
                   end
    | StSet x c =>
        match ty with
        | Some _ => fail
        | None =>
            let* tc := typof_comp te c in
            let* (v, m', pps, inv') := ieval_comp te ge e m inv c tc in
            let inv' :=
              match pps with
              | Some pps => InvSet.add_ppset x pps inv'
              | _ => inv'
              end
            in
            ret (env_set x v e, m', inv')
        end
    | StIfThenElse a s1 s2 =>
        let* (va, ppsa) := ieval_atom te ge e m inv TBool a in
        match ppsa with
        | None =>
            ieval_statement te ge e m inv ty (if bool_of_valbool va then s1 else s2)
        | _ => fail
        end
    | StSwitch a cases =>
        let* ta := typof_atom te a in
        let* (va, ppsa) := ieval_atom te ge e m inv ta a in
        match ppsa with
        | None =>
            let vcases := MapList.map (ieval_statement te ge e m inv ty) cases in
            ieval_match ta va ty vcases
        | _ => fail
        end
    | StSequence s1 s2 =>
        let* (e1, m1, inv1) := ieval_statement te ge e m inv None s1 in
        ieval_statement te ge e1 m1 inv1 ty s2
    | StReturn a =>
        match ty with
        | Some tyr =>
            let* ta := typof_atom te a in
            let* (va, ppsa) := ieval_atom te ge e m inv ta a in
            let* va := cast_val va tyr in
            ret ((va, ppsa), m, inv)
        | _ => fail
        end
    | StAttr _ s1 => ieval_statement te ge e m inv ty s1
    end.

  Definition params_inv (params: smaplist typ) (inv: InvSet.t) : list (option PPathSet.t) :=
    MapList.fold_right (fun pid _ acc => (InvSet.get pid inv) :: acc) nil params.

  Fixpoint ieval_fun_rec (te: tenv) (ge: genv) (e: env) (params_all params_rec: smaplist typ) (tret: typ) (s: statement)
      : Fun (List.map snd params_rec) tret.
  Proof.
    unfold Fun in *; destruct params_rec.
    - simpl.
      apply
        (fun m _ =>
          let* (v, ppsv, m', inv) := ieval_statement te ge e m InvSet.empty (Some tret) s in
          match ppsv with
          | None => ret (v, m', params_inv params_all inv)
          | _ => fail
          end).
    - simpl. intros m v.
      specialize (ieval_fun_rec te ge (env_set (fst p) v e) params_all params_rec tret s m).
      destruct params_rec; simpl.
      * apply (ieval_fun_rec tt).
      * apply ieval_fun_rec.
  Defined.

  Definition ieval_fun (te: tenv) (ge: genv) (params: smaplist typ) (tret: typ) (s: statement)
      : Fun (List.map snd params) tret :=
    ieval_fun_rec te ge (env_empty) params params tret s.

  Definition genv_update (ge: genv) (x: ident) (g: gval) : option genv :=
    match ge x with
    | None =>
        ret (fun y =>
              if Ident.eq_dec y x then ret g else
              ge y)
    | _ => fail
    end.

  Definition eval_def_fun (te: tenv) (ge: genv) (x: ident) (f: function) : option genv :=
    let '(tret, params) := (fn_return f, fn_params f) in
    if MapList.nodup Ident.eq_dec params then
      let* tret := btyp_to_typ te tret in
      let* params := Denot.map_err (btyp_to_typ te) params in
      let g := GFun (List.map snd params) tret (ieval_fun te ge params tret (fn_body f)) in
      genv_update ge x g
    else fail.

  Definition eval_def_const (te: tenv) (ge: genv) (m: mem) (x: ident) (l: literal) (bt: btyp) : option (genv * mem) :=
    let* t := btyp_to_typ te bt in
    let* (vl, m') := eval_literal abs te l m in
    let* vl := ecast_val (Some vl) t in
    let* ge' := genv_update ge x (GConst t vl) in
    ret (ge', m').

  Definition eval_decl_const (te: tenv) (impl ge: genv) (x: ident) (bt: btyp) : option genv :=
    let* t := btyp_to_typ te bt in
    let* g := impl x in
    if typ_eq_dec t (typof_glob g) then
      genv_update ge x g
    else fail.

  Definition eval_decl_fun (te: tenv) (impl ge: genv) (x: ident) (params: list (Syntax.param_attr * btyp)) (tret: btyp) : option genv :=
    let* tparams := mmap (btyp_to_typ te) (List.map snd params) in
    let* tret := btyp_to_typ te tret in
    let* g := impl x in
    if typ_eq_dec (TFun tparams tret) (typof_glob g) then
      genv_update ge x g
    else fail.

  Definition eval_globdef (te: tenv) (impl ge: genv) (m: mem) (def: globdef) : option (genv * mem) :=
    match def with
    | DefConst x l ty => eval_def_const te ge m x l ty
    | DefFun x f =>
        let* ge' := eval_def_fun te ge x f in
        ret (ge', m)
    | DeclConst y bt =>
        let* ge' := eval_decl_const te impl ge y bt in
        ret (ge', m)
    | DeclFun y params tret =>
        let* ge' := eval_decl_fun te impl ge y params tret in
        ret (ge', m)
    end.

  Definition eval_prog (impl: genv) (m: mem) (prog: program) : option (tenv * genv * mem) :=
    let* te := tenv_of_type_defs (prog_types prog) in
    let* (ge', m') :=
      fold_left_err
        (fun '(acc_ge, acc_m) d => eval_globdef te impl acc_ge acc_m d)
        (prog_defs prog)
        (fun _ => fail, m)
    in
    ret (te, ge', m').

End SEM.
