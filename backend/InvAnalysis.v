(** Invalid Path for imp1 *)
Require Import Uint63.
Require Import String FMapInterface FMapList ZArith Int ListSet.
From BarocqComp Require Import Error Maps2 Types Syntax Imp1 Graph Typing Utils Pp Printer.
From BarocqComp Require Import Imp1ElimAlias.
From Coq Require Import FMapPositive.

(** The analysis requires an alias analysis.
    We have the [Imp1ElimAlias] and this is hardcoded.
    The analysis makes sure that all the function are purely functional.
 *)

Import G.PathTree.

Module InvMap.

  Definition t := STree.t G.PathTree.t.

  Definition is_field (fd : EdgeLabel.t) : bool :=
    match fd with
    | EdgeLabel.Field _ => true
    | _                 => false
    end.

  Fixpoint check_tree (tr:G.PathTree.t) :=
    match tr with
    | Node l =>
        match l with
        | nil => true
        | (fd,_)::_ =>  if is_field fd
                        then List.forallb (fun '(fd',r) => is_field fd' && check_tree r) l
                        else List.forallb (fun '(fd',r) => negb (is_field fd') && check_tree r) l
        end
    end.

  Definition ocheck (o: option G.PathTree.t) :=
    match o with
    | None => true
    | Some p => check_tree p
    end.



  Definition check (m:t):=
    STree.fold (fun acc _ v => acc && check_tree v) m true.

  Definition pp (m:t) := STree.pp (Bstr ":") G.PathTree.pp m.

  Definition merge (o1 o2: option G.PathTree.t) : option G.PathTree.t :=
    match o1 , o2 with
    | None , x | x , None => x
    | Some v1 , Some v2   => Some (G.PathTree.union v1 v2)
    end.

  Definition join (e1 e2:t) := STree.combine merge e1 e2.

  Definition of_path (x:string) (l :list EdgeLabel.t) :=
    STree.set x (G.PathTree.create l) STree.empty.

  Definition singleton (x:string) (p: G.PathTree.t) : t :=
    STree.set x p STree.empty.

  Definition set (x:string) (v: option G.PathTree.t) (m:t) : t :=
    match v with
    | None => STree.remove x m
    | Some v => STree.set x v m
    end.

  Definition empty : t := STree.empty.

End InvMap.

Module Afunction.

  Record t :=
    mk
      {
        fn_areturn  :  (btyp * option G.PathTree.t);
        fn_aparams : list (btyp * option G.PathTree.t);
      }.

  Definition pp_elt (x:btyp * option G.PathTree.t) :=
    pp_option G.PathTree.pp (snd x).

  Definition pp (f:t) :=
    Bcat
      (pp_list (Bstr "->") pp_elt (fn_aparams f))
      (Bcat (Bstr "->") (pp_elt (fn_areturn f))).

End Afunction.

Definition genv := STree.t Afunction.t.

Definition pp_inv := STree.pp (Bstr " : ") Afunction.pp.

Definition of_alias (fd:EdgeLabel.t) (p : option (list EdgeLabel.t))  : G.PathTree.t :=
  match p with
  | None => Node nil
  | Some l => G.PathTree.create (fd::l)
  end.


Definition inv_may_alias (env:InvMap.t) (paths : STree.t (list EdgeLabel.t)) (fd:EdgeLabel.t) :=
  InvMap.join env (STree.map (fun _ l => G.PathTree.create (List.rev (fd::l))) paths).


Fixpoint find_may_edge {A: Type} (e:EdgeLabel.t) (l:list (EdgeLabel.t * A)) : option A :=
  match l with
  | nil => None
  | (e1,v1) ::l1 => if may_edge e e1 then Some v1 else find_may_edge e l1
  end.

Definition get_field (p:option G.PathTree.t) (fd: EdgeLabel.t) : option G.PathTree.t :=
  match p with
  | None => None (* Every path is valid *)
  | Some p => match p with
              | Node nil => Some (Node nil) (* Every path is invalid *)
              | Node l   =>  find_may_edge fd l
              end
  end.

Fixpoint eval_atom (env:InvMap.t) (a:atom) : option G.PathTree.t :=
  match a with
  | ATrue | AFalse | AInt32 _ _ | AInt64 _ _ | AConstr _ _ _ => None
  | AVar i _ => STree.get i env
  | ACast a1 _ | AUnaryOp _ a1 _ => eval_atom env a1
  | ABinaryOp _ a1 a2 _ =>
      match eval_atom env a1, eval_atom env a2 with
      | Some pt1, Some pt2 => Some (G.PathTree.union pt1 pt2)
      | Some pt, _  | _, Some pt => Some pt
      | _, _ => None
      end
  | AArrayGet a i _ _  =>  get_field (eval_atom env a) (EdgeLabel.Index i)
  | ARecordProj a id _ _ => get_field (eval_atom env a) (EdgeLabel.Field id)
  | APureCall _ _ _ _ => None
  end.

Definition set_path (p:option G.PathTree.t) (fd:EdgeLabel.t) (v: option G.PathTree.t) : option G.PathTree.t :=
  match p with
  | None => match v with
            | None => None (* Totally defined *)
            | Some v => Some (Node ((fd,v)::nil))
            end
  | Some p => G.PathTree.set_path p fd v
end.

Definition check (str: string) (e1:InvMap.t) (e2:InvMap.t) : res (unit:Type):=
  if InvMap.check e2
  then OK tt
  else
    let b1 := Bframe "-" "|" (InvMap.pp e1) in
    let b2 := Bframe "-" "|" (InvMap.pp e2) in
    let err := Pp.seq ((Bstr str :: Bstr " before " :: b1 :: Bstr " after " :: b2 :: nil)) in
    Error (MSG nl :: (msg (Pp.pp err))).


Definition show_path_above_alias (te:tenv) (ge:aenv) (d:domain) (env:InvMap.t) (a1:atom) (env': InvMap.t): res unit :=
  let pd := pp_domain d in
  let pe := InvMap.pp env in
  let a  := pp_atom a1 in
  let* res := path_above_alias te ge d a1 in
  let args := Pp.seq (Bstr "path_above_alias:" :: Bstr "alias domain" :: Bframe "-" "|" pd :: Bstr "invalid" :: Bframe "-" "|" pe :: Bstr "atom " :: a :: nil) in
  Error (msg (Pp.pp (Bstack args
                            (Bstack (Bstr "===>")
                               (InvMap.pp env') Left) Left))).

Definition set_field (te:tenv) (ge: aenv) (d:domain) (env:InvMap.t) (a1:atom) (i:EdgeLabel.t) (v:atom) :=
  let pa1  := eval_atom env a1 in
  let pv    := eval_atom env v in
  let* may  := path_above_alias te ge d a1 in
  let env' := inv_may_alias env may  i in
  let* _   := check "set_field" env env' in
(*  let* _   := show_path_above_alias ge d env a1 env' in*)
  let* (_,_,b) := write te ge d a1 (i::nil) v in
  if b  (* no-op - nothinh happens *)
  then OK (pa1  , env)
  else
    OK (set_path pa1 i pv,env').

Fixpoint get_fields (p:option G.PathTree.t) (l :list EdgeLabel.t) : option G.PathTree.t :=
  match l with
  | nil => p
  | fd ::l => get_fields (get_field p fd) l
  end.

Definition suffix_alias (suf: G.PathTree.t) (p : option (list EdgeLabel.t))  : G.PathTree.t :=
  match p with
  | None => Node nil
  | Some l => G.PathTree.create_with  l suf
  end.


Definition inv_suffix_alias (env:InvMap.t) (paths : STree.t (list EdgeLabel.t)) (suf:G.PathTree.t) :=
  InvMap.join env (STree.map (fun _ p => G.PathTree.create_with (List.rev p) suf) paths).

(** Use aliasing instead of equality *)
Fixpoint prefixed_by (p:list EdgeLabel.t) (tr:G.PathTree.t) :=
  match p with
  | nil => Some tr
  | f::p' => match tr with
             | Node nil => Some (Node nil)
             | Node l   => match find_may_edge f l with
                           | None => None
                           | Some tf => prefixed_by p' tf
                           end
             end
  end.

Definition inv_below_alias (env:InvMap.t) (l : (list EdgeLabel.t) * string) (p:G.PathTree.t) :=
  let (l,v) := l in
  match prefixed_by l p with
  | None => env
  | Some p' => InvMap.join env (InvMap.singleton v p' )
  end.


Definition invalid_argument (te:tenv) (age: aenv) (d:domain) (a:atom) (inv: option G.PathTree.t) (env:InvMap.t) :=
  match inv with
  | None => OK env (* The argument is still completly valid *)
  | Some p => let* maya := path_above_alias te age d a in
              let env'  := inv_suffix_alias env maya p in
              let* mayb := path_below_alias te age d a in
              OK (List.fold_right (fun e acc => inv_below_alias acc e p) env' mayb)
  end.

Fixpoint invalid_arguments (te:tenv) (age: aenv) (d:domain) (inv: InvMap.t) (args : list atom) (l : list (btyp * option G.PathTree.t)) : res InvMap.t :=
  match args with
  | nil => match l with
           | nil => OK inv
           | _   => Error (msg "Wrong number of arguments")
           end
  | a1::args' => match l with
                 | nil => Error (msg "Wrong number of arguments")
                 | (_,p1)::lp => let* inv1 := invalid_argument te age d a1 p1 inv in
                                 invalid_arguments te age d inv1 args' lp
                 end
  end.

Definition call (te:tenv) (age: aenv) (d:domain) (ge:genv) (id:ident) (args:list atom) (env:InvMap.t) :=
  match Vars.get id (Vars d) with
  | Some _ => Error ((MSG "identifier ") :: MSG id :: MSG " should be a function." :: nil)
  | None   =>
      match STree.get id ge with
          | None => Error ((MSG "function ") :: MSG id :: MSG " does not exist" :: nil)
      | Some af =>
          let fargs := Afunction.fn_aparams af in
          let (_,p) := Afunction.fn_areturn af in
          (** Invalidate the aliases of the arguments *)
          let* env' := invalid_arguments te age d env args fargs in
          OK (p,env')
          end
  end.

Definition inv_comp  (te:tenv) (age: aenv) (d:domain) (ge:genv)  (env:InvMap.t) (c:comp) :=
  match c with
  | CpAtom a => OK (eval_atom env a,env)
  | CpArraySet a1 i v _ => set_field te age d env a1 (EdgeLabel.Index i) v
  | CpRecordUpdate a1 fd v _ => set_field te age d env a1 (EdgeLabel.Field fd) v
  | CpCall id _ args _  => call te age d ge id args env
  end.


Definition join (v1 v2 : option G.PathTree.t * InvMap.t) : res (option G.PathTree.t * InvMap.t) :=
  OK (InvMap.merge (fst v1) (fst v2) , InvMap.join (snd v1) (snd v2)).

Fixpoint inv_statement (te:tenv) (age:aenv) (d:domain) (ge:genv) (env:InvMap.t) (s:statement) :=
  match s with
  | StSet id c => let* (p,env') := inv_comp te age d ge env c in
                  OK (None, InvMap.set id p env')
  | StIfThenElse _ s1 s2 =>
      let* e1 := inv_statement te age d ge env s1 in
      let* e2 := inv_statement te age d ge env s2 in
      join e1 e2
  | StSwitch a l =>
      let ld := List.map (fun x => inv_statement te age d ge env (snd x)) l in
      merge_list join ld
  | StSequence s1 s2 =>
      let* e1 := inv_statement te age d ge env s1 in
      let* d' := eval_statement te age s1 d in
      match d' with
      | inl d' => inv_statement te age d' ge (snd e1) s2
      | inr _  => Error (msg "statement is wrongly typed")
      end
  | StReturn a  => OK (eval_atom env a,env)
  | StAttr a s  =>
      if String.eqb "aliasing" a
      then
        Error (MSG "#[aliasing]":: MSG nl :: MSG (Pp.pp (InvMap.pp env)):: MSG nl :: MSG (Pp.pp (pp_domain d)) :: nil)
      else inv_statement te age d ge env s
  end.


Definition get_inv_arguments (inv:InvMap.t) (l:list (string * btyp)) :=
  List.map  (fun '(s,bt) => (bt,STree.get s inv)) l.


Definition error_of_path (p : G.PathTree.t) :=
  Bcat (Bstr "the return expression has invalid paths;")
  match p with
  | Node nil => Bstr " all the paths are invalid."
  | Node (e::nil) => Bcat (Bstr " the field ") (Bcat (EdgeLabel.pp (fst e)) (Bstr " is invalid."))
  | Node l      => Bcat (Bstr " the fields ") (Bcat (pp_list (Bstr ", ") EdgeLabel.pp (List.map fst l))
                                                (Bstr " are invalid."))
  end.


Definition inv_def_function (te:tenv)  (age:aenv) (ge:genv) (f:function) : res Afunction.t :=
  let* d := domain_of_function te f in
  let*(r,inv)  := inv_statement te age d ge InvMap.empty (fn_body f) in
  match r with
  | None => OK (Afunction.mk (fn_return f,r) (get_inv_arguments inv (fn_params f)))
  | Some p => Error (msg (Pp.pp (error_of_path p)))
  end.

Definition inv_of_attr (a:param_attr) :=
  match a with
  | AttrReadonly => None
  | AttrWrite | AttrNone => Some (Node nil)
  end.



Definition inv_decl_function (l:list (param_attr * btyp)) (r:btyp) :=
  Afunction.mk (r,None) (List.map (fun '(p,t) => (t,inv_of_attr p)) l).


Definition inv_globdef (te:tenv) (age:aenv) (ge:genv) (gd:globdef) : res genv :=
  match gd with
  | DefConst _ _ _ => OK ge
  | DefFun id f    => match inv_def_function te age ge f with
                      | OK f => OK (STree.set id f ge)
                      | Error e => Error (MSG "In function " :: MSG id :: MSG ":" :: MSG nl :: e)
                      end
  | DeclConst _ _ => OK ge
  | DeclFun id params r => OK (STree.set id (inv_decl_function params r) ge)
  end.

Fixpoint inv_globdefs (te:tenv) (age:aenv) (ge:genv) (gdefs:list globdef) : res genv :=
  match gdefs with
  | nil =>  OK ge
  | gd :: gdefs' => let* ge' := inv_globdef te age ge gd in
                    inv_globdefs te age ge' gdefs'
  end.

Definition check_program (p:program) : res (tenv *(aenv * genv)) :=
  (* Build the typing environment *)
  let* te := err_of_opt (tenv_of_type_defs (prog_types p)) in
  (* Perform alias analysis over all the functions *)
  let* age := eval_globdefs te STree.empty (prog_defs p) in
  (* Analyse the invalid path - could be done on the fly*)
  let* inv := inv_globdefs te age STree.empty (prog_defs p) in
  OK (te,(age,inv)).


From compcert Require Import Maps.
From BarocqComp Require Import Denot.
From BarocqComp Require Import Imp1 Imp1Imp.

Section CORRES.

  Variable tabs : PMap.t Type.

  Inductive match_vals: forall ty, eval_typ tabs ty -> Imp1Imp.val ty -> Imp1Imp.mem tabs -> Prop :=
    | match_Vbool: forall b m,
        match_vals TBool b (Imp1Imp.Vprim TBool (PBool b)) m
    | match_Vint32: forall i s m,
        match_vals (TInt32 s) i (Imp1Imp.Vprim (TInt32 s) (PInt32 s i)) m
    | match_Vint64: forall i s m,
        match_vals (TInt64 s) i (Imp1Imp.Vprim (TInt64 s) (PInt64 s i)) m
    | match_Venum: forall eid elems e m,
        match_vals (TEnum eid elems) e (Imp1Imp.Vprim (TEnum eid elems) (PEnum eid elems e)) m
    | match_Vrecord:
        forall rid fields vr ur a m,
          (forall fd (ty: typ) (vv: eval_typ tabs ty) (uv: Imp1Imp.val ty),
            @Brecord.gprojt typ (eval_typ tabs) fields typ_eq_dec vr fd ty = Some vv ->
            @Brecord.gprojt typ val fields typ_eq_dec ur fd ty = Some uv ->
            match_vals ty vv uv m) ->
          Imp1Imp.get tabs (PtrR a rid fields) m = Some (MRecord tabs rid fields ur) ->
          match_vals (TRecord rid fields) vr (Imp1Imp.Vptr (TRecord rid fields) (PtrR a rid fields)) m
    | match_Varray:
        forall ty va ua a m,
        (forall i (vv: eval_typ tabs ty) (uv: Imp1Imp.val ty),
          Barray.get va i = Some vv ->
          Barray.get ua i = Some uv ->
          match_vals ty vv uv m) ->
        Imp1Imp.get tabs (PtrA a ty) m = Some (MArray tabs ty ua) ->
        match_vals (TArray ty) va (Imp1Imp.Vptr (TArray ty) (PtrA a ty)) m.

  Variable path : Type.

  Variable inv_paths : Type.

  Variable is_valid : path -> InvMap.t -> Prop.

  Record vstate : Type := {
    vs_genv: Denot.genv tabs;
    vs_lenv: Denot.lenv tabs;
  }.

  Record ustate : Type := {
    us_genv: Imp1Imp.genv tabs;
    us_env: Imp1Imp.env;
    us_mem: Imp1Imp.mem tabs;
  }.

  Variable V_eval_path : forall (ty: typ), path -> vstate -> res (eval_typ tabs ty).

  Variable U_eval_path : forall (ty: typ), path -> ustate -> res (Imp1Imp.val ty).

  Definition match_states (inv: InvMap.t) (vs: vstate) (us: ustate) : Prop :=
    forall (ty: typ) (p: path),
      is_valid p inv ->
      res_rel (fun vv uv => match_vals ty vv uv (us_mem us))
        (V_eval_path ty p vs) (U_eval_path ty p us).

  (* Theorem inv_check_correct:
    forall arch tabs te age d ge inv' s r vs us ty,
      match_states inv vs us ->
      Imp1.eval_statement arch tabs te (vs_genv vs) (vs_lenv vs) ty = OK vv ->
      inv_statement te age d ge inv s = OK (_, inv') ->
      (exists uv,
        Imp1Imp.eval_statement arch tabs _ te (us_genv us) (us_env us) (us_mem us) (Some ty) = OK (uv, m')
        /\ match_states inv'  ) *)


End CORRES.

