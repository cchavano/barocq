(** Invalid Path for imp1 *)
Require Import Uint63.
Require Import String FMapInterface FMapList ZArith Int ListSet.
From BarocqComp Require Import Error Maps2 Types Imp1 Graph Typing Utils Pp.
From BarocqComp Require Import Imp1ElimAlias.
From Coq Require Import FMapPositive.
Require Import Syntax.
Import Typed.
Import Imp1.Typed.
(** The analysis requires an alias analysis.
    We have the [Imp1ElimAlias] and this is hardcoded.
    The analysis makes sure that all the function are purely functional.
 *)

Import G.PathTree.

Module InvMap.

  Definition t := STree.t G.PathTree.t.

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

Definition join_path (p1 p2: option G.PathTree.t) :=
  match p1,p2 with
  | None , x | x , None => x
  | Some p1 , Some p2 => Some (G.PathTree.union p1 p2)
  end.

Definition set_path_field (fd:EdgeLabel.t) (v:option G.PathTree.t) :=
  match v with
  | None => None
  | Some p => Some (Node ((fd,p)::nil))
  end.

Definition set_inv (p : option G.PathTree.t) (fd:EdgeLabel.t) (v : option G.PathTree.t) :=
  join_path p  (set_path_field fd v).


Fixpoint find_may_edge {A: Type} (e:EdgeLabel.t) (l:list (EdgeLabel.t * A)) : option A :=
  match l with
  | nil => None
  | (e1,v1) ::l1 => if may_edge e e1 then Some v1 else find_may_edge e l1
  end.

Definition get_field (p:option G.PathTree.t) (fd: EdgeLabel.t) : option G.PathTree.t :=
  match p with
  | None => None (* Evary path is valid *)
  | Some p => match p with
              | Node nil => Some (Node nil) (* Evary path is invalid *)
              | Node l   =>  find_may_edge fd l
              end
  end.

Fixpoint eval_atom (env:InvMap.t) (a:atom) :=
  match a with
  | ATrue | AFalse | AInt32 _ _ | AInt64 _ _ | AConstr _ _ => None
  | AVar i _ => STree.get i env
  | ACast _ _ | AUnaryOp _ _ _ | ABinaryOp _ _ _ _ => None (* this is a primitive value *)
  | AArrayGet a i _ _  =>  get_field (eval_atom env a) (EdgeLabel.Index i)
  | ARecordProj a id _ _ => get_field (eval_atom env a) (EdgeLabel.Field id)
  end.

Definition set_field (ge: aenv) (d:domain) (env:InvMap.t) (a1:atom) (i:EdgeLabel.t) (v:atom) :=
  let pa1  := eval_atom env a1 in
  let v    := eval_atom env v in
  let* may  := path_above_alias ge d a1 in
  let env' := inv_may_alias env may  i in
  OK (set_inv pa1 i v,env').


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
  InvMap.join env (STree.map (fun _ p => G.PathTree.create_with p suf) paths).

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

Definition invalid_argument (age: aenv) (d:domain) (a:atom) (inv: option G.PathTree.t) (env:InvMap.t) :=
  match inv with
  | None => OK env (* The argument is still completly valid *)
  | Some p => let* maya := path_above_alias age d a in
              let env'  := inv_suffix_alias env maya p in
              let* mayb := path_below_alias age d a in
              OK (List.fold_right (fun e acc => inv_below_alias acc e p) env' mayb)
  end.

Fixpoint invalid_arguments (age: aenv) (d:domain) (inv: InvMap.t) (args : list atom) (l : list (btyp * option G.PathTree.t)) : res InvMap.t :=
  match args with
  | nil => match l with
           | nil => OK inv
           | _   => Error (msg "Wrong number of arguments")
           end
  | a1::args' => match l with
                 | nil => Error (msg "Wrong number of arguments")
                 | (_,p1)::lp => let* inv1 := invalid_argument age d a1 p1 inv in
                                 invalid_arguments age d inv1 args' lp
                 end
  end.

Definition call (age: aenv) (d:domain) (ge:genv) (id:ident) (args:list atom) (env:InvMap.t) :=
  match Vars.get id (Vars d) with
  | Some _ => Error ((MSG "identifier ") :: MSG id :: MSG " should be a function." :: nil)
  | None   =>
      match STree.get id ge with
          | None => Error ((MSG "function ") :: MSG id :: MSG " does not exist" :: nil)
      | Some af =>
          let fargs := Afunction.fn_aparams af in
          let (_,p) := Afunction.fn_areturn af in
          (** Invalidate the aliases of the arguments *)
          let* env' := invalid_arguments age d env args fargs in
          OK (p,env')
          end
  end.


Definition inv_comp  (age: aenv) (d:domain) (ge:genv)  (env:InvMap.t) (c:comp) :=
  match c with
  | CpAtom a _ => OK (eval_atom env a,env)
  | CpArraySet a1 i v _ => set_field age d env a1 (EdgeLabel.Index i) v
  | CpRecordUpdate a1 fd v _ => set_field age d env a1 (EdgeLabel.Field fd) v
  | CpCall id _ args _  => call age d ge id args env
  end.

Definition join (v1 v2 : option G.PathTree.t * InvMap.t) : res (option G.PathTree.t * InvMap.t) :=
  OK (InvMap.merge (fst v1) (fst v2) , InvMap.join (snd v1) (snd v2)).

Fixpoint inv_statement (te:tenv) (age:aenv) (d:domain) (ge:genv) (env:InvMap.t) (s:statement) :=
  match s with
  | StSet id c => let* (p,env') := inv_comp age d ge env c in
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
  | StAttr a s  => if String.eqb "aliasing" a
                   then Error (MSG "#[aliasing]":: MSG nl :: MSG (Pp.pp (InvMap.pp env)):: MSG (Pp.pp (pp_domain d)) :: nil)
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
                      | Error e => Error (MSG "In function " :: MSG id :: MSG ":" :: e)
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
  let* te := tenv_of_type_defs (prog_types p) in
  (* Perform alias analysis over all the functions *)
  let* age := eval_globdefs te STree.empty (prog_defs p) in
  (* Analyse the invalid path - could be done on the fly*)
  let* inv := inv_globdefs te age STree.empty (prog_defs p) in
  OK (te,(age,inv)).
