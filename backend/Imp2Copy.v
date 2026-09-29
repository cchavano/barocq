(** Copy propagation *)
From Stdlib Require Import Bool.
From BarocqComp Require Import Syntax ExtOrdered Types Imp2 Maps2.
From compcert Require Import Integers.

Inductive constant :=
| CBool (b:bool)
| CInt32 (i:int) (s:signedness)
| CInt64 (i:int64) (s:signedness)
| CVar   (v:Syntax.ident) (bt:typ2).


Definition constant_eqb (c1 c2:constant) :=
  match c1, c2 with
  | CBool b1 , CBool b2 => Bool.eqb b1 b2
  | CInt32 i1 s1 , CInt32 i2 s2 =>
      Int.eq i1 i2 && signedness_eqb s1 s2
  | CInt64 i1 s1 , CInt64 i2 s2 =>
      Int64.eq i1 i2 && signedness_eqb s1 s2
  | CVar v1 t1 , CVar v2 t2 =>
      String.eqb v1 v2 && typ2_eqb t1 t2
  | _ , _ => false
  end.



Definition is_var (v:Syntax.ident) (c:constant) :=
  match c with
  | CVar v' _ => if Ident.eq_dec v v' then true else false
  | _ => false
  end.

Definition layout_eq_dec (l1 l2:layout) : {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
  decide equality.
  apply BinInt.Z.eq_dec.
Defined.

Fixpoint typ2_eq_dec (t1 t2:typ2) : { t1 = t2 } + { t1 <> t2}.
Proof.
  generalize Ident.eq_dec.
  generalize signedness_eq_dec.
  generalize layout_eq_dec.
  decide equality.
  - apply List.list_eq_dec.
    apply Ident.eq_dec.
  - apply List.list_eq_dec.
    apply pair_eq_dec. exact Ident.eq_dec.
    exact typ2_eq_dec.
  - apply List.list_eq_dec.
    exact typ2_eq_dec.
Defined.

Definition constant_eq_dec (c1 c2: constant) : { c1 = c2 } + { c1 <> c2}.
Proof.
  generalize Bool.bool_dec.
  generalize signedness_eq_dec.
  generalize Int.eq_dec.
  generalize Int64.eq_dec.
  generalize typ2_eq_dec.
  generalize Ident.eq_dec.
  decide equality.
Defined.

Definition var_of_constant (c:constant) :=
  match c with
  | CVar v bt => Some (v,bt)
  | _ => None
  end.

Definition constant_of_atom (a:atom)  : option constant :=
  match a with
  | ATrue => Some (CBool true)
  | AFalse => Some (CBool false)
  | AInt32 i s => Some (CInt32 i s)
  | AInt64 i s => Some (CInt64 i s)
  | AVar v bt    => Some (CVar v bt)
  |  _         => None
  end.

Definition atom_of_constant (c:constant) : atom :=
  match c with
  | CBool b => if b then ATrue else AFalse
  | CInt32 i s => AInt32 i s
  | CInt64 i s => AInt64 i s
  | CVar id bt => AVar id bt
  end.


Fixpoint rename_atom (ren : STree.t constant) (a:atom) : atom :=
  match a with
  | ATrue => ATrue
  | AFalse => AFalse
  | AInt32 i s => AInt32 i s
  | AInt64 i s => AInt64 i s
  | AConstr id i bt => AConstr id i bt
  | AVar v bt  => match STree.get v ren with
                  | None => AVar v bt
                  | Some v' => (atom_of_constant v')
                  end
  | ACast a bt => ACast (rename_atom ren a) bt
  | AUnaryOp o a bt => AUnaryOp o (rename_atom ren a) bt
  | ABinaryOp b a1 a2  bt => ABinaryOp b (rename_atom ren a1) (rename_atom ren a2) bt
  | AArrayGet a1 a2 l bt => AArrayGet (rename_atom ren a1) (rename_atom ren a2) l bt
  | ARecordProj a1 fid l bt => ARecordProj (rename_atom ren a1) fid l bt
  | APureCall fid b l bt  => APureCall fid b (List.map (rename_atom ren) l) bt
  end.

Definition merge_ren (r1 : STree.t constant) (r2: STree.t constant) :=
  STree.combine (fun i j =>  Some (i,j)) r1 r2.

Definition is_skip (s:statement) :=
  match s with
  | StSkip => true
  | _      => false
  end.

Definition stseq (s1 s2 : statement) :=
  if is_skip s1 then s2
  else if is_skip s2 then s1 else
         StSequence s1 s2.

Definition merge_one (s1 s2: statement) (ren: STree.t constant) (v:Ident.ident) (c1 c2:option constant) :
  (STree.t constant * statement * statement ) :=
  match c1 , c2 with
  | None , None => (ren, s1,s2)
  | Some c1 , None => (ren, stseq s1 (StSet v ( (atom_of_constant c1))),
                        s2)
  | None , Some c2  => (ren,s1 , stseq s2 (StSet v ( (atom_of_constant c2))))
  | Some c1 , Some c2 =>
      if constant_eq_dec  c1 c2
      then (STree.set v c1 ren,s1,s2)
      else (ren, stseq s1 (StSet v ( (atom_of_constant c1))),
             stseq s2 (StSet v ( (atom_of_constant c2))))
  end.

Definition merge_statement (r1 r2 : STree.t constant) :=
  STree.fold (fun '(ren,s1,s2) v '(c1,c2) => merge_one s1 s2 ren v c1 c2) (merge_ren r1 r2) (STree.empty, StSkip, StSkip).

Definition statement_of_renaming (r:STree.t constant) : statement :=
  STree.fold (fun st v c => stseq (StSet v (atom_of_constant c)) st) r StSkip.

Definition transl_ecomp (ren: STree.t constant) (ec:ecomp) : ecomp :=
  match ec with
  | EcArraySet a1 a2 a3 => EcArraySet (rename_atom ren a1) (rename_atom ren a2) (rename_atom ren a3)
  | EcRecordUpdate a1 id a2 => EcRecordUpdate (rename_atom ren a1) id (rename_atom ren a2)
  end.

Definition remove_opt (o:option ident) (ren : STree.t constant) : STree.t constant :=
  match o with
  | None => ren
  | Some id => STree.remove id ren
  end.

Definition flush_rename (ren:STree.t constant) (id:ident) : STree.t constant * statement :=
  STree.fold (fun acc x c => if is_var id c
                             then (fst acc, stseq (StSet x (atom_of_constant c)) (snd acc))
                             else (STree.set x c (fst acc) , snd acc)) ren (STree.empty,StSkip).

Definition inter_rename_aux (r1 r2 : option constant) :=
  match r1 , r2 with
  | None , None => None
  | None , Some _ | Some _ , None => None
  | Some c1 , Some c2 => if constant_eq_dec c1 c2 then Some c1 else None
  end.

Definition diff_rename_aux (r1 r2 : option constant) :=
  match r1 , r2 with
  | None , None => None
  | None , Some c  => None
  | Some c , None  => Some c
  | Some c1 , Some c2 => if constant_eq_dec c1 c2 then None else Some c1
  end.

Definition inter_rename (r1 r2: STree.t constant) :=
  STree.combine inter_rename_aux r1 r2.

Definition diff_rename (r1 r2: STree.t constant) :=
  STree.combine diff_rename_aux r1 r2.


Definition inter_list (l : list ((Benum.pattern * statement) * (STree.t constant * bool))) : STree.t constant :=
  match l with
  | nil => STree.empty
  | cons e  l =>
      List.fold_left (fun acc e => inter_rename (fst (snd e)) acc) l (fst (snd e))
  end.

Definition filter_pattern (shared_ren:STree.t constant) (p : (Benum.pattern * statement) * (STree.t constant * bool))
   :=

  let dren := diff_rename (fst (snd p)) shared_ren in
  (fst (fst p) , stseq (snd (fst p)) (statement_of_renaming dren)).

Definition gen_switch (l : list ((Benum.pattern * statement) * (STree.t constant * bool))) : STree.t constant *
                                                                                         list (Benum.pattern * statement) * bool :=
  let is_return := List.forallb (fun x => snd (snd x)) l in
  if is_return
  then (STree.empty, List.map fst l, is_return) (* ignore the renaming, we simply return *)
  else let shared_ren := inter_list l in
       (shared_ren, List.map (filter_pattern shared_ren) l, is_return).




Definition eqb (v1 v2: STree.t constant * statement * bool) :=
  let '(c1,s1,b1) := v1 in
  let '(c2,s2,b2) := v2 in
  STree.beq constant_eqb c1 c2 && statement_eqb s1 s2 && Bool.eqb b1 b2.

Fixpoint transl_statement (ren:STree.t constant) (s:statement) : (STree.t constant * statement * bool) :=
  match s with
  | StSkip     => (ren,StSkip,false)
  | StSet id c => let c' := rename_atom ren c in
                  (* TODO - if c' is a variable, no need to flush *)
                  let (ren',st) := flush_rename ren id in
                  match constant_of_atom c' with
                  | None => (STree.remove id ren', stseq st (StSet id c'),false)
                  | Some c' => (STree.set id c' ren', st,false)
                  end
  | StEcomp ec  => (ren, StEcomp (transl_ecomp ren ec),false)
  | StIfThenElse a1 s1 s2 =>
      let a1 := rename_atom ren a1 in
      let '(r1,s1,b1) := transl_statement ren s1 in
      let '(r2,s2,b2) := transl_statement ren s2 in
      let '(rn,cp1,cp2) := merge_statement r1 r2 in
      if andb b1 b2
      then (rn, StIfThenElse a1 s1 s2, true) (* the statement returns *)
      else (rn, StIfThenElse a1 (stseq s1 cp1) (stseq s2 cp2),false)
  | StWhile cond variant body =>
      (*match itern (fun rn =>
                          let '(rn1,_,_) := transl_statement rn body in
                          OK rn1)
                       (STree.beq constant_eqb)
                       (fun rn1 rn2 =>
                          let '(rn,_,_) := merge_statement rn1 rn2 in
                          OK rn)
                       ren 10  with
        Error => *)
      (* Would be better to iterate *)
      let st := statement_of_renaming ren in
      let '(rn',body',b) := transl_statement STree.empty body in
      let st' := statement_of_renaming rn' in
      (STree.empty ,
        stseq st (StWhile cond variant (stseq body' st')) , false)
  | StSwitch a l =>
      let a1 := rename_atom ren a in
      let l  := List.map (fun x =>
                            let '(ren',s',b) := transl_statement ren (snd x) in
                            ((fst x, s'),(ren',b))) l in
      let '(ren,l',b) := gen_switch l in
      (ren, StSwitch a1 l',b)
  | StSequence s1 s2 =>
      let '(ren,s1',_) := transl_statement ren s1 in
      let '(ren,s2',b) := transl_statement ren s2 in
      (ren, stseq s1' s2',b)
  | StCall oid f ty l t2 =>
      (remove_opt oid ren,
      StCall oid f ty (List.map (rename_atom ren) l) t2,false)
  | StReturn a => (ren,StReturn (option_map (rename_atom ren) a),true)
  end.

Definition transl_function  (f:function) :=
  let '(_,s',_) := transl_statement  STree.empty (fn_body f) in
  mk_function (fn_return f) (fn_params f) s'.

Definition transl_globdef  (g:globdef) :=
  match g with
  | DefFun id f => DefFun id  (transl_function  f)
  | _      =>  g
  end.

Definition transl_globdefs  (l:list globdef) :  list globdef :=
  List.map transl_globdef l.

Definition transl_program   (p: program) : program :=
  let gds :=  transl_globdefs  (prog_defs p) in
  mk_program gds (prog_types p) (prog_tabs p).
