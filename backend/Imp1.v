From Coq Require Import Bool List String PArith Lia.
From compcert Require Import Integers.
From BarocqComp Require Import  Barocq Benum  Barray Brecord Error Maps2 Utils Syntax Types Typing Pp.
From BarocqComp Require Printer.
(** * Abstract syntax *)

(** ** Literals *)

Definition literal : Type := Syntax.literal.

(** ** Atoms *)

Definition atom : Type := Syntax.atom.

(** ** Statements *)
 
Inductive statement : Type :=
  | StSet : ident -> comp -> statement
  | StIfThenElse : atom -> statement -> statement -> statement
  | StSwitch : atom -> list (pattern * statement) -> statement
  | StSequence : statement -> statement -> statement
  | StReturn : atom -> statement
  | StAttr   : ident -> statement -> statement
.

(** ** Functions *)

Definition function : Type := Syntax.function statement btyp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function btyp.

(** ** Programs *)

Definition program : Type := Syntax.program globdef field_descr.

Module Typed.

  (** * Typed abstract syntax *)

  (** ** Literals *)

  Definition literal : Type := Syntax.literal.

  (** ** Atoms *)
    
  Definition atom : Type := Syntax.Typed.atom.

  (** ** Computations *)

  Definition comp : Type := Syntax.Typed.comp.

  (** ** Statements *)

  Inductive statement : Type :=
    | StSet : ident -> comp -> statement
    | StIfThenElse : atom -> statement -> statement -> statement
    | StSwitch : atom -> list (pattern * statement) -> statement
    | StSequence : statement -> statement -> statement
    | StReturn : atom -> statement
    | StAttr : ident -> statement -> statement.

  (** ** Functions *)

  Definition function : Type := Syntax.function statement btyp.

  (** ** Global definitions *)

  Definition globdef : Type := Syntax.globdef literal function btyp.

  (** ** Programs *)

  Definition program : Type := Syntax.program globdef field_descr.


Module Pp.
  Import String.
  Import ListNotations.
  Import Typed.

  Fixpoint pp_statement (s:statement) :=
    match s with
    | StSet i c => Bcat (Bstr i) (Bcat (Bstr "=") (Printer.Typed.pp_comp c))
    | StIfThenElse a s1 s2 =>
        let s1 := Bcat (Bstr " then ") (pp_statement s1) in
        let s2 := Bcat (Bstr " else ") (pp_statement s2) in
        let c  := Printer.Typed.pp_atom a in
        let cd := Bcat (Bstr "if ") c in
        Bstack cd (Bstack s1 s2 Left) Left
    | StSwitch a l => Bstr "case..."
    | StSequence s1 s2 =>
        let s1 := pp_statement s1 in
        let s2 := pp_statement s2 in
        Bstack (Bcat s1 (Bstr ";"))
               s2 Left
    | StReturn a => Bcat (Bstr "return ") (Printer.Typed.pp_atom a)
    | StAttr a s => Bcat (Bstr "[#") (Bcat (Bstr a) (Bcat (Bstr "]") (pp_statement s)))
    end.

  Definition pp_program (p:program) := Printer.pp_program  Printer.pp_btyp pp_statement p.

End Pp.


  Section TRANSF.
    Variable trans_statement : statement -> res statement.

    Definition trans_function (f:function) :=
      let* b := trans_statement (fn_body f) in
      OK {| fn_return := fn_return f;
           fn_params := fn_params f;
           fn_body   := b
        |}.

    Definition trans_globdef (gd : globdef) : res globdef :=
      match gd with
      | DefFun id f    => let* f' := trans_function f in
                          OK (DefFun id f')
      | _ => OK gd
      end.

    Definition trans_program (p:program) : res program :=
      let* gd' :=  mmap trans_globdef (prog_defs p) in
      OK {|
        prog_defs := gd';
        prog_types := prog_types p;
        prog_tabs := prog_tabs p;
      |}.

  End TRANSF.

  Module UnType.
(*    Fixpoint untype_atom (a:atom) : Imp1.atom :=
      match
    ATrue : btyp -> Syntax.Typed.atom
  | AFalse : btyp -> Syntax.Typed.atom
  | AInt32 : int -> btyp -> Syntax.Typed.atom
  | AInt64 : int64 -> btyp -> Syntax.Typed.atom
  | AConstr : ident -> btyp -> Syntax.Typed.atom
  | AVar : ident -> btyp -> Syntax.Typed.atom
  | ACast : Syntax.Typed.atom -> btyp -> Syntax.Typed.atom
  | AUnaryOp : unary_op -> Syntax.Typed.atom -> btyp -> Syntax.Typed.atom
  | ABinaryOp : binary_op ->
                Syntax.Typed.atom ->
                Syntax.Typed.atom -> btyp -> Syntax.Typed.atom.
*)

  End UnType.


  

  
  Module Semantics.
    Import Typed.

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

    Definition addr_of_ptr {ty:typ} (p:ptr ty) : res addr :=
      match p with
      | PtrA a _ => OK a
      | PtrR a _ _ => OK a
      | PtrF _ _ _ => fail
      | PtrAbs a _ => OK a
      end.


    Module MEM.
      (** We just need a fresh address *)
      Section S.
        Context {mval : typ -> Type}.

        Record t : Type := mkmem {
            _mem  : addr -> res {ty : typ & mval ty};
            _fresh : addr;
            _wf_fresh : forall a, (_fresh <= a)%positive -> _mem a  = fail;
                               }.

        Definition  get {ty:typ} (p:ptr ty) (m:t) : res (mval ty):=
          let* a := (addr_of_ptr p) in
          let* ma := _mem m a in
          let (tv,v) := ma in
          match typ_eq_dec tv ty with
          | left EQ => OK (cast (f_equal mval EQ) v)
          | _  => fail
          end.

        Definition _set (a:addr) (ty:typ) (v:mval ty) (m: addr -> res {ty:typ & mval ty}) :=
          fun x => if Pos.eq_dec a x then
                     OK (existT _ _ v)
                   else m x.

        Lemma set_lt : forall a ty (v:mval ty) m,
                              (a < (_fresh m))%positive ->
                              forall a1, (_fresh m <= a1)%positive -> _set a ty v (_mem m) a1 = efail.
        Proof.
          unfold _set.
          intros.
          destruct (Pos.eq_dec a a1).
          subst.
          lia.
          apply _wf_fresh. lia.
        Qed.

        Definition set {ty: typ} (p:ptr ty) (v:mval ty) (m:t) : res t :=
          let* a := addr_of_ptr p
          in match Coqlib.plt a (_fresh m) with
             | left LT => OK {| _mem := _set a ty v (_mem m); _fresh := _fresh m; _wf_fresh := set_lt a ty v m LT |}
             | right _ => efail
             end.

        Lemma alloc_lt : forall m a,
            (Pos.succ (_fresh m) <= a)%positive -> _mem m a = efail.
        Proof.
          intros.
          apply _wf_fresh.
          lia.
        Qed.

        Definition alloc (m:t) : t * positive :=
          (mkmem (_mem m) (Pos.succ (_fresh m)) (alloc_lt m), _fresh m).

      End S.

    End MEM.



    Section S.
      Variable arch : Target.archi.
      Variable abs_typ_impl : Maps.PMap.t Type.

    (* The semantics is dynamically typed.
     *)

    Inductive val : typ -> Type :=
    | Vprim  : forall (ty:typ) (p:pval ty), val ty
    | Vptr  : forall (ty:typ) (p:ptr ty), val ty.


    Inductive mval : typ -> Type :=
    | MPval : forall (ty:typ) (v: pval ty), mval ty
    | MArray : forall (ty:typ) (a : array (val ty)), mval (TArray ty)
    | MRecord : forall (id:ident) (rty :smaplist typ)
                       (r :record val rty), mval (TRecord id rty) (* id should not be there *)
    | MAbs : forall (id:ident),SMap.get id abs_typ_impl -> mval (TAbs id).

    Definition mem := @MEM.t mval.

    Fixpoint typ_of_fun (l:list typ) (r:typ) :=
      match l with
      | nil => res (val r * mem)
      | e::l => val e -> typ_of_fun l r
      end.

    Definition Fun (args: list typ) (tret: typ) := mem -> typ_of_fun args tret.

    Definition funT := { args : list typ & {tret : typ & Fun args tret}}.

    Definition genv := ident -> res funT.

    Definition cast_pval {ty}  (pv : pval ty) (ty':typ): res (pval ty') :=
      match typ_eq_dec ty ty' with
      | left EQ => OK (cast (f_equal pval EQ) pv)
      | _ => fail
      end.

    Definition cast_mval {ty}  (pv : mval ty) (ty':typ): res (mval ty') :=
      match typ_eq_dec ty ty' with
      | left EQ => OK (cast (f_equal mval EQ) pv)
      | _ => fail
      end.

  Definition cast_val {ty:typ} (v: val ty) (ty':typ) : res (val ty') :=
    match typ_eq_dec ty ty' with
    | left EQ => OK (eq_rect ty val v ty' EQ)
    | right _ => efail
    end.



  Definition env := ident -> res {ty & val ty}.

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

  Definition eval_pval {ty:typ} (p:pval ty) : eval_typ abs_typ_impl ty :=
    match p with
    | PBool b     => b
    | PInt32 s i  => i
    | PInt64 s i  => i
    | PEnum i l e => e
    end.

  Definition pval_of_typ (ty:typ) : eval_typ abs_typ_impl ty -> res (pval ty) :=
    match ty with
    | TBool => fun b => OK (PBool b)
    | TInt32 s => fun i => OK (PInt32 s i)
    | TInt64 s => fun i => OK (PInt64 s i)
    | TEnum i l => fun e => OK (PEnum i l e)
    |  _        => (fun _ => fail)
    end.

  Definition val_of_pval {ty:typ} (pv: res (pval ty)) : res (val ty) :=
    let* v := pv in
    OK (Vprim _ v).


  Definition typof_atom (te:tenv) (a: atom) : res typ :=
    btyp_to_typ te (Typing.typof_atom a).

  Definition eval_val {ty:typ} (v : val ty) : res (eval_typ abs_typ_impl ty) :=
    match v with
    | Vprim _ v => OK (eval_pval v)
    | _  => fail
    end.

  Definition val_of_eval_typ {ty:typ} (v : eval_typ abs_typ_impl ty) : res (val ty) :=
    match pval_of_typ ty v with
    | OK v => OK (Vprim _ v)
    | _    => fail
    end.

  Definition index_of_pval {ty:typ} (v:pval ty) : res int64 :=
    if arch
    then
      match v with
      | PInt32 Unsigned i =>  OK (Intop.U64.of_u32 i)
      | _          => fail
      end
    else
      match v with
      | PInt64 Unsigned i =>  OK i
      | _          => fail
      end.

  Definition index_of_val {ty :typ} (v:val ty) : res int64 :=
    match v with
    | Vprim _ pv => index_of_pval pv
    | _       => fail
    end.

  Definition isptr {ty:typ} (v:val ty) : res (ptr ty) :=
    match v with
    | Vptr _ p => OK p
    | _        => fail
    end.


  Definition cast_typof_field ( k:ident) (fields : smaplist typ) (GP :good_proj k fields = true) :
    typeof_field val k  fields GP ->   {ty:typ & val ty} :=
    fun X =>
      let s := exists_typeof_field val k fields GP in
      let (ty, EQ) := s in
      existT val ty (cast EQ X).

  Definition eval_array_get (m:mem) {ta:typ} (v1:val ta) {ti:typ} (v2:val ti) (tr:typ) : res (val tr) :=
    let*  i := index_of_val v2 in
    let*  p := isptr v1 in
    let* arr := MEM.get p m in
    match arr with
    | MArray _ l =>  let* v := get l i in cast_val v tr
    | _ => fail
    end.

  Definition eval_record_proj (m:mem) {tr : typ} (pr:val tr) (k:ident) (tr:typ) : res (val tr) :=
    let* p := isptr pr in
    let* rc := MEM.get p m in
    match rc with
    | MRecord id fields r =>
        match bool_dec  (good_proj k fields) true  with
        | left EQ => let (ty,v) := cast_typof_field k fields EQ (project val r k EQ) in
                    cast_val v tr
        | right _ => fail
        end
    | _ => fail
    end.

  Fixpoint eval_atom (te: tenv) (e:env) (m: mem) (tyr:typ) (a:atom)  : res (val tyr) :=
    match a with
    | ATrue => val_of_pval (cast_pval (PBool true) tyr)
    | AFalse => val_of_pval (cast_pval (PBool false) tyr)
    | AInt32 i s => val_of_pval (cast_pval (PInt32 s i) tyr)
    | AInt64 i s  => val_of_pval (cast_pval (PInt64 s i) tyr)
    | AConstr s bt =>
        let* td := btyp_to_typ te bt  in
        match get_enum td with
        | None => fail
        | Some (i,l) => let* e :=  make_enum l s in
                        val_of_pval (cast_pval (PEnum i l e) tyr)
        end
    | AVar v _ => let* v := e v in
                  let (tv,vl) := v in
                  cast_val vl tyr
    | ACast a1 tr =>
        let* tr := btyp_to_typ te tr in
        let* te1 := typof_atom te a1 in
        let* v1  := eval_atom te e m te1 a1   in
        match v1 with
        | Vprim ty' pv =>
            let* f := get_cast abs_typ_impl ty' tr in
            let* v' := f (eval_pval pv)  in
            let* pv := pval_of_typ _ v' in val_of_pval (cast_pval pv tyr)
        | _ => fail
        end
    | AUnaryOp op a1 bt =>
        let* tye := btyp_to_typ te bt in
        let* v := eval_atom te e m tye a1  in
        let* v := eval_val v in
        let* res := eval_unary_op abs_typ_impl op tye v tyr in
        val_of_eval_typ res
    | ABinaryOp op a1 a2 bt =>
        let* tye1 := typof_atom te a1 in
        let* tye2  := typof_atom te a2 in
        let* v1 := eval_atom te e m tye1 a1 in
        let* v2 := eval_atom te e m tye2 a2 in
        let* v1 := eval_val v1 in
        let* v2 := eval_val v2 in
        let* res := eval_binary_op abs_typ_impl op tye1 tye2 v1 v2 tyr in
        let* pv := pval_of_typ _ res in val_of_pval (cast_pval pv tyr)
    | AArrayGet a1 i _ bt =>
        let* tya1 := typof_atom te a1 in
        let* v1 := eval_atom te e m tya1 a1 in
        let* v2 := eval_atom te e m (typof_index arch) i  in
        eval_array_get m v1 v2 tyr
    | ARecordProj r id _ bt =>
        let* t := typof_atom te r in
        let* r := eval_atom te e m t r in
        eval_record_proj m r id tyr
    end.

Definition eval_array_set (m:mem) {ta:typ} (a:val ta) {ti:typ} (i:val ti) {te:typ} (v:val te): res mem :=
  let*  i := index_of_val i in
  let*  p := isptr a in
  let* arr := MEM.get p m in
  match arr in mval t return  t = ta -> res mem with
  | MArray te' l => fun EQ =>
                      let* v := cast_val v te' in
                      let* l' := set l i v in
                      MEM.set p (cast (f_equal mval EQ) (MArray _ l'))  m
  | _ => fun _ => fail
  end eq_refl.

Definition eval_record_update (m:mem) {tr:typ} (r:val tr) (k:ident) {te:typ} (v:val te): res mem :=
  let* p := isptr r in
  let* rc := MEM.get p m in
  match rc in mval t return  t = tr -> res mem with
  | MRecord id fields r => fun EQ =>
                             let* r1 := dyn_upd val typ_eq_dec r k  _ v in
                             MEM.set p (cast (f_equal mval EQ) (MRecord _ _ r1))  m
  | _ => fun _ => fail
  end eq_refl.


(* Definition eval_access (te:tenv) (e:env) (m:mem) {ty:typ} (v:val ty) (acc:access) (tr:typ)  : res (val tr) :=
  match acc with
  | AcRecordField id bt _ => eval_record_proj m v id  tr
  | AcArrayIndex a bt _ =>
      let* i := eval_atom te e (typof_index arch) a  in
      eval_array_get m v i tr
  end.

Definition typeof_access (te:tenv) (a:access) : res typ :=
  match a with
  | AcRecordField _ bt _ => btyp_to_typ te bt
  | AcArrayIndex _ bt _ => btyp_to_typ te bt
  end.

Fixpoint eval_accesses (te:tenv) (e:env) (m:mem) {ty:typ} (v:val ty) (l:list access) (tr:typ) : res (val tr) :=
  match l with
  | nil => cast_val v tr
  | acc::l =>
      let* ta := typeof_access te acc in
      let*va := eval_access te e m v acc ta in
      eval_accesses te e m va l tr
  end. *)

Definition cast_function {a1 a2:list typ} {r1 r2:typ} (Eq : TFun a1 r1 = TFun a2 r2) (f : mem -> typ_of_fun a1 r1) :
  mem -> typ_of_fun a2 r2.
Proof.
  injection Eq.
  intros E1 E2.
  rewrite E2 in f.
  rewrite E1 in f.
  apply f.
Defined.


Definition get_fun (ge:genv) {args:list typ} {ret:typ} (v :val (TFun args ret)) : res (mem -> typ_of_fun args ret):=
match v with
| Vprim _ _ => fail (* This is actually impossible *)
| Vptr _ ptr  =>
    match ptr with
    | PtrF fid _ _ => let* f := ge fid in
                      match f with
                      | existT _ args' (existT _ ret' fc) =>
                          match typ_eq_dec (TFun args' ret') (TFun args ret)  with
                          | left EQ => OK (cast_function EQ fc)
                          | _  => fail
                          end
                      end
    | _ => fail
    end
end.


Fixpoint eval_app (tparams : list typ) (tret : typ)
  (args : DList.dlist (DList.resFtyp val) tparams) : forall (f: typ_of_fun tparams tret), res (val tret * mem) :=
    match args with
  | DList.DNIL _ => fun f => f
  | DList.DCONS  _ e  args' =>
      fun f => let* e1 := e in
               eval_app _ _ args' (f e1)
    end.


Definition eval_comp (te:tenv) (ge:genv) (e:env) (m:mem) (c:comp) (tr:typ) : res (val tr  * mem) :=
  match c with
  | CpAtom a bt => let* va := eval_atom te e m tr a in
                   OK (va,m)
  (* | CpArrayGet a1 i bt _ =>
      let* tya1 := typof_atom te a1 in
      let* v1 := eval_atom te e m tya1 a1 in
      let* v2 := eval_atom te e m (typof_index arch) i  in
      let* r  := eval_array_get m v1 v2 tr in
      OK(r,m) *)
  | CpArraySet a i v bt =>
      let* ta := typof_atom te a in
      let* tv := typof_atom te v in
      let* a := eval_atom te e m ta a in
      let* i := eval_atom te e m (typof_index arch) i in
      let* v := eval_atom te e m tr v in
      let* m := eval_array_set m a i v  in
      OK (v,m)
  (* | CpRecordProj r id bt _ =>
      let* t := typof_atom te r in
      let* r := eval_atom te e m t r in
      let* v := eval_record_proj m r id tr in
      OK(v,m) *)
  | CpRecordUpdate r id v bt =>
      let* trec := typof_atom te r in
      let* tv   := typof_atom te v in
      let* r := eval_atom te e m tr r in
      let* v := eval_atom te e m tv v in
      let* m := eval_record_update m r id v in
      OK(r,m)
  (* | CpDeepAccess a l bt =>
      let*  ta := typof_atom te a in
      let* a := eval_atom te e m ta a in
      let* v := eval_accesses te e m a l tr in
      OK(v,m) *)
  | CpCall f btf args bt =>
      let* tyf := btyp_to_typ te btf in
      match tyf with
      | TFun tparams tret =>
          let* f := eval_atom te e m (TFun tparams tr) (AVar f btf) in
          let* f := get_fun ge f in
          let* vargs := DList.map2 _ (eval_atom te e m) args tparams in
          eval_app tparams tr vargs (f m)
      | _  => fail
      end
    end.

Definition typof_comp (te:tenv) (c: comp) : res typ :=
    btyp_to_typ te (Typing.typof_comp c).

Definition env_set (id:ident) {ty:typ} (v:val ty) (e:env) : env :=
  fun x => if Ident.eq_dec x id then OK (existT _ ty v) else e x.


Definition typ_of_statement (ty:option typ) :=
  match ty with
  | None => env
  | Some ty => val ty
  end.

Definition eval_match (tv:typ) (v: val tv) (ty: option typ) (cases: list (pattern * (res (typ_of_statement ty * mem)))) :
  res (typ_of_statement ty * mem) :=
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



Fixpoint eval_statement (te:tenv) (ge:genv) (e:env) (m:mem) (ty:option typ) (s:statement)  : res (typ_of_statement ty * mem) :=
  match s with
  | StSet id c =>
      match ty with
      | None =>
          let* tyid := typof_comp te c in
          let*(r,m') := eval_comp te ge e m c tyid in
          OK (env_set id r e,m')
      | _ => fail
      end
  | StIfThenElse a s1 s2 =>
      let* v := eval_atom te e m TBool a in
      eval_statement te ge e m ty (if bool_of_valbool v then s1 else s2)
  | StSwitch a l =>
      let* ta := typof_atom te a in
      let* va  := eval_atom te e m ta a  in
      let vcases :=  MapList.map (eval_statement te ge e m ty) l in
      eval_match ta va ty vcases
  | StSequence s1 s2 =>
      let* (e1,m1) := eval_statement te ge e m None s1 in
      eval_statement te ge e1 m1 ty s2
  | StReturn a =>
      match ty with
      | None => fail
      | Some ty =>
          let* va := eval_atom te e m ty a in
          OK (va,m)
      end
  | StAttr a s => eval_statement te ge e m ty s
  end.



Fixpoint build_funval_rec (te: tenv) (ge: genv)  (e: env) (params: smaplist typ) (tret: typ)  (s: statement) :
  mem -> typ_of_fun (List.map snd params) tret.
Proof.
  destruct params.
  - simpl.
    apply (fun m => eval_statement te ge e m (Some tret) s).
  - simpl.
    apply (fun m X => build_funval_rec te ge (env_set (fst p)  X e) params tret s m).
Defined.

Definition env_empty : env := fun _ => fail.

Definition build_Fun (te:tenv) (ge:genv) (params:smaplist btyp) (tret:btyp) (s:statement) : res funT  :=
  if MapList.nodup Ident.eq_dec params
  then
    let* tret' := btyp_to_typ te tret in
    let* params' := MapList.map_err (btyp_to_typ te) params in
    OK (existT _ (List.map snd params') (existT _ tret' (build_funval_rec te ge  env_empty params' tret' s)))
  else fail.

Section MAPACC.
  Context {A B MEM:Type}.
  Variable F : A -> MEM -> res (B * MEM).

  Fixpoint mmap_fold (l:list A) (m:MEM) : res (list B * MEM) :=
    match l with
    | nil => OK(nil,m)
    | e::l => let* (fe,m1) := F e m in
              let* (l ,mr) := mmap_fold l m1 in
              OK (fe::l,mr)
    end.

End MAPACC.


Fixpoint array_of_values (l :list {ty:typ & val ty}) (ty:typ) : res (array (val ty)) :=
  match l with
  | nil => OK nil
  | e::l => let* a := array_of_values l ty in
            let (te,ve) := e in
            let* ve' := cast_val ve ty in
            OK (ve' :: a)
  end.


Fixpoint eval_record_lit (lv: smaplist {ty:typ & val ty}) (fields: smaplist typ) : res (eval_recordtyp val fields).
    destruct lv as [|[x [tv v]] lv']; destruct fields as [| [y t] fields'].
    - apply (OK tt).
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
        apply (OK (Field y cv, rc)).
      + apply fail.
  Defined.


(* Like Barocq, the semantics is not typed *)

Fixpoint eval_literal (te: tenv)  (l: literal)  (m:mem): res ({ty:typ & val ty} * mem) :=
  match l with
  | LTrue => OK  (existT _ _ (Vprim _ (PBool true)),m)
  | LFalse => OK (existT _ _ (Vprim _ (PBool false)), m)
  | LInt32 i s => OK (existT _ _  (Vprim _ (PInt32 s i)),m)
      (* match get_signed true bt with
      | None => fail
      | Some s => OK (existT _ _  (Vprim _ (PInt32 s i)),m)
      end *)
  | LInt64 i s => OK (existT _ _ (Vprim _ (PInt64 s i)),m)
      (* match get_signed true bt with
      | None => fail
      | Some s => OK (existT _ _ (Vprim _ (PInt64 s i)),m)
      end *)
  | LArray a bt _ =>
      let* ta := btyp_to_typ te bt in
      match ta with
      | TArray elt =>
          let* (av,m) := mmap_fold (eval_literal te) a m in
          let* av := array_of_values av elt in
          let (m2,fa) := MEM.alloc m in
          let ptr     := PtrA fa elt in
          let* m := MEM.set ptr (MArray _ av) m2 in
          OK(existT _ _ (Vptr _ ptr),m)
      |  _         => fail
      end
  | LRecord rc ub rid =>
      let* tr := btyp_to_typ te (BRecord rid ub) in
      match tr with
      | TRecord id l =>
          let* (r,m) := mmap_fold (fun x m => let* (v,m) := eval_literal te (snd x) m in
                                              OK ((fst x,v),m)) rc m in
          let* r := eval_record_lit r l in
          let (m1,fa) := MEM.alloc m in
          let ptr     := PtrR fa id l in
          let* m2 := MEM.set ptr (MRecord id l r) m1 in
          OK(existT _ _ (Vptr _ ptr),m2)
      |  _         => fail
      end
  end.



    End S.
  End Semantics.


End Typed.

Module Aliasing_AST.

  (** * Typed abstract syntax with aliasing information *)

  Parameter ABSDOM : Type.

  (** ** Literals *)

  Definition literal : Type := Syntax.literal.

  (** ** Atoms *)
    
  Definition atom : Type := Syntax.Typed.atom.

  (** ** Computations *)

  Definition comp : Type := Syntax.Typed.comp.

  (** ** Statements *)

  Inductive statement : Type :=
    | StSet : ident -> comp -> ABSDOM -> ABSDOM -> statement
    | StIfThenElse : atom -> statement -> statement -> ABSDOM -> ABSDOM -> statement
    | StSwitch : atom -> list (pattern * statement) -> ABSDOM -> ABSDOM -> statement
    | StSequence : statement -> statement -> statement
    | StReturn : atom -> ABSDOM -> ABSDOM -> statement.

  (** ** Functions *)

  Definition function : Type := Syntax.function statement btyp.

  (** ** Global definitions *)

  Definition globdef : Type := Syntax.globdef literal function btyp.

  (** ** Programs *)

  Definition program : Type := Syntax.program globdef field_descr.

End Aliasing_AST.

Module Imp1Typed := Imp1.Typed.

Module Typing.

  Import Syntax.Typed.
  Import Imp1Typed.
  Import ListNotations.

  Section ARCHI.

  Variable arch : Target.archi.

  Fixpoint typecheck_atom (be: benv) (gx: gcontext) (lx: lcontext) (a: Syntax.atom) : res Syntax.Typed.atom :=
    match a with
    | Syntax.ATrue => ret ATrue
    | Syntax.AFalse => ret AFalse
    | Syntax.AInt32 i s => ret (AInt32 i s)
    | Syntax.AInt64 i s => ret (AInt64 i s)
    | Syntax.AConstr x =>
        let* t := typof_constr be x in
        ret (AConstr x t)
    | Syntax.AVar x =>
        let* t := typof_var gx lx x in
        ret (AVar x t)
    | Syntax.ACast a1 ty =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* t := typecheck_cast (typof_atom a1') ty in
        ret (ACast a1' t)
    | Syntax.AUnaryOp op a1 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let ty1 := typof_atom a1' in
        let* t := typecheck_unary_op op ty1 in
        ret (AUnaryOp op a1' t)
    | Syntax.ABinaryOp op a1 a2 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* t := typecheck_binary_op op ty1 ty2 in
        ret (ABinaryOp op a1' a2' t)
    | Syntax.AArrayGet a i =>
        let* a' := typecheck_atom be gx lx a in
        let* i' := typecheck_atom be gx lx i in
        let ta := typof_atom a' in
        let ti := typof_atom i' in
        let* (ty, ly) := typecheck_array_get2 arch ta ti in
        ret (AArrayGet a' i' ly ty)
    | Syntax.ARecordProj a f =>
        let* a' := typecheck_atom be gx lx a in
        let ta := typof_atom a' in
        let* (ty, ly) := typecheck_record_proj2 be ta f in
        ret (ARecordProj a' f ly ty)
    end.

  (* Fixpoint typecheck_access (be: benv) (gx: gcontext) (lx: lcontext) (ty: btyp) (acs: list Syntax.access) : res (btyp * list Syntax.Typed.access) :=
    match acs with
    | nil => ret (ty, nil)
    | ac :: acs' =>
        match ac with
        | Syntax.AcRecordField f =>
            let* (ty', ly) := typecheck_record_proj2 be ty f in
            let* (r, lr) := typecheck_access be gx lx ty' acs' in
            ret (r, (AcRecordField f ty' ly) :: lr)
        | Syntax.AcArrayIndex ai =>
            let* ai' := typecheck_atom be gx lx ai in
            let* (ty', ly) := typecheck_array_get2 arch ty (typof_atom ai') in
            let* (r, lr) := typecheck_access be gx lx ty' acs' in
            ret (r, (AcArrayIndex ai' ty' ly) :: lr)
        end
    end. *)

  Definition typecheck_comp (be: benv) (gx: gcontext) (lx: lcontext) (c: Syntax.comp) : res Imp1Typed.comp :=
    match c with
    | Syntax.CpAtom a =>
        let* a' := typecheck_atom be gx lx a in
        ret (CpAtom a' (typof_atom a'))
    (* | Syntax.CpArrayGet a1 a2 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* (ty, ly) := typecheck_array_get2 arch ty1 ty2 in
        ret (CpArrayGet a1' a2' ty ly) *)
    | Syntax.CpArraySet a1 a2 a3 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let* a3' := typecheck_atom be gx lx a3 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let ty3 := typof_atom a3' in
        let* ty := typecheck_array_set arch ty1 ty2 ty3 in
        ret (CpArraySet a1' a2' a3' ty)
    (* | Syntax.CpRecordProj a x =>
        let* a' := typecheck_atom be gx lx a in
        let tya := typof_atom a' in
        let* (ty, ly) := typecheck_record_proj2 be tya x in
        ret (CpRecordProj a' x ty ly) *)
    | Syntax.CpRecordUpdate a1 x a2 =>
        let* a1' := typecheck_atom be gx lx a1 in
        let* a2' := typecheck_atom be gx lx a2 in
        let ty1 := typof_atom a1' in
        let ty2 := typof_atom a2' in
        let* ty := typecheck_record_update be ty1 ty2 x in
        ret (CpRecordUpdate a1' x a2' ty)
    (* | Syntax.CpDeepAccess a acs =>
        let* a' := typecheck_atom be gx lx a in
        let* (t, acs') := typecheck_access be gx lx (typof_atom a') acs in
        ret (CpDeepAccess a' acs' t) *)
    | Syntax.CpCall f args =>
        let* tf := typof_var gx lx f in
        let* args' := mmap (typecheck_atom be gx lx) args in
        let targs := map typof_atom args' in
        let* ty := typecheck_call tf targs in
        ret (CpCall f tf args' ty)
    end.

  (* Should be checked if the context contains the same set of set variables. ? *)
  Definition merge_contexts (lx1 lx2: lcontext) : res lcontext :=
    STree.fold
      (fun acc k v =>
        let* acc := acc in
        lcontext_update acc k v)
      lx2
      (ret lx1).

  Fixpoint typecheck_statement (be: benv) (gx: gcontext) (lx: lcontext) (tret: btyp) (s: Imp1.statement) : res (Imp1Typed.statement * lcontext) :=
    let fix typecheck_match_rec (be: benv) (gx: gcontext) (lx: lcontext) (te: btyp) (tret: btyp) (elems: list ident) (unmatched: list ident)
      (cases: list (pattern * Imp1.statement)) : res (list (pattern * Imp1Typed.statement) * lcontext) :=
      match cases with
      | nil => fail
      | (x, sx) :: nil =>
          let* unmatched' := typecheck_pattern be te elems x unmatched in
          if list_is_empty unmatched' then
            let* (sx', lx') := typecheck_statement be gx lx tret sx in
            ret (((x, sx') :: nil), lx')
          else
            failwith "Imp1.Typing.typecheck_match_rec: non-exhaustive pattern-matching"
      | (x, sx) :: ((_ :: _) as cases') =>
          let* unmatched' := typecheck_pattern be te elems x unmatched in
          let* (sx', lx') := typecheck_statement be gx lx tret sx in
          let* (cases_typed, lxr) := typecheck_match_rec be gx lx te tret elems unmatched' cases' in
          let* lxm := merge_contexts lx' lxr in
          ret (((x, sx') :: cases_typed), lxm)
      end
    in
    let typecheck_match (be: benv) (gx: gcontext) (lx: lcontext) (tret: btyp) (ty: btyp)
      (cases: list (pattern * Imp1.statement)) : res (list (pattern * Imp1Typed.statement) * lcontext) :=
      match ty with
      | BEnum te =>
          let* elems := TEnv.get_edef be te in
          typecheck_match_rec be gx lx ty tret elems elems cases
      | _ => failwith "Imp1.Typing.typecheck_match: enum type expected"
      end
    in
    match s with
    | Imp1.StSet x c =>
        let* c' := typecheck_comp be gx lx c in
        let* lx' := lcontext_update lx x (typof_comp c') in
        ret (StSet x c', lx')
    | Imp1.StIfThenElse a s1 s2 =>
        let* (s1', lx1) := typecheck_statement be gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement be gx lx tret s2 in
        let* a' := typecheck_atom be gx lx a in
        match typof_atom a' with
        | BBool =>
            let* lx' := merge_contexts lx1 lx2 in
            ret (StIfThenElse a' s1' s2', lx')
        | _ => failwith "Imp1.Typing.typecheck_statement: atom of type bool expected"
        end
    | Imp1.StSwitch a cases =>
        let* a' := typecheck_atom be gx lx a in
        let* (cases_typed, lx') := typecheck_match be gx lx tret (typof_atom a') cases in
        ret (StSwitch a' cases_typed, lx')
    | Imp1.StSequence s1 s2 =>
        let* (s1', lx1) := typecheck_statement be gx lx tret s1 in
        let* (s2', lx2) := typecheck_statement be gx lx1 tret s2 in
        ret (StSequence s1' s2', lx2)
    | Imp1.StReturn a =>
        let* a' := typecheck_atom be gx lx a in
        let ty := typof_atom a' in
        if btyp_eq_dec ty tret then
          ret (StReturn a', lx)
        else
          failwith "Imp1.Typing.typecheck_statement: return type mismatch"
    | Imp1.StAttr a s =>
        let* (s',lx') := typecheck_statement be gx lx tret s in
        ret (StAttr a s',lx')
    end.

  Definition typecheck_function (be: benv) (gx: gcontext) (f: Imp1.function) : res Imp1Typed.function :=
    let* lx :=
      list_fold_left_err
        (fun acc '(x, tx) => lcontext_update acc x tx)
        (fn_params f)
        (ret STree.empty)
    in
    let* (body, _) := typecheck_statement be gx lx (fn_return f) (fn_body f) in
    ret {|
      fn_return := fn_return f;
      fn_params := fn_params f;
      fn_body := body
    |}.
  
  Fixpoint typecheck_globdefs_rec (be: benv) (gx: gcontext) (defs: list Imp1.globdef) : res (list Imp1Typed.globdef) :=
    match defs with
    | nil => ret nil
    | d :: defs' =>
        match d with
        | DefConst x l ty =>
            let* l' := typecheck_literal be l in
            if btyp_eq_dec ty (typof_literal l') then
              let* gx := gcontext_update gx x ty in
              let* rd := typecheck_globdefs_rec be gx defs' in
              ret (DefConst x l' ty :: rd)
            else
              failwith "Imp1.Typing.typecheck_globdefs: type mismatch in constant definition"
        | DefFun x f =>
            let* f' := typecheck_function be gx f in
            let* gx := gcontext_update gx x (mk_fun_btyp (fn_params f') (fn_return f')) in
            let* rd := typecheck_globdefs_rec be gx defs' in
            ret (DefFun x f' :: rd)
        | DeclConst x ty =>
            let* gx := gcontext_update gx x ty in
            let* rd := typecheck_globdefs_rec be gx defs' in
            ret (DeclConst x ty :: rd)
        | DeclFun x tparams tret =>
            let* gx := gcontext_update gx x (mk_fun_btyp tparams tret) in
            let* rd := typecheck_globdefs_rec be gx defs' in
            ret (DeclFun x tparams tret :: rd)
        end
    end.

  Definition typecheck_globdefs (be: benv) (defs: list Imp1.globdef) : res (list Imp1Typed.globdef) :=
    typecheck_globdefs_rec be STree.empty defs.

  Definition typecheck_program (prog: Imp1.program) : res Imp1Typed.program :=
    let* be := TEnv.build (prog_types prog) in
    let* defs := typecheck_globdefs be (prog_defs prog) in
    ret {|
      prog_defs := defs;
      prog_types := prog_types prog;
      prog_tabs := prog_tabs prog;
    |}.

  End ARCHI.

End Typing.

Module Imp1Typing := Imp1.Typing.
