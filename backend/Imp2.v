From Stdlib Require Import List.
From compcert Require Import Integers Maps.
From BarocqComp Require Import Types Syntax Benum Pp Printer.

(** * Abstract syntax *)

(** ** Types *)

Inductive typ2 : Type :=
  | TVoid : typ2
  | TBool : typ2
  | TInt32 : signedness -> typ2
  | TInt64 : signedness -> typ2
  | TArray : typ2 -> layout -> typ2
  | TEnum : ident -> typ2
  | TRecord : ident -> list ident -> typ2
  | TFun : list typ2 -> typ2 -> typ2
  | TAbs : ident -> typ2.

(** ** Literals *)

Inductive literal :=
  | LTrue : literal
  | LFalse : literal
  | LInt32 : int -> signedness -> literal
  | LInt64 : int64 -> signedness -> literal
  | LVar : ident -> typ2 -> literal
  | LArray : list literal -> typ2 -> layout -> literal
  | LRecord : list (ident * literal) -> list ident -> ident -> literal.

Definition typof_literal (l: literal) : typ2 :=
  match l with
  | LTrue
  | LFalse => TBool
  | LInt32 _ s => TInt32 s
  | LInt64 _ s => TInt64 s
  | LVar _ ty => ty
  | LArray _ ta ly => TArray ta ly
  | LRecord _ ub rid => TRecord rid ub
  end.

(** ** Atoms *)

Inductive atom :=
  | ATrue : atom
  | AFalse : atom
  | AInt32 : int -> signedness -> atom
  | AInt64 : int64 -> signedness -> atom
  | AConstr : ident -> int -> typ2 -> atom
  | AVar : ident -> typ2 -> atom
  | ACast : atom -> typ2 -> atom
  | AUnaryOp : unary_op -> atom -> typ2 -> atom
  | ABinaryOp : binary_op -> atom -> atom -> typ2 -> atom
  | AArrayGet : atom -> atom -> layout -> typ2 -> atom
  | ARecordProj : atom -> ident -> layout -> typ2 -> atom
  | APureCall : ident -> typ2 -> list atom -> typ2 -> atom.

Definition typof_atom (a: atom) : typ2 :=
  match a with
  | ATrue
  | AFalse => TBool
  | AInt32 _ s => TInt32 s
  | AInt64 _ s => TInt64 s
  | AConstr _ _ ty
  | AVar _ ty
  | ACast _ ty
  | AUnaryOp _ _ ty
  | ABinaryOp _ _ _ ty
  | AArrayGet _ _ _ ty
  | ARecordProj _ _ _ ty
  | APureCall _ _ _ ty => ty
  end.

(** ** "Effectul" computations *)

Inductive ecomp : Type :=
  | EcArraySet : atom -> atom -> atom -> ecomp
  | EcRecordUpdate : atom -> ident -> atom -> ecomp.

(** ** Statements *)

Inductive statement : Type :=
  | StSkip : statement
  | StSet : ident -> atom -> statement
  | StEcomp : ecomp -> statement
  | StCall : option ident -> ident -> typ2 -> list atom -> typ2 -> statement
  | StIfThenElse : atom -> statement -> statement -> statement
  | StSwitch : atom -> list (pattern * statement) -> statement
  | StSequence : statement -> statement -> statement
  | StReturn : option atom -> statement.

(** ** Functions *)

Definition function : Type := Syntax.function statement typ2.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef statement typ2 literal.

(** ** Programs *)

Definition program : Type := Syntax.program statement typ2 literal.

Module Pp.
  Import String.
  Import ListNotations.

  Fixpoint pp_typ2 (t:typ2) : box :=
    match t with
    | TVoid => Bstr "void"
    | TBool => Bstr "bool"
    | TInt32 s => if s then Bstr "i32" else Bstr "u32"
    | TInt64 s => if s then Bstr "i64" else Bstr "u64"
    | TArray ty _ => Pp.seq (Bstr "[" :: pp_typ2 ty :: Bstr "]" :: nil)
    | TEnum id    => Bcat (Bstr "enum ") (Bstr id)
    | TRecord id _ => Bcat (Bstr "record ") (Bstr id)
    | TFun args r => Pp.seq (Bstr "(" :: pp_list (Bstr ", ") pp_typ2 args :: Bstr ") -> " :: pp_typ2 r :: nil)
    | TAbs id   => Bcat (Bstr "abs ") (Bstr id)
    end.

  Fixpoint pp_atom (a:atom) : box :=
    match a with
    | ATrue =>  Bstr "true"
    | AFalse => Bstr "false"
    | AInt32 i s => pp_sint s i
    | AInt64 i s => pp_sint64 s i
    | AConstr s _ _ =>  Bstr s
    | AVar s _     => Bstr s
    | ACast a0 bt => seq [pp_atom a0; Bstr " as "; pp_typ2 bt]
    | AUnaryOp o a0 _ => Bcat (Bstr (string_of_unary_op o)) (pp_atom a0)
    | ABinaryOp o a1 a2 _ =>
        Pp.seq ((pp_atom a1) :: Bstr " " :: Bstr (string_of_binary_op o)
          :: Bstr " " :: (pp_atom a2) :: nil)
    | AArrayGet a0 i _ _ => Bcat (pp_atom a0) (array_index pp_atom i)
    | ARecordProj a0 i _ _ => Bcat (pp_atom a0) (Bcat (Bstr ".") (Bstr i))
    | APureCall f _ l _ => seq [Bstr f; Bstr "("; pp_list (Bstr ", ") pp_atom l; Bstr ")"]
    end.

  Definition pp_ecomp  (ec:ecomp) :=
    match ec with
    | EcArraySet a i v =>
        Bcat (pp_atom a)
          (Bcat
             (Bcat (array_index pp_atom i)
                (Bstr "<-")) (pp_atom v))
    | EcRecordUpdate a f v => Bcat (pp_atom a)
                              (Bcat
                                  (Bcat (Bcat (Bstr ".") (Bstr f)) (Bstr "<-"))
                                  (pp_atom v))
  end.

  Definition pp_opt_ident (o:option ident) :=
    match o with
    | None => Bstr "()"
    | Some id => Bstr id
    end.

  Definition pp_option_atom (o:option atom) :=
    match o with
    | None => Bstr "()"
    | Some a => pp_atom a
    end.

  Fixpoint pp_statement (s:statement) :=
    match s with
    | StSkip    => Bstr "skip"
    | StSet i c => Bcat (Bstr i) (Bcat (Bstr " := ") (pp_atom c))
    | StEcomp e  => pp_ecomp e
    | StCall r f _ l _ => seq [pp_opt_ident r ; Bstr " := ";Bstr f; Bstr "("; pp_list (Bstr ", ") pp_atom l; Bstr ")"]
    | StIfThenElse a s1 s2 =>
        let s1 := Bcat (Bstr "then ") (pp_statement s1) in
        let s2 := Bcat (Bstr "else ") (pp_statement s2) in
        let c  := pp_atom a in
        let cd := Bcat (Bstr "if ") c in
        Bstack cd (Bstack s1 s2 Left) Left
    | StSwitch a l => pp_match pp_atom pp_statement "case " a l
    | StSequence s1 s2 =>
        let s1 := pp_statement s1 in
        let s2 := pp_statement s2 in
        Bstack (suffix_nocat s1 ";") s2 Left
    | StReturn a => Bcat (Bstr "return ") (pp_option_atom a)
    end.

  Fixpoint pp_literal (l:literal) : box :=
    match l with
    | LTrue  => Bstr "true"
    | LFalse => Bstr "false"
    | LInt32 i _ => pp_int i
    | LInt64 i _ => pp_int64 i
    | LVar id ty => Bstr id
    | LArray l0 _ _ => Bcat (Bstr "[") (Bcat (pp_list (Bstr ", ") pp_literal l0) (Bstr ",]"))
    | LRecord l0 _ _ =>
        Bcat (Bstr "{") (Bcat (pp_list (Bstr ", ") (pp_pair (Bstr " = ") Bstr pp_literal) l0) (Bstr ",}"))
    end.

  Definition pp_program (p:program) := Printer.pp_program  pp_typ2 pp_literal pp_statement  p.

End Pp.
