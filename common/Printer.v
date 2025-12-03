(** Printing for programs *)
From BarocqComp Require Import Pp.
From Coq Require Import String List ZArith.
From BarocqComp Require Import Syntax.
From BarocqComp Require Import Unsigned63 Types.
Open Scope string.


Fixpoint appendl (l:list string) : string :=
  match l with
  | nil => ""
  | e::l => append e (appendl l)
  end.

Definition string_of_positive (p:positive) := string_of_Z (Zpos p).

Definition pp_int (i:Integers.Int.int) : box :=
  Bstr (string_of_Z (Integers.Int.unsigned i)).

Definition pp_int64 (i:Integers.Int64.int) : box :=
  Bstr (string_of_Z (Integers.Int64.unsigned i)).

Definition pp_signedness (s:signedness) :=
  match s with
  | Signed => Bstr "s"
  | Unsigned => Bstr "u"
  end.

Definition pp_sint (s:signedness) (i:Integers.Int.int) : box :=
  Bcat (pp_signedness s) (pp_int i).

Definition pp_sint64 (s:signedness) (i:Integers.Int64.int) : box :=
  Bcat (pp_signedness s) (pp_int64 i).


Definition array_index {A: Type} (f:A -> box) (v:A) :=
  Bcat (Bstr "[") (Bcat (f v) (Bstr "]")).

Definition pp_arrow_typ {T:Type} (pp_typ : T -> box) (args : list (ident * T)) (ret :T) :=
  let pp_arg x := Pp.seq (Bstr "(" :: pp_pair  (Bstr ":") Bstr pp_typ x :: Bstr ")" :: nil) in
  Pp.seq
    (pp_list (Bstr " -> ") pp_arg args  :: Bstr " -> " :: pp_typ ret :: nil).

Definition pp_function {B T: Type}  (pp_body: B -> box) (pp_typ : T -> box) (id:ident) (f:function B T) : box :=
  Bstack
    (Pp.seq  (Bstr "defn " :: Bstr id :: Bstr " : " :: pp_arrow_typ pp_typ f.(fn_params) f.(fn_return) :: Bstr " := " :: nil))
    (Bcat (Bstr "     ") (pp_body f.(fn_body))) Left.

Definition string_of_unary_op (o:unary_op) :=
  match o with
  | UopNotbool => "!"
  | UopNotint  => "~"
  | UopNeg     => "-"
  | UopPlus    => "+"
  end.

Definition string_of_binary_op (o:binary_op) :=
  match o with
  | BopAndbool => "&&"
  | BopOrbool  => "||"
  | BopXorbool => "xor"
  | BopAdd     => "+"
  | BopSub     => "-"
  | BopMul     => "*"
  | BopDiv     => "/"
  | BopMod     => "mod"
  | BopAndint  => "&"
  | BopOrint   => "|"
  | BopXorint  => "^"
  | BopShl     => "<<"
  | BopShr     => ">>"
  | BopEq      => "="
  | BopNeq     => "!="
  | BopLt      => "<"
  | BopGt      => ">"
  | BopLe      => "<="
  | BopGe      => ">="
  end.

Fixpoint pp_atom (a:atom) :=
  match a with
  | ATrue => Bstr "true"%string
  | AFalse => Bstr "false"%string
  | AInt32 i _ => Bstr "int"%string
  | AInt64 i _ => Bstr "int64"%string
  | AConstr s  => Bstr s
  | AVar s     => Bstr s
  | ACast a bt   => Bcat (Bstr "(btyp)"%string) (pp_atom a)
  | AUnaryOp o a => Bcat (Bstr (string_of_unary_op o)) (pp_atom a)
  | ABinaryOp o a1 a2 => Bcat (pp_atom a1)
                             (Bcat (Bstr (string_of_binary_op o)) (pp_atom a2))
  | AArrayGet a i  => Bcat (pp_atom a )
                           (array_index pp_atom i)
  | ARecordProj a i => Bcat (pp_atom a)
                         (Bcat (Bstr ".") (Bstr i))
  end.

Module Typed.
  Import Typed.

  Fixpoint pp_atom (a:atom) :=
    match a with
    | ATrue => Bstr "true"%string
    | AFalse => Bstr "false"%string
    | AInt32 i _ => Bstr "int"%string
    | AInt64 i _ => Bstr "int64"%string
    | AConstr s  _ => Bstr s
    | AVar s _     => Bstr s
    | ACast a bt   => Bcat (Bstr "(btyp)"%string) (pp_atom a)
    | AUnaryOp o a _ => Bcat (Bstr (string_of_unary_op o)) (pp_atom a)
    | ABinaryOp o a1 a2 _ => Bcat (pp_atom a1)
                             (Bcat (Bstr (string_of_binary_op o)) (pp_atom a2))
    | AArrayGet a i _ _ => Bcat (pp_atom a )
                                 (array_index pp_atom i)
    | ARecordProj a i _ _ => Bcat (pp_atom a)
                              (Bcat (Bstr ".") (Bstr i))
    end.

  Definition pp_comp (c:comp) :=
    match c with
    | CpAtom a _ => pp_atom a
    | CpRecordUpdate a f v _ => Bcat (pp_atom a)
                                (Bcat
                                   (Bcat (Bcat (Bstr ".") (Bstr f)) (Bstr "<-"))
                                   (pp_atom v))
    | CpArraySet a i v _    => Bcat (pp_atom a)
                                      (Bcat
                                         (Bcat (array_index pp_atom i)
                                            (Bstr "<-")) (pp_atom v))
    | CpCall f _ l _ => Bcat (Bstr f) (Bcat (Bstr "(")
                                          (Bstr ")"))
  end.

End Typed.

Definition pp_attr (a:param_attr) :=
  match a with
  | AttrReadonly => (Bstr "+r")
  | AttrWrite    => (Bstr "+w!")
  | AttrNone     => (Bstr "+w")
  end.

Definition pp_globdef {L F T:Type} (pp_lit :  L -> box) (pp_fct : ident -> F -> box) (pp_typ : T -> box) (gd:globdef L F T) :=
  match gd with
  | DefConst id l t => (Bcat (Bstr id)
                          (Bcat (Bcat (Bstr " : ") (pp_typ t)) (Bcat (Bstr " := ") (pp_lit l))))
  | DefFun   id  f  => (pp_fct id f)
  | DeclConst id t  => (Bcat (Bstr id) (Bcat (Bstr " : ") (pp_typ t )))
  | DeclFun id l t  => (Bcat (Bstr id) (Bcat (Bstr " : ") (Bcat (pp_list  (Bstr " -> ") (pp_pair (Bstr ",") pp_attr pp_typ) l)
                                                             (Bcat (Bstr " -> ") (pp_typ t)))))
  end.

Fixpoint pp_literal (l:literal) :=
  match l with
  | LTrue => Bstr "true"
  | LFalse => Bstr "false"
  | LInt32 i s => pp_int i
  | LInt64 i s => pp_int64 i
  | LArray l bt _ => Bcat (Bstr "[| ") (Bcat (pp_list (Bstr ";") pp_literal l) (Bstr " |]"))
  | LRecord l _ _ => Bcat (Bstr "{| ")  (Bcat (pp_list (Bstr ";") (pp_pair (Bstr ":") Bstr pp_literal) l) (Bstr " |}"))
  end.

Import Types.

Fixpoint pp_btyp (bt: btyp) :=
  match bt with
  | BBool => Bstr "bool"
  | BInt32 s => Bcat (pp_signedness s) (Bstr "int32")
  | BInt64 s => Bcat (pp_signedness s) (Bstr "int64")
  | BArray bt ly => Bcat (pp_btyp bt) (Bstr "[]")
  | BEnum id => Bcat (Bstr "enum ") (Bstr id)
  | BRecord id _ => Bcat (Bstr "record ") (Bstr id)
  | BFun args r  => Bcat (pp_list (Bstr " -> ") pp_btyp args) (pp_btyp r)
  | BAbs id      => Bcat (Bstr "abs ") (Bstr id)
  end.

Definition pp_layout (p:layout) :=
  match p with
  | LyPrim => Bstr "p"
  | LyBoxed  => Bstr "b"
  | LyUnboxed z => pp_option (fun z => Bstr (string_of_Z z)) z
  end.



Definition pp_program {T U body:Type} (pp_typ : T -> box) (pp_body : body -> box)
  (p:program (globdef literal (function body T) T) U) : box :=
    pp_list (Bstr nl) (Printer.pp_globdef Printer.pp_literal (pp_function pp_body pp_typ) pp_typ) p.(prog_defs).
