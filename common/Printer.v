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

Definition string_of_nat (n:nat) := string_of_Z (Z.of_nat n).

Definition pp_int (i:Integers.Int.int) : box :=
  Bstr (string_of_Z (Integers.Int.unsigned i)).

Definition pp_int64 (i:Integers.Int64.int) : box :=
  Bstr (string_of_Z (Integers.Int64.unsigned i)).

Definition pp_sint (s:signedness) (i:Integers.Int.int) : box :=
  if s
  then pp_int i
  else Bcat (pp_int i) (Bstr "U").

Definition pp_sint64 (s:signedness) (i:Integers.Int64.int) : box :=
  if s
  then Bcat (pp_int64 i) (Bstr "L")
  else Bcat (pp_int64 i) (Bstr "UL").


Definition pp_signedness (s:signedness) :=
  match s with
  | Signed => Bemp
  | Unsigned => Bstr "u"
  end.


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

Import Types.

Fixpoint pp_btyp (bt: btyp) :=
  match bt with
  | BBool => Bstr "bool"
  | BInt32 s => if s then Bstr "i32" else Bstr "u32"
  | BInt64 s => if s then Bstr "i64" else Bstr "u64"
  | BArray bt ly => Pp.seq (Bstr "[" :: pp_btyp bt :: Bstr "]" :: nil)
  | BEnum id => Bcat (Bstr "enum ") (Bstr id)
  | BRecord id _ => Bcat (Bstr "record ") (Bstr id)
  | BFun args r  => Bcat (pp_list (Bstr " -> ") pp_btyp args) (pp_btyp r)
  | BAbs id      => Bcat (Bstr "abs ") (Bstr id)
  end.


(* Fixpoint pp_atom (a:atom) :=
  match a with
  | ATrue => Bstr "true"%string
  | AFalse => Bstr "false"%string
  | AInt32 i s => pp_sint s i
  | AInt64 i s => pp_sint64 s i
  | AConstr s  => Bstr s
  | AVar s     => Bstr s
  | ACast a bt   => Pp.seq (pp_atom a :: Bstr " as " :: pp_btyp bt :: nil)
  | AUnaryOp o a => Bcat (Bstr (string_of_unary_op o)) (pp_atom a)
  | ABinaryOp o a1 a2 => Bcat (pp_atom a1)
                             (Bcat (Bstr (string_of_binary_op o)) (pp_atom a2))
  | AArrayGet a i  => Bcat (pp_atom a )
                           (array_index pp_atom i)
  | ARecordProj a i => Bcat (pp_atom a)
                         (Bcat (Bstr ".") (Bstr i))
  | APureCall f l => Pp.seq (Bstr f :: Bstr "(" :: pp_list (Bstr ", ") pp_atom l
                        :: Bstr ")" :: nil)
  end. *)

(* Module Typed.
  Import Typed. *)


Fixpoint pp_atom (a:atom) :=
  match a with
  | ATrue => Bstr "true"%string
  | AFalse => Bstr "false"%string
  | AInt32 i s => pp_sint s i
  | AInt64 i s => pp_sint64 s i
  | AConstr s  _ _ => Bstr s
  | AVar s _     => Bstr s
  | ACast a bt   => Pp.seq (pp_atom a :: Bstr " as " :: pp_btyp bt :: nil)
  | AUnaryOp o a _ => Bcat (Bstr (string_of_unary_op o)) (pp_atom a)
  | ABinaryOp o a1 a2 _ => Bcat (pp_atom a1)
                            (Bcat (Bstr (string_of_binary_op o)) (pp_atom a2))
  | AArrayGet a i _ _ => Bcat (pp_atom a )
                                (array_index pp_atom i)
  | ARecordProj a i _ _ => Bcat (pp_atom a)
                            (Bcat (Bstr ".") (Bstr i))
  | APureCall f _ l _ => Pp.seq (Bstr f :: Bstr "(" :: pp_list (Bstr ", ") pp_atom l
                            :: Bstr ")" :: nil)
  end.

Definition pp_comp (c:comp) :=
  match c with
  | CpAtom a => pp_atom a
  | CpRecordUpdate a f v _ => Bcat (pp_atom a)
                              (Bcat
                                  (Bcat (Bcat (Bstr ".") (Bstr f)) (Bstr "<-"))
                                  (pp_atom v))
  | CpArraySet a i v _    => Bcat (pp_atom a)
                                    (Bcat
                                        (Bcat (array_index pp_atom i)
                                          (Bstr "<-")) (pp_atom v))
  | CpCall f _ l _ => Pp.seq (Bstr f :: Bstr "(" :: pp_list (Bstr ", ") pp_atom l
                        :: Bstr ")" :: nil)
end.

(* End Typed. *)

Definition pp_attr (a:param_attr) :=
  match a with
  | AttrReadonly => (Bstr "+r")
  | AttrWrite    => (Bstr "+w!")
  | AttrNone     => (Bstr "+w")
  end.

Definition pp_globdef {B T L:Type} (pp_lit :  L -> box) (pp_fct : ident -> function B T -> box) (pp_typ : T -> box) (gd:globdef B T L) :=
  match gd with
  | DefConst id l t => Pp.seq (Bstr "defn ":: Bstr id :: Bstr " : " :: pp_typ t :: Bstr " := " :: pp_lit l :: nil)
  | DefFun   id  f  => (pp_fct id f)
  | DeclConst id t  => Pp.seq  (Bstr "defn "::Bstr id :: Bstr " : " :: pp_typ t :: nil)
  | DeclFun id l t  => Pp.seq  (Bstr "defn ":: Bstr id :: Bstr " : " ::
                                  (pp_list  (Bstr " -> ") (pp_pair (Bstr ",") pp_attr pp_typ) l)
                                   :: Bstr " -> " :: pp_typ t :: nil)
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


Definition pp_layout (p:layout) :=
  match p with
  | LyPrim => Bstr "p"
  | LyBoxed  => Bstr "b"
  | LyUnboxed z => pp_option (fun z => Bstr (string_of_Z z)) z
  end.

Definition pp_program {B T:Type} (pp_typ : T -> box) (pp_body : B -> box)
  (p:program B T literal) : box :=
    Pp.stack Left (List.map (Printer.pp_globdef Printer.pp_literal (pp_function pp_body pp_typ) pp_typ) p.(prog_defs)).
