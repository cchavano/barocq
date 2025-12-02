From BarocqComp Require Import Types Syntax Benum.
From BarocqComp Require Pp Printer.

(** * Abstract syntax *)

(** ** Literals *)

Definition literal : Type := Syntax.literal.

(** ** Atoms *)

Definition atom : Type := Syntax.atom.

(** ** Expressions *)

Inductive expr : Type :=
  | EAtom : atom -> expr
  (* | EArrayGet : atom -> atom -> expr *)
  | EArraySet : atom -> atom -> atom -> expr
  (* | ERecordProj : atom -> ident -> expr *)
  | ERecordUpdate : atom -> ident -> atom -> expr
  (* | EDeepAccess : atom -> list access -> expr *)
  | EApp : atom -> list atom -> expr
  | EIfThenElse : atom -> expr -> expr -> expr
  | EMatch : atom -> list (pattern * expr) -> expr
  | ELetIn : ident -> expr -> expr -> expr
  | EAttr  : ident -> expr -> expr.

(** ** Functions *)

Definition function : Type := Syntax.function expr btyp.

(** ** Global definitions *)

Definition globdef : Type := Syntax.globdef literal function btyp.

(** ** Programs *)

Definition program : Type := Syntax.program globdef field_descr.

Module Pp.
  Import Pp.
  Import String.

  Fixpoint pp_expr (e:expr) : box :=
    match e with
    | EAtom a => Printer.pp_atom a
    | EArraySet a i v => Pp.seq (Printer.pp_atom a :: Bstr "[" :: Printer.pp_atom i :: Bstr "] <- " :: Printer.pp_atom v :: nil)
    | ERecordUpdate a fd v => Pp.seq (Printer.pp_atom a :: Bstr "." :: Bstr fd :: Bstr " <- " :: Printer.pp_atom v :: nil)
    | EApp a l => Pp.seq (Printer.pp_atom a :: Bstr "(" :: pp_list (Bstr ", ") Printer.pp_atom l :: Bstr ")" :: nil)
    | EMatch a l => Bstr "match ... "
    | EIfThenElse c t e => Bstack
                             (Bcat (Bstr "if ") (Printer.pp_atom c))
                             (Bstack (Bcat (Bstr "then ") (pp_expr t))
                                     (Bcat (Bstr "else ") (pp_expr e)) Left) Left
    | ELetIn id e1 e2 => Bcat (Bstr "let") (Bstack (Pp.seq (Bstr id :: Bstr " := " :: pp_expr e1 :: Bstr " in " :: nil))
                                              (pp_expr e2) Left)
    | EAttr id e => Pp.seq (Bstr "#[ " :: Bstr id :: Bstr " ]"  :: pp_expr e :: nil)
    end.

  Definition pp_program (p:program) : box :=
    Printer.pp_program Printer.pp_btyp  pp_expr p.

End Pp.
