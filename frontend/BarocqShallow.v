From compcert Require Import Ctypes Integers.
From BarocqComp Require Import Barray Benum Maps2 Utils Types Syntax.

Module BNF.

  (** * Abstract syntax of normalized programs *)

  (** ** Literals *)

  Definition literal : Type := Syntax.literal.

  (** ** Atoms *)

  Inductive atom :=
    | ATrue : atom
    | AFalse : atom
    | AInt32 : int -> signedness -> atom
    | AInt64 : int64 -> signedness -> atom
    | AConstr : ident -> atom
    | AVar : ident -> atom
    | ACast : atom -> btyp -> atom
    | AUnaryOp : unary_op -> atom -> atom
    | ABinaryOp : binary_op -> atom -> atom -> atom
    | ARecordProj : atom -> ident -> atom
    | ARecordUpdate : atom -> ident -> atom -> atom.

  (** ** Expressions *)

  Inductive expr : Type :=
    | EAtom : atom -> expr
    | EArrayGet : atom -> atom -> expr
    | EArraySet : atom -> atom -> atom -> expr
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

  Definition program : Type := Syntax.program globdef btyp.

End BNF.

Module Monadic.

  (** * Typed abstract syntax for monadic shallow-embedded programs *)

  (** ** Types *)

  Inductive mtyp : Type :=
    | MBool : mtyp
    | MInt32 : signedness -> mtyp
    | MInt64 : signedness -> mtyp
    | MArray : mtyp -> mtyp
    | MEnum : ident -> mtyp
    | MRecord : ident -> mtyp
    | MFun : list mtyp -> mtyp -> mtyp
    | MAbs : ident -> mtyp
    | MRes : mtyp -> mtyp.

  (** Literals *)

  Inductive literal :=
    | LTrue : literal
    | LFalse : literal
    | LInt32 : int -> signedness -> literal
    | LInt64 : int64 -> signedness -> literal
    | LArray : array literal -> mtyp -> literal
    | LRecord : list (ident * literal) -> ident -> literal.

  (** ** Atoms *)

  Inductive atom :=
    | ATrue : atom
    | AFalse : atom
    | AInt32 : int -> signedness -> atom
    | AInt64 : int64 -> signedness -> atom
    | AConstr : ident -> mtyp -> atom
    | AVar : ident -> mtyp -> atom
    | ACast : atom -> mtyp -> mtyp -> atom
    | AUnaryOp : unary_op -> atom -> mtyp -> atom
    | ABinaryOp : binary_op -> atom -> atom -> mtyp ->  atom
    | ARecordProj : atom -> ident -> mtyp -> atom
    | ARecordUpdate : atom -> ident -> atom -> mtyp -> atom
    | ALambda : list ident -> atom -> mtyp -> atom
    | ALambdaRet : list ident -> atom -> mtyp -> atom
    | AApp : ident -> list ident -> mtyp -> atom.

  (** ** Expressions *)

  Inductive expr : Type :=
    | EAtom : atom -> mtyp -> expr
    | EArrayGet : atom -> atom -> mtyp -> expr
    | EArraySet : atom -> atom -> atom -> mtyp -> expr
    | EApp : atom -> list atom -> mtyp -> expr
    | EIfThenElse : atom -> expr -> expr -> mtyp -> expr
    | EMatch : atom -> list (pattern * expr) -> mtyp -> expr
    | ELetIn : ident -> expr -> expr -> mtyp -> expr
    | ELetMon : ident -> expr -> expr -> mtyp -> expr
    | ERet : expr -> mtyp -> expr
    | EAttr : ident -> expr -> mtyp -> expr
  .

  (** ** Functions *)

  Definition function : Type := Syntax.function expr mtyp.

  (** ** Global definitions *)

  Definition globdef : Type := Syntax.globdef literal function mtyp.

  (** ** Programs *)

  Definition program : Type := Syntax.program globdef mtyp.

End Monadic.
