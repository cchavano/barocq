From compcert Require Import Ctypes Integers.
From BarocqComp Require Import Barray Benum Utils Types Syntax.

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
    | ELetIn : ident -> expr -> expr -> expr.

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
    | ERet : expr -> mtyp -> expr.

  (** ** Functions *)

  Definition function : Type := Syntax.function expr mtyp.

  (** ** Global definitions *)

  Definition globdef : Type := Syntax.globdef literal function mtyp.

  (** ** Programs *)

  Definition record_def : Type := Syntax.record_def mtyp.

  Definition type_def : Type := Syntax.type_def mtyp.

  Definition program : Type := Syntax.program globdef mtyp.

  Definition get_enum_typedefs (types: list type_def) : list enum_def :=
    List.fold_right
      (fun td acc =>
        match td with
        | TdEnum ed => cons ed acc
        | _ => acc
        end)
      nil
      types.

  Definition get_record_typedefs (types: list type_def) : list record_def :=
    List.fold_right
      (fun td acc =>
        match td with
        | TdRecord rd => cons rd acc
        | _ => acc
        end)
      nil
      types.

  Definition get_abstract_typedefs (types: list type_def) : list (ident * struct_or_union) :=
    List.fold_right
      (fun td acc =>
        match td with
        | TdAbstract tid su => cons (tid, su) acc
        | _ => acc
        end)
      nil
      types.

End Monadic.