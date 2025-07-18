From compcert Require Import Ctypes Integers.
From BarocqComp Require Import Array Utils Types Syntax.

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
    | ELetIn : ident -> expr -> expr -> expr.

  (** ** Functions *)

  Definition function : Type := Syntax.function expr.

  (** ** Global definitions *)

  Definition globdef : Type := Syntax.globdef literal function.

  (** ** Programs *)

  Record program : Type := mk_program {
    prog_defs : list globdef;
    prog_types : list type_def
  }.

End BNF.

Module Monadic.

  (** * Typed abstract syntax for monadic shallow-embedded programs *)

  (** ** Types *)

  Inductive mtyp : Type :=
    | MBool : mtyp
    | MInt32 : signedness -> mtyp
    | MInt64 : signedness -> mtyp
    | MArray : mtyp -> mtyp
    | MRecord : ident -> mtyp
    | MFun : list mtyp -> mtyp -> mtyp
    | MAbs : ident -> mtyp
    | MRes : mtyp -> mtyp.

  (** Literals *)

  Inductive literal :=
    | LTrue : mtyp -> literal
    | LFalse : mtyp -> literal
    | LInt32 : int -> mtyp -> literal
    | LInt64 : int64 -> mtyp -> literal
    | LArray : array literal -> mtyp -> literal
    | LRecord : list (ident * literal) -> mtyp -> literal.

  (** ** Atoms *)

  Inductive atom :=
    | ATrue : mtyp -> atom
    | AFalse : mtyp -> atom
    | AInt32 : int -> mtyp -> atom
    | AInt64 : int64 -> mtyp -> atom
    | AVar : ident -> mtyp -> atom
    | ACast : atom -> mtyp -> atom
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
    | ELetIn : ident -> expr -> expr -> mtyp -> expr
    | ELetMon : ident -> expr -> expr -> mtyp -> expr
    | ERet : expr -> mtyp -> expr.

  (** ** Functions *)

  Record function : Type := mk_function {
    fn_return: mtyp;
    fn_params: list (ident * mtyp);
    fn_body: expr
  }.

  (** ** Global definitions *)

  Inductive globdef : Type :=
    | DefConst : ident -> literal -> mtyp -> globdef
    | DefFun : ident -> function -> globdef
    | DeclConst : ident -> mtyp -> globdef
    | DeclFun : ident -> list (param_attr * mtyp) -> mtyp -> globdef.

  (** ** Programs *)

  Record record_def := mk_record_def {
    rd_name : ident;
    rd_fields : list (ident * mtyp)
  }.

  Inductive type_def : Type :=
    | TdRecord : record_def -> type_def
    | TdAbstract : ident -> struct_or_union -> type_def. 

  Record program : Type := mk_program {
    prog_defs : list globdef;
    prog_types : list type_def
  }.

  Definition get_record_defs (types: list type_def) : list record_def :=
    List.fold_right
      (fun td acc =>
        match td with
        | TdRecord rd => cons rd acc
        | _ => acc
        end)
      nil
      types.

End Monadic.