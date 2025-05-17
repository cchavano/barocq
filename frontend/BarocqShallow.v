From compcert Require Import Ctypes Integers.
From BarocqComp Require Import Utils Types Syntax.

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
    | AStructProj : atom -> ident -> atom
    | AStructUpdate : atom -> ident -> atom -> atom.

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
    | MStruct : ident -> mtyp
    | MFun : list mtyp -> mtyp -> mtyp
    | MAbs : ident -> mtyp
    | MRes : mtyp -> mtyp.

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
    | AStructProj : atom -> ident -> mtyp -> atom
    | AStructUpdate : atom -> ident -> atom -> mtyp -> atom
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
    | ERet : atom -> mtyp -> expr.

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

  Record struct_def := mk_struct_def {
    sd_name : ident;
    sd_fields : list (ident * mtyp)
  }.

  Inductive type_def : Type :=
    | TdStruct : struct_def -> type_def
    | TdAbstract : ident -> struct_or_union -> type_def. 

  Record program : Type := mk_program {
    prog_defs : list globdef;
    prog_types : list type_def
  }.

  Definition get_struct_defs (types: list type_def) : list struct_def :=
    List.fold_right
      (fun td acc =>
        match td with
        | TdStruct sd => cons sd acc
        | _ => acc
        end)
      nil
      types.

End Monadic.