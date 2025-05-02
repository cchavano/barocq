From compcert Require Import Integers.
From BarocqComp Require Import Utils Array Ident Types.

(** * Identfitiers *)

Definition ident : Type := Ident.t.

(* Definition ident : Type := Ident.Extended.t. *)

(** * Constant literals *)

Inductive literal :=
  | LTrue : literal
  | LFalse  : literal
  | LInt32 : int -> signedness -> literal
  | LInt64 : int64 -> signedness -> literal
  | LArray : array literal -> literal
  | LStruct : list (ident * literal) -> ident -> literal.

(** * Operators *)

Inductive unary_op : Type :=
  | UopNotbool : unary_op
  | UopNotint : unary_op
  | UopNeg : unary_op
  | UopPlus: unary_op.

Inductive binary_op : Type :=
  | BopAndbool : binary_op
  | BopOrbool : binary_op
  | BopXorbool : binary_op
  | BopAdd : binary_op
  | BopSub : binary_op
  | BopMul : binary_op
  | BopDiv : binary_op
  | BopMod : binary_op
  | BopAndint : binary_op
  | BopOrint : binary_op
  | BopXorint : binary_op
  | BopShl : binary_op
  | BopShr : binary_op
  | BopEq : binary_op
  | BopNeq : binary_op
  | BopLt : binary_op
  | BopGt : binary_op
  | BopLe : binary_op
  | BopGe : binary_op.

(** * Atoms *)

(** Atoms are pure computations in C *)

Inductive atom : Type :=
  | ATrue : atom
  | AFalse : atom
  | AInt32 : int -> signedness -> atom
  | AInt64 : int64 -> signedness -> atom
  | AVar : ident -> atom
  | ACast : atom -> ctyp -> atom
  | AUnaryOp : unary_op -> atom -> atom
  | ABinaryOp : binary_op -> atom -> atom -> atom.

(** Deep accesses with atomics array indexes. *)

Inductive access : Type :=
  | AcStructField : ident -> access
  | AcArrayIndex : atom -> access.

(** * Computations with atomic operands *)

Inductive comp : Type := 
  | CpAtom : atom -> comp
  | CpArrayGet : atom -> atom -> comp
  | CpArraySet : atom -> atom -> atom -> comp
  | CpStructProj : atom -> ident -> comp
  | CpStructUpdate : atom -> ident -> atom -> comp
  | CpDeepAccess : atom -> list access -> comp
  | CpCall : atom -> list atom -> comp.

(** * Typed syntax *)

Module Typed.

  Inductive literal :=
    | LTrue : ctyp -> literal
    | LFalse : ctyp -> literal
    | LInt32 : int -> ctyp -> literal
    | LInt64 : int64 -> ctyp -> literal
    | LArray : array literal -> ctyp -> literal
    | LStruct : list (ident * literal) -> ctyp -> literal.

  Inductive atom :=
    | ATrue : ctyp -> atom
    | AFalse : ctyp -> atom
    | AInt32 : int -> ctyp -> atom
    | AInt64 : int64 -> ctyp -> atom
    | AVar : ident -> ctyp -> atom
    | ACast : atom -> ctyp -> atom
    | AUnaryOp : unary_op -> atom -> ctyp -> atom
    | ABinaryOp : binary_op -> atom -> atom -> ctyp -> atom.

  Inductive access : Type :=
    | AcStructField : ident -> ctyp -> access
    | AcArrayIndex : atom -> ctyp -> access.

  Inductive comp : Type := 
    | CpAtom : atom -> ctyp -> comp
    | CpArrayGet : atom -> atom -> ctyp -> comp
    | CpArraySet : atom -> atom -> atom -> ctyp -> comp
    | CpStructProj : atom -> ident -> ctyp -> comp
    | CpStructUpdate : atom -> ident -> atom -> ctyp -> comp
    | CpDeepAccess : atom -> list access -> ctyp -> comp
    | CpCall : atom -> list atom -> ctyp -> comp.

End Typed.

(** * Functions *)

Record function (B: Type) : Type := mk_function {
  fn_return : ctyp;
  fn_params : list (ident * ctyp);
  fn_body : B
}.

(** * Global definitions *)

Inductive globdef (C F: Type) : Type :=
  | DefConst : ident -> C -> ctyp -> globdef C F
  | DefFun : ident -> F -> globdef C F.

(** * Programs *)

Record struct_def := mk_struct_def {
  sd_name : ident;
  sd_fields : list (ident * ctyp)
}.

Record program (G: Type) : Type := mk_program {
  prog_defs : list G;
  prog_types : list struct_def;
}.

Arguments DefConst {C} {F}.
Arguments DefFun {C} {F}.

Arguments mk_function {B}.
Arguments fn_return {B}.
Arguments fn_params {B}.
Arguments fn_body {B}.

Arguments mk_program {G}.
Arguments prog_defs {G}.
Arguments prog_types {G}.