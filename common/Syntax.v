From compcert Require Import Integers Ctypes.
From BarocqComp Require Import Utils Barray Ident Types Maps2.

Definition ident := Ident.ident.

(** * Constant literals *)

Inductive literal :=
  | LTrue : literal
  | LFalse  : literal
  | LInt32 : int -> signedness -> literal
  | LInt64 : int64 -> signedness -> literal
  | LArray : array literal -> literal
  | LRecord : list (ident * literal) -> ident -> literal.

(** * Operators *)

Inductive unary_op : Type :=
  | UopNotbool : unary_op
  | UopNotint : unary_op
  | UopNeg : unary_op
  | UopPlus : unary_op.

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
  | AConstr : ident -> atom
  | AVar : ident -> atom
  | ACast : atom -> btyp -> atom
  | AUnaryOp : unary_op -> atom -> atom
  | ABinaryOp : binary_op -> atom -> atom -> atom.

(** Deep accesses with atomics array indexes. *)

Inductive access : Type :=
  | AcRecordField : ident -> access
  | AcArrayIndex : atom -> access.

(** * Computations with atomic operands *)

Inductive comp : Type := 
  | CpAtom : atom -> comp
  | CpArrayGet : atom -> atom -> comp
  | CpArraySet : atom -> atom -> atom -> comp
  | CpRecordProj : atom -> ident -> comp
  | CpRecordUpdate : atom -> ident -> atom -> comp
  | CpDeepAccess : atom -> list access -> comp
  | CpCall : atom -> list atom -> comp.

(** * Typed syntax *)

Module Typed.

  Inductive literal :=
    | LTrue : btyp -> literal
    | LFalse : btyp -> literal
    | LInt32 : int -> btyp -> literal
    | LInt64 : int64 -> btyp -> literal
    | LArray : array literal -> btyp -> literal
    | LRecord : list (ident * literal) -> btyp -> literal.

  Inductive atom :=
    | ATrue : btyp -> atom
    | AFalse : btyp -> atom
    | AInt32 : int -> btyp -> atom
    | AInt64 : int64 -> btyp -> atom
    | AConstr : ident -> btyp -> atom
    | AVar : ident -> btyp -> atom
    | ACast : atom -> btyp -> atom
    | AUnaryOp : unary_op -> atom -> btyp -> atom
    | ABinaryOp : binary_op -> atom -> atom -> btyp -> atom.

  Inductive access : Type :=
    | AcRecordField : ident -> btyp -> access
    | AcArrayIndex : atom -> btyp -> access.

  Inductive comp : Type := 
    | CpAtom : atom -> btyp -> comp
    | CpArrayGet : atom -> atom -> btyp -> comp
    | CpArraySet : atom -> atom -> atom -> btyp -> comp
    | CpRecordProj : atom -> ident -> btyp -> comp
    | CpRecordUpdate : atom -> ident -> atom -> btyp -> comp
    | CpDeepAccess : atom -> list access -> btyp -> comp
    | CpCall : atom -> list atom -> btyp -> comp.

End Typed.

(** * Syntax shared by some of the intermediate representations. *)

(** ** Functions *)

Record function (B: Type) : Type := mk_function {
  fn_return : btyp;
  fn_params : list (ident * btyp);
  fn_body : B
}.

(** ** Global definitions *)

Inductive param_attr :=
  | AttrReadonly
  | AttrWrite
  | AttrNone.

Inductive globdef (C F: Type) : Type :=
  | DefConst : ident -> C -> btyp -> globdef C F
  | DefFun : ident -> F -> globdef C F
  | DeclConst : ident -> btyp -> globdef C F
  | DeclFun : ident -> list (param_attr * btyp) -> btyp -> globdef C F.

(** ** Programs *)

Record enum_def := mk_enum_def {
  ed_name : ident;
  ed_elems : list ident
}.

Record record_def := mk_record_def {
  rd_name : ident;
  rd_fields : list (ident * btyp)
}.

Inductive struct_or_union : Type :=
  | SU_struct
  | SU_union.

Inductive type_def : Type :=
  | TdEnum : enum_def -> type_def
  | TdRecord : record_def -> type_def
  | TdAbstract : ident -> struct_or_union -> type_def. 

Record program (G: Type) : Type := mk_program {
  prog_defs : list G;
  prog_types : list type_def;
}.

Definition get_record_typedefs (types: list type_def) : list record_def :=
  List.fold_right
    (fun td acc =>
      match td with
      | TdRecord sd => cons sd acc
      | _ => acc
      end)
    nil
    types.

Arguments DefConst {C} {F}.
Arguments DefFun {C} {F}.
Arguments DeclConst {C} {F}.
Arguments DeclFun {C} {F}.

Arguments mk_function {B}.
Arguments fn_return {B}.
Arguments fn_params {B}.
Arguments fn_body {B}.

Arguments mk_program {G}.
Arguments prog_defs {G}.
Arguments prog_types {G}.