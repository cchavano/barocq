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

Record function (B T: Type) : Type := mk_function {
  fn_return : T;
  fn_params : list (ident * T);
  fn_body : B
}.

(** ** Global definitions *)

Inductive param_attr :=
  | AttrReadonly
  | AttrWrite
  | AttrNone.

Inductive globdef (L F T: Type) : Type :=
  | DefConst : ident -> L -> T -> globdef L F T
  | DefFun : ident -> F -> globdef L F T
  | DeclConst : ident -> T -> globdef L F T
  | DeclFun : ident -> list (param_attr * T) -> T -> globdef L F T.

(** ** Programs *)

Record enum_def := mk_enum_def {
  ed_name : ident;
  ed_elems : list ident
}.

Record record_def (T: Type) := mk_record_def {
  rd_name : ident;
  rd_fields : list (ident * T)
}.

Arguments rd_name {T}.
Arguments rd_fields {T}.

Inductive struct_or_union : Type :=
  | SU_struct
  | SU_union.

Inductive type_def (T: Type) : Type :=
  | TdEnum : enum_def -> type_def T
  | TdRecord : record_def T -> type_def T
  | TdAbstract : ident -> struct_or_union -> type_def T. 

Arguments TdEnum {T}.
Arguments TdRecord {T}.
Arguments TdAbstract {T}.

Record program (G T: Type) : Type := mk_program {
  prog_defs : list G;
  prog_types : list (type_def T);
}.

Definition get_record_typedefs {T} (types: list (type_def T)) : list (record_def T) :=
  List.fold_right
    (fun td acc =>
      match td with
      | TdRecord sd => cons sd acc
      | _ => acc
      end)
    nil
    types.

Arguments DefConst {L} {F} {T}.
Arguments DefFun {L} {F} {T}.
Arguments DeclConst {L} {F} {T}.
Arguments DeclFun {L} {F} {T}.

Arguments mk_function {B} {T}.
Arguments fn_return {B} {T}.
Arguments fn_params {B} {T}.
Arguments fn_body {B} {T}.

Arguments mk_program {G T}.
Arguments prog_defs {G T}.
Arguments prog_types {G T}.