From Stdlib Require Import String.
From compcert Require Import Ctypes Integers.
From BarocqComp Require Import Barray Benum Maps2 Utils Types Syntax Pp Printer.

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

  Definition globdef : Type := Syntax.globdef expr btyp literal.

  (** ** Programs *)

  Definition program : Type := Syntax.program expr btyp literal.

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
    | EAttr : ident -> expr -> mtyp -> expr.

  (** ** Functions *)

  Definition function : Type := Syntax.function expr mtyp.

  (** ** Global definitions *)

  Definition globdef : Type := Syntax.globdef expr mtyp literal.

  (** ** Programs *)

  Definition program : Type := Syntax.program expr mtyp literal.

  (** Override the definition of Syntax.get_record_typedefs to avoid
      breaking the OCaml code. *)

  Definition get_record_typedefs (types: smaplist (type_def (mtyp * Types.layout))) : smaplist (smaplist mtyp) :=
    MapList.fold_right
      (fun tid td acc =>
        match td with
        | TdRecord fields => cons (tid, (MapList.map fst fields)) acc
        | _ => acc
        end)
      nil
      types.

  Fixpoint pp_atom (a:atom) :=
    match a with
    | ATrue  => Bstr "true"%string
    | AFalse => Bstr "false"%string
    | AInt32 i s => pp_sint s i
    | AInt64 i s => pp_sint64 s i
    | AConstr s _ => Bstr s
    | AVar s _ => Bstr s
    | ACast a b1 b2 => Pp.seq (pp_atom a :: Bstr " as " :: Bstr "___" :: nil)
    | AUnaryOp o a _ => Bcat (Bstr (string_of_unary_op o)) (pp_atom a)
    | ABinaryOp o a1 a2 _ => Bcat (pp_atom a1)
                            (Bcat (Bstr (string_of_binary_op o)) (pp_atom a2))
    | ARecordProj a id _ => Bcat (pp_atom a)
                            (Bcat (Bstr ".") (Bstr id))
    | ARecordUpdate a id v _ => Pp.seq (pp_atom a :: Bstr " <- " :: Bstr id :: Bstr " := " :: pp_atom v :: nil)
    | ALambda lid a _  => Bstr "lambda"
    | ALambdaRet lid _ _ => Bstr "lambda_ret"
    | AApp f args _      => Pp.seq ((Bstr f) :: Bstr "(" :: Pp.seq (List.map Bstr args) :: Bstr ")" :: nil)
    end.



End Monadic.
