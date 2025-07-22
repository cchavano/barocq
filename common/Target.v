(** * Target arch *)

(** The target architecture is used to typecheck array indexes.
  The user might provide a different architecture from the one
  with which CompCert was compiled.
*)

Inductive archi : Type :=
  | Ptr32
  | Ptr64.