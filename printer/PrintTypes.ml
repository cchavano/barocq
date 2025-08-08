open Printf
open Ident
open Types
open PrintUtils

let recordtyp_to_string (f : 'typ -> string) (fields : (ident * 'typ) list) :
    string =
  list_to_string
    ~delim:("{", ";}")
    ~sep:"; "
    (fun (x, t) -> sprintf "%s : %s" (ident_to_string x) (f t))
    fields

let funtyp_to_string (f : 'typ -> string) (tparams : 'typ list) (tret : 'typ) :
    string =
  let p =
    match tparams with
    | [t] -> f t
    | _ -> list_to_string_paren f tparams
  in
  sprintf "%s -> %s" p (f tret)

let is_simpl_typ (ty : typ) : bool =
  match ty with
  | TArray _ | TFun _ -> false
  | _ -> true

let rec typ_to_string (ty : typ) : string =
  match ty with
  | TBool -> "bool"
  | TInt32 Signed -> "i32"
  | TInt32 Unsigned -> "u32"
  | TInt64 Signed -> "i64"
  | TInt64 Unsigned -> "u64"
  | TArray t -> sprintf "array %s" (opt_parens t)
  | TEnum (te, _) -> ident_to_string te
  | TRecord (tr, _) -> ident_to_string tr
  | TAbs t -> ident_to_string t
  | TFun (tparams, tret) -> funtyp_to_string typ_to_string tparams tret

and opt_parens (ty : typ) = PrintUtils.opt_parens is_simpl_typ typ_to_string ty

let rec btyp_to_string (ty : btyp) : string =
  match ty with
  | BBool -> "bool"
  | BInt32 Signed -> "i32"
  | BInt32 Unsigned -> "u32"
  | BInt64 Signed -> "i64"
  | BInt64 Unsigned -> "u64"
  | BArray (BArray t) -> sprintf "array (%s)" (btyp_to_string t)
  | BArray ta -> sprintf "array %s" (btyp_to_string ta)
  | BEnum te -> ident_to_string te
  | BRecord tr -> ident_to_string tr
  | BAbs t -> ident_to_string t
  | BFun (tparams, tret) -> funtyp_to_string btyp_to_string tparams tret
