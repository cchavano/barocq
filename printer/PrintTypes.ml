open Printf
open Types
open PrintCommon

let structtyp_to_string (f : 'typ -> string) (fields : (ident * 'typ) list) :
    string =
  list_to_string
    "{"
    ";}"
    "; "
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
  | TStruct (x, _) -> sprintf "%s" (ident_to_string x)
  | TFun (tparams, tret) -> funtyp_to_string typ_to_string tparams tret

and opt_parens (ty : typ) = PrintCommon.opt_parens is_simpl_typ typ_to_string ty

let rec ctyp_to_string (ty : ctyp) : string =
  match ty with
  | CBool -> "bool"
  | CInt32 Signed -> "i32"
  | CInt32 Unsigned -> "u32"
  | CInt64 Signed -> "i64"
  | CInt64 Unsigned -> "u64"
  | CArray (CArray t) -> sprintf "array (%s)" (ctyp_to_string t)
  | CArray t -> sprintf "array %s" (ctyp_to_string t)
  | CStruct a -> ident_to_string a
  | CFun (tparams, tret) -> funtyp_to_string ctyp_to_string tparams tret
