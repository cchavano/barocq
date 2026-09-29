open Printf
open Ident
open Types
open PrintUtils

let recordtyp_to_string (f : 'typ -> string) (fields : (ident * 'typ) list) :
    string =
  list_to_string
    ~delim:("{\n", "\n}")
    ~sep:"\n"
    (fun (x, t) -> sprintf "%s%s : %s," indent (ident_to_string x) (f t))
    fields

let funtyp_to_string (f : 'typ -> string) (tparams : 'typ list) (tret : 'typ) :
    string =
  let p =
    match tparams with
    | [t] -> f t
    | _ -> list_to_string_paren f tparams
  in
  sprintf "%s -> %s" p (f tret)

let rec typ_to_string (ty : typ) : string =
  match ty with
  | TUnit -> "unit"
  | TBool -> "bool"
  | TInt32 Signed -> "i32"
  | TInt32 Unsigned -> "u32"
  | TInt64 Signed -> "i64"
  | TInt64 Unsigned -> "u64"
  | TArray t -> sprintf "[%s]" (typ_to_string t)
  | TEnum (te, _) -> ident_to_string te
  | TRecord (tr, _) -> begin match tr with
                       | None -> "{}"
                       | Some tr -> ident_to_string tr end
  | TAbs t -> ident_to_string t
  | TFun (tparams, tret) -> funtyp_to_string typ_to_string tparams tret

let rec btyp_to_string_rec (ly : layout) (ty : btyp) : string =
  match ty with
  | BBool -> "bool"
  | BInt32 Signed -> "i32"
  | BInt32 Unsigned -> "u32"
  | BInt64 Signed -> "i64"
  | BInt64 Unsigned -> "u64"
  | BEnum te -> ident_to_string te
  | BRecord (tr, _) ->
      let tr' = ident_to_string tr in
      begin match ly with
      | LyBoxed -> tr'
      | LyUnboxed None -> sprintf "#%s" tr'
      | _ -> assert false
      end
  | BActR l ->
     let rec string_of_list () l =
       match l with
       | [] -> ""
       | (s,ty) ::l -> sprintf "%s:%s;%a" (ident_to_string s) (btyp_to_string_rec ly ty) string_of_list l in
     sprintf "{%a}" string_of_list l
  | BArray (ta, ba) ->
      let ta' = btyp_to_string_rec ba ta in
      begin match ly with
      | LyBoxed -> sprintf "[%s]" ta'
      | LyUnboxed (Some sz) -> sprintf "#[%s; %s]" ta' (Camlcoq.Z.to_string sz)
      | _ -> assert false
      end
  | BAbs t -> ident_to_string t
  | BFun (tparams, tret) ->
      funtyp_to_string (btyp_to_string_rec LyBoxed) tparams tret

let btyp_to_string (ty : btyp) : string = btyp_to_string_rec LyBoxed ty
