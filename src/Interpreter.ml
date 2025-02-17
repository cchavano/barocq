open Printf
open Camlcoq
open Types
open Barocq
open Common
open PrintCommon
open PrintTypes

exception Error of string

let rec val_to_string (ty : typ) (x : 'a) : string =
  let o = Obj.magic x in
  match ty with
  | TBool -> sprintf "%B" o
  | TInt32 -> sprintf "%ld" (camlint_of_coqint o)
  | TInt64 -> sprintf "%Ld" (camlint64_of_coqint o)
  | TArray ta -> list_to_string_bracketbar (val_to_string ta) o
  | TStruct (_, fields) -> struct_to_string fields o
  | TFun _ -> "<fun>"

and struct_to_string (fields : (ident * typ) list) (st : 'a) : string =
  let rec aux fields st : (ident * typ * Obj.t) list =
    match fields with
    | [] -> []
    | (x, t) :: fields' ->
        let f, st' = Obj.magic st in
        (x, t, f) :: aux fields' st'
  in
  let l = aux fields st in
  list_to_string
    "{"
    "}"
    "; "
    (fun (x, t, o) -> sprintf "%s = %s" (ident_to_string x) (val_to_string t o))
    l

let value_to_string (vv : value) : string =
  match vv with
  | Val (tv, v) -> sprintf "val %s : %s" (val_to_string tv v) (typ_to_string tv)

let interpret (p : xprogram) : unit =
  match interpret p with
  | Errors.OK lv -> List.iter (fun v -> printf "%s\n" (value_to_string v)) lv
  | Errors.Error msg -> raise @@ Error (C2C.string_of_errmsg msg)
