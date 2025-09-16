open Printf
open Ident
open Types
open Barocq
open PrintUtils
open PrintTypes

exception Error of string

let rec val_to_string (ty : typ) (x : 'a) : string =
  let o = Obj.magic x in
  match ty with
  | TBool -> sprintf "%B" o
  | TInt32 Signed -> i32_to_string o
  | TInt32 Unsigned -> u32_to_string o
  | TInt64 Signed -> i64_to_string o
  | TInt64 Unsigned -> u64_to_string o
  | TArray ta -> list_to_string_bracketbar (val_to_string ta) o
  | TEnum (_, elems) -> ident_to_string (Benum.ident_of_constr elems o)
  | TRecord (_, fields) -> struct_to_string fields o
  | TAbs _ -> "<abs>"
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
    ~delim:("{", "}")
    ~sep:"; "
    (fun (x, t, o) -> sprintf "%s = %s" (ident_to_string x) (val_to_string t o))
    l

let value_to_string (vv : value) : string =
  match vv with
  | Val (tv, v) -> sprintf "val %s : %s" (val_to_string tv v) (typ_to_string tv)

let interpret (arch : Target.archi) (p : Typed.command list) : unit =
  match interpret arch (Maps.PMap.init (Obj.magic ())) p with
  | Errors.OK lv -> List.iter (fun v -> printf "%s\n" (value_to_string v)) lv
  | Errors.Error msg -> raise @@ Error (C2C.string_of_errmsg msg)
