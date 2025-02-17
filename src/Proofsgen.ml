open Printf
open Syntax
open BarocqShallow.Monadic
open PrintCommon

let coqlib : string ref = ref ""

let shallowfile : string ref = ref ""

let deepfile : string ref = ref ""

let convert_struct_value (id : ident) (arg : string) : string =
  sprintf "transl_struct_%s %s" (ident_to_string id) arg

let gen_deep_call_arg ((aid, aty) : ident * mtyp) : string =
  match aty with
  | MStruct id -> sprintf "(%s)" (convert_struct_value id (ident_to_string aid))
  | _ -> ident_to_string aid

let gen_deep_call_args (args : (ident * mtyp) list) : string =
  match args with
  | [] -> "tt"
  | _ -> list_to_string "" "" " " gen_deep_call_arg args

let gen_shallow_call_ret (res : string) (ty : mtyp) : string =
  match ty with
  | MRes _ -> res
  | MStruct id ->
      sprintf "ret (%s)" (convert_struct_value id (sprintf "(%s)" res))
  | _ -> sprintf "ret (%s)" res

let gen_function_corres (fid : ident) (f : coq_function) : string =
  let params = f.fn_params in
  let forall =
    match params with
    | [] -> ""
    | _ ->
        sprintf "%sforall %s,\n" indent (Shallowgen.param_list_to_rocq params)
  in
  let deep_fun_id =
    let str = ident_to_string fid in
    String.sub str 1 (String.length str - 1)
  in
  let deep_call =
    sprintf
      "eval_def %s.prog %s %s"
      !deepfile
      (sprintf "$\"%s\"" deep_fun_id)
      (gen_deep_call_args params)
  in
  let shallow_call =
    let args =
      match params with
      | [] -> "tt"
      | _ -> list_to_string "" "" " " ident_to_string (List.map fst params)
    in
    let base = sprintf "%s.%s %s" !shallowfile (ident_to_string fid) args in
    gen_shallow_call_ret base f.fn_return
  in
  sprintf
    "Theorem fun%s_corres :\n%s%s%s =\n%s%s.\nProof.\n%sreflexivity.\nQed."
    (ident_to_string fid)
    forall
    indent
    deep_call
    indent
    shallow_call
    indent

let gen_const_corres (cid : ident) (l : literal) (ty : mtyp) =
  let deep_const_id =
    let str = ident_to_string cid in
    String.sub str 1 (String.length str - 1)
  in
  let shallow_const =
    match ty with
    | MStruct id ->
        convert_struct_value
          id
          (sprintf "%s.%s" !shallowfile (ident_to_string cid))
    | _ -> ident_to_string cid
  in
  let thm =
    sprintf
      "eval_def %s.prog $\"%s\" = %s"
      !deepfile
      deep_const_id
      shallow_const
  in
  sprintf
    "Theorem const%s_corres :\n%s%s.\nProof.\n%sreflexivity.\nQed."
    (ident_to_string cid)
    indent
    thm
    indent

let field_to_rocq_struct (fname : ident) (arg : string) : string =
  sprintf
    "Field %s (%s.%s %s)"
    (Deepgen.ident_to_deep fname)
    !shallowfile
    (ident_to_string fname)
    arg

let struct_to_rocq_struct (st : ident list) (arg : string) : string =
  List.fold_right
    (fun d acc -> sprintf "(%s, %s)" (field_to_rocq_struct d arg) acc)
    st
    "tt"

let gen_struct_conv (id : ident) (fields : (ident * mtyp) list) : string =
  let id_str = ident_to_string id in
  sprintf
    "Definition transl_struct_%s (s: %s.%s) : eval_struct_ctyp %s.prog %s :=\n\
     %s%s."
    id_str
    !shallowfile
    id_str
    !deepfile
    (Deepgen.ident_to_deep id)
    indent
    (struct_to_rocq_struct (List.map fst fields) "s")

let gen_struct_field_proj_conv_corres (id : ident)
    ((fname, ftyp) : ident * mtyp) : string =
  let id_str = ident_to_string id in
  sprintf
    "Theorem transl_struct_%s_proj_%s_corres :\n\
     %sforall (s: %s.%s),\n\
     %sStruct.proj (transl_struct_%s s) %s = ret (%s s).\n\
     Proof.\n\
     %sreflexivity.\n\
     Qed."
    id_str
    (ident_to_string fname)
    indent
    !shallowfile
    id_str
    indent
    id_str
    (Deepgen.ident_to_deep fname)
    (ident_to_string fname)
    indent

let gen_struct_field_update_conv_corres (id : ident)
    ((fname, ftyp) : ident * mtyp) : string =
  let id_str = ident_to_string id in
  (* let struct_var = "s" in *)
  sprintf
    "Theorem transl_struct_%s_update_%s_corres :\n\
     %sforall (s: %s.%s) (v: %s),\n\
     %sStruct.update (transl_struct_%s s) %s v =\n\
     %sret (transl_struct_%s (%s.set_%s_%s s v)).\n\
     Proof.\n\
     %sreflexivity.\n\
     Qed."
    id_str
    (ident_to_string fname)
    indent
    !shallowfile
    id_str
    (Shallowgen.mtyp_to_rocq ftyp)
    indent
    id_str
    (Deepgen.ident_to_deep fname)
    indent
    id_str
    !shallowfile
    id_str
    (ident_to_string fname)
    indent

let gen_struct_conv_corres (id : ident) (fields : (ident * mtyp) list) : string
    =
  list_to_string
    ""
    ""
    "\n\n"
    (fun field ->
      sprintf
        "%s\n\n%s"
        (gen_struct_field_proj_conv_corres id field)
        (gen_struct_field_update_conv_corres id field))
    fields

let gen_globdef_corres (def : globdef) : string =
  match def with
  | DefConst (id, ty, l) -> gen_const_corres id ty l
  | DefFun (id, f) -> gen_function_corres id f

let make_headers () : string =
  sprintf
    "From Coq Require Import String.\n\
     From compcert Require Import Integers Clightdefs.\n\
     From BarocqComp Require Import Error Array Struct Barocq.\n\
     From %s Require Import %s %s.\n\n\
     Import ClightNotations.\n\n\
     Open Scope string_scope.\n\
     Open Scope clight_scope.\n\n"
    !coqlib
    !shallowfile
    !deepfile

let print_proofs (out : out_channel) (prog : program) : unit =
  let types = Maps.PTree.elements prog.prog_types in
  let defs = prog.prog_defs in
  let s, e =
    match (types, defs) with
    | [], [] -> ("", "")
    | _ :: _, [] -> ("\n", "")
    | _ :: _, _ :: _ -> ("\n\n", "\n")
    | [], _ :: _ -> ("", "\n")
  in
  fprintf out "%s" (make_headers ());
  fprintf out "(** * Struct conversions **)\n\n";
  print_list
    ""
    s
    "\n\n"
    (fun (id, fields) -> gen_struct_conv id fields)
    out
    types;
  print_list
    ""
    s
    "\n\n"
    (fun (id, fields) -> gen_struct_conv_corres id fields)
    out
    types;
  fprintf out "(** * Program correspondence proofs **)\n\n";
  print_list "" e "\n\n" gen_globdef_corres out defs
