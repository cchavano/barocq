open Printf
open Syntax
open Types
open BarocqShallow.Monadic
open PrintCommon

let coqlib : string ref = ref ""

let shallowfile : string ref = ref ""

let deepfile : string ref = ref ""

let gen_abs_types_impl_env (types : type_def list) : string =
  let rec lassoc (types : type_def list) : (string * string) list =
    match types with
    | [] -> []
    | td :: types' ->
        let r = lassoc types' in
        begin
          match td with
          | TdAbstract (tid, _) ->
              (Deepgen.ident_to_deep tid, ident_to_string tid) :: r
          | _ -> r
        end
  in
  let env_list prefix l =
    list_to_string
      ""
      ""
      ";\n"
      (fun (d, s) -> sprintf "%s(%s, %s.%s)" prefix d !shallowfile s)
      l
  in
  let env_build env_list l =
    let indent3 = String.make 6 ' ' in
    sprintf
      "PMap.get tid\n\
       %s(List.fold_left\n\
       %s(fun ge '(d, s) => PMap.set d s ge)\n\
       %s[\n\
       %s\n\
       %s]\n\
       %s(PMap.init (unit : Type)))"
      (String.make 4 ' ')
      indent3
      indent3
      (env_list (String.make 8 ' ') l)
      indent3
      indent3
  in
  let l = lassoc types in
  sprintf
    "Definition ABS_TYPES_IMPL (tid: ident) : Type :=\n%s%s.\n\n"
    indent
    (match l with
    | [] -> "unit"
    | _ -> env_build env_list (lassoc types))

let gen_abs_defs_impl_env (defs : globdef list) : string =
  let rec lassoc (defs : globdef list) : (string * string) list =
    match defs with
    | [] -> []
    | d :: defs' ->
        let r = lassoc defs' in
        begin
          match d with
          | DeclConst (x, _) | DeclFun (x, _, _) ->
              (Deepgen.ident_to_deep x, ident_to_string x) :: r
          | _ -> r
        end
  in
  let genv_list prefix l =
    list_to_string
      ""
      ""
      ";\n"
      (fun (d, s) ->
        sprintf
          "%s(%s, (Val ABS_TYPES_IMPL (typof_def_noerr %s.prog %s) %s.%s))"
          prefix
          d
          !deepfile
          d
          !shallowfile
          s)
      l
  in
  let genv_build genv_list l =
    let indent2 = String.make 4 ' ' in
    sprintf
      "List.fold_left\n\
       %s(fun ge '(d, s) => PTree.set d s ge)\n\
       %s[\n\
       %s\n\
       %s]\n\
       %sPTree.Empty"
      indent2
      indent2
      (genv_list (String.make 6 ' ') l)
      indent2
      indent2
  in
  let l = lassoc defs in
  sprintf
    "Definition ABS_DEFS_IMPL : genv ABS_TYPES_IMPL :=\n%s%s.\n\n"
    indent
    (match l with
    | [] -> "PTree.Empty"
    | _ -> genv_build genv_list l)

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
  let deep_fun_id = ident_to_string fid in
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
    "Theorem fun_%s_corres :\n%s%s%s =\n%s%s.\nProof.\n%stry reflexivity.\nQed."
    (ident_to_string fid)
    forall
    indent
    deep_call
    indent
    shallow_call
    indent

let gen_const_corres (cid : ident) (l : literal) (ty : mtyp) =
  let deep_const_id = ident_to_string cid in
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
    "Theorem const_%s_corres :\n%s%s.\nProof.\n%sreflexivity.\nQed."
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

let gen_struct_conv (st : struct_def) : string =
  let id_str = ident_to_string st.sd_name in
  sprintf
    "Definition transl_struct_%s (s: %s.%s) : eval_struct_ctyp %s.prog %s :=\n\
     %s%s."
    id_str
    !shallowfile
    id_str
    !deepfile
    (Deepgen.ident_to_deep st.sd_name)
    indent
    (struct_to_rocq_struct (List.map fst st.sd_fields) "s")

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

let gen_struct_conv_corres (st : struct_def) : string =
  list_to_string
    ""
    ""
    "\n\n"
    (fun field ->
      sprintf
        "%s\n\n%s"
        (gen_struct_field_proj_conv_corres st.sd_name field)
        (gen_struct_field_update_conv_corres st.sd_name field))
    st.sd_fields

let gen_globdef_corres (def : globdef) : string =
  match def with
  | DefConst (id, ty, l) -> gen_const_corres id ty l
  | DefFun (id, f) -> gen_function_corres id f
  | _ -> ""

let make_headers () : string =
  sprintf
    "From Coq Require Import BinPosDef String List.\n\
     From compcert Require Import Maps Integers Clightdefs.\n\
     From BarocqComp Require Import Types Error Array Struct Barocq.\n\
     From %s Require Import %s %s.\n\n\
     Import ListNotations.\n\
     Import ClightNotations.\n\n\
     Open Scope string_scope.\n\
     Open Scope clight_scope.\n\n"
    !coqlib
    !shallowfile
    !deepfile

let print_proofs (out : out_channel) (prog : program) : unit =
  let types = prog.prog_types in
  let defs = prog.prog_defs in
  let s, e =
    match (types, defs) with
    | [], [] -> ("", "")
    | _ :: _, [] -> ("\n", "")
    | _ :: _, _ :: _ -> ("\n\n", "\n")
    | [], _ :: _ -> ("", "\n")
  in
  fprintf out "%s" (make_headers ());
  fprintf out "%s" (gen_abs_types_impl_env types);
  fprintf out "%s" (gen_abs_defs_impl_env defs);
  fprintf
    out
    "Definition eval_def := Barocq.eval_def ABS_TYPES_IMPL ABS_DEFS_IMPL.\n\n";
  fprintf
    out
    "Definition eval_struct_ctyp := Barocq.eval_struct_ctyp ABS_TYPES_IMPL.\n\n";
  let structs = get_struct_defs types in
  if structs <> [] then begin
    fprintf out "(** * Struct conversions **)\n\n";
    print_list out "" s "\n\n" gen_struct_conv structs;
    print_list out "" s "\n\n" gen_struct_conv_corres structs
  end;
  if defs <> [] then fprintf out "(** * Program correspondence proofs **)\n\n";
  let defs =
    List.filter
      (fun (d : BarocqShallow.Monadic.globdef) ->
        match d with
        | DefFun _ | DefConst _ -> true
        | _ -> false)
      defs
  in
  print_list out "" e "\n\n" gen_globdef_corres defs
