open Printf
open Syntax
open BarocqShallow.Monadic
open PrintCommon

let coqlib : string ref = ref ""

let shallowfile : string ref = ref ""

let deepfile : string ref = ref ""

module Deeptypes = struct
  let prim_types : string =
    list_to_string
      ~delim:("", "\n")
      ~sep:"\n\n"
      (fun t -> sprintf "%s%s" indent t)
      [
        "Definition bool_t := TBool.";
        "Definition int32_t := TInt32 Signed.";
        "Definition uint32_t := TInt32 Unsigned.";
        "Definition int64_t := TInt64 Signed.";
        "Definition uint64_t := TInt64 Unsigned.";
      ]

  let rec is_simpl_mtyp (ty : mtyp) : bool =
    match ty with
    | MBool | MInt32 _ | MInt64 _ | MRecord _ -> true
    | MRes tr -> is_simpl_mtyp tr
    | _ -> false

  let rec mtyp_to_typ_string (ty : mtyp) : string =
    match ty with
    | MBool -> "bool_t"
    | MInt32 Types.Signed -> "int32_t"
    | MInt32 Types.Unsigned -> "uint32_t"
    | MInt64 Types.Signed -> "int64_t"
    | MInt64 Types.Unsigned -> "uint64_t"
    | MArray ta -> sprintf "TArray %s" (opt_parens ta)
    | MRecord rid -> ident_to_string rid
    | MFun (tparams, tret) ->
        sprintf
          "TFun %s %s"
          (list_to_string_bracket mtyp_to_typ_string tparams)
          (opt_parens tret)
    | MAbs tid -> ident_to_string tid
    | MRes tr -> mtyp_to_typ_string tr

  and opt_parens (ty : mtyp) : string =
    PrintCommon.opt_parens is_simpl_mtyp mtyp_to_typ_string ty

  let typedef_to_string (td : type_def) : string =
    match td with
    | TdRecord rd ->
        sprintf
          "Definition %s : typ := TRecord %s %s."
          (ident_to_string rd.rd_name)
          (Deepgen.ident_to_deep rd.rd_name)
          (list_to_string_bracket
             (fun (fname, fty) ->
               sprintf
                 "(%s, %s)"
                 (Deepgen.ident_to_deep fname)
                 (mtyp_to_typ_string fty))
             rd.rd_fields)
    | TdAbstract (tid, _) ->
        sprintf
          "Definition %s : typ := TAbs %s."
          (ident_to_string tid)
          (Deepgen.ident_to_deep tid)

  let deftype_to_string (def : globdef) : string =
    let dt =
      match def with
      | DefConst (cid, _, ty) | DeclConst (cid, ty) ->
          sprintf "%s := %s" (ident_to_string cid) (mtyp_to_typ_string ty)
      | DefFun (fid, f) ->
          let fty = MFun (List.map snd f.fn_params, f.fn_return) in
          sprintf "%s := %s" (ident_to_string fid) (mtyp_to_typ_string fty)
      | DeclFun (fid, tparams, tret) ->
          let fty = MFun (List.map snd tparams, tret) in
          sprintf "%s := %s" (ident_to_string fid) (mtyp_to_typ_string fty)
    in
    sprintf "Definition typof_%s." dt

  let print_typedefs (out : out_channel) (types : type_def list) : unit =
    print_list
      out
      ~delim:("", "\n")
      ~sep:"\n\n"
      (fun td -> sprintf "%s%s" indent (typedef_to_string td))
      types

  let print_deftypes (out : out_channel) (defs : globdef list) : unit =
    print_list
      out
      ~delim:("", "\n")
      ~sep:"\n\n"
      (fun def -> sprintf "%s%s" indent (deftype_to_string def))
      defs

  let print (out : out_channel) (prog : program) : unit =
    let types = prog.prog_types in
    let defs = prog.prog_defs in
    fprintf out "\n";
    fprintf out "Module Deeptypes.\n\n";
    fprintf out "%s" prim_types;
    fprintf out "\n";
    if types <> [] then begin
      print_typedefs out prog.prog_types;
      fprintf out "\n"
    end;
    if defs <> [] then begin
      print_deftypes out prog.prog_defs;
      fprintf out "\n"
    end;
    fprintf out "End Deeptypes.\n"
end

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
      ~delim:("", "")
      ~sep:";\n"
      (fun (d, s) -> sprintf "%s(%s, %s.%s : Type)" prefix d !shallowfile s)
      l
  in
  let env_build env_list l =
    let indent2 = make_indent 2 in
    sprintf
      "List.fold_left\n\
       %s(fun ge '(d, s) => PMap.set d s ge)\n\
       %s[\n\
       %s\n\
       %s]\n\
       %s(PMap.init (unit : Type))"
      indent2
      indent2
      (env_list (make_indent 3) l)
      indent2
      indent2
  in
  let l = lassoc types in
  sprintf
    "Definition abs_types_impl : PMap.t Type :=\n%s%s.\n"
    indent
    (match l with
    | [] -> "PMap.init (unit : Type)"
    | _ -> env_build env_list (lassoc types))

module Brecordtypes = struct
  let rec is_simpl_mtyp (ty : mtyp) : bool =
    match ty with
    | MBool | MInt32 _ | MInt64 _ | MAbs _ -> true
    | MRes ty' -> is_simpl_mtyp ty'
    | _ -> false

  let rec mtyp_to_string (ty : mtyp) : string =
    match ty with
    | MBool -> "bool"
    | MInt32 _ -> "int"
    | MInt64 _ -> "int64"
    | MArray ta -> sprintf "array %s" (opt_parens ta)
    | MRecord t -> sprintf "record %s" (ident_to_string t)
    | MAbs t -> sprintf "%s.%s" !shallowfile (ident_to_string t)
    | MFun (tparams, tret) -> (
        match tparams with
        | [] -> sprintf "unit -> %s" (opt_parens tret)
        | _ ->
            List.fold_right
              (fun t acc -> sprintf "%s -> %s" (opt_parens t) acc)
              tparams
              (opt_parens tret))
    | MRes ty' -> sprintf "res %s" (opt_parens ty')

  and opt_parens (ty : mtyp) : string =
    PrintCommon.opt_parens is_simpl_mtyp mtyp_to_string ty

  let typedef_to_string (rd : record_def) : string =
    sprintf
      "Definition %s : list (ident * Type) := %s."
      (ident_to_string rd.rd_name)
      (list_to_string_bracket
         (fun (fname, fty) ->
           sprintf
             "(%s, %s : Type)"
             (Deepgen.ident_to_deep fname)
             (opt_parens fty))
         rd.rd_fields)

  let print_typedefs (out : out_channel) (types : type_def list) : unit =
    let records = get_record_defs types in
    print_list
      out
      ~delim:("", "\n")
      ~sep:"\n\n"
      (fun td -> sprintf "%s%s" indent (typedef_to_string td))
      records

  let print (out : out_channel) (prog : program) : unit =
    let types = prog.prog_types in
    fprintf out "\n";
    fprintf out "Module Brecordtypes.\n\n";
    if types <> [] then begin
      print_typedefs out prog.prog_types;
      fprintf out "\n"
    end;
    fprintf out "End Brecordtypes.\n"
end

module RecordConv = struct
  type direction =
    | RtoB
    | BtoR

  let direction_to_string (d : direction) : string =
    match d with
    | RtoB -> "RtoB"
    | BtoR -> "BtoR"

  let rec conv_mtyp_str (d : direction) (ty : mtyp) : string =
    match ty with
    | MRecord rid ->
        sprintf "conv_%s_%s" (ident_to_string rid) (direction_to_string d)
    | MArray ta ->
        let r = conv_mtyp_str d ta in
        if r = "" then ""
        else if String.starts_with ~prefix:"conv" r then
          sprintf "transl_array %s" r
        else sprintf "transl_array (%s)" r
    | _ -> ""

  let conv_value (d : direction) (fty : mtyp) (v : string) : string =
    let tstr = conv_mtyp_str d fty in
    if tstr = "" then v else sprintf "%s %s" tstr v

  let conv_value_opt_parens (d : direction) (fty : mtyp) (v : string) : string =
    let v_conv = conv_value d fty v in
    if v_conv = v then v else sprintf "(%s)" v_conv

  (* Rocq to Barocq *)

  let conv_field_RtoB (rid : string) (fname : ident) (fty : mtyp) (arg : string)
      : string =
    let v =
      sprintf
        "%s.(%s_%s)"
        arg
        (String.lowercase_ascii rid)
        (ident_to_string fname)
    in
    sprintf
      "Field %s %s"
      (Deepgen.ident_to_deep fname)
      (conv_value_opt_parens RtoB fty v)

  let conv_record_RtoB (rd : record_def) (arg : string) : string =
    List.fold_right
      (fun (fname, fty) acc ->
        sprintf
          "(%s, %s)"
          (conv_field_RtoB (ident_to_string rd.rd_name) fname fty arg)
          acc)
      rd.rd_fields
      "tt"

  let gen_conv_record_RtoB (rd : record_def) : string =
    let rid = ident_to_string rd.rd_name in
    sprintf
      "Definition conv_%s_RtoB (s: %s.%s) : record Brecordtypes.%s :=\n%s%s."
      rid
      !shallowfile
      rid
      rid
      indent
      (conv_record_RtoB rd "s")

  (* Barocq to Rocq *)

  let conv_record_BtoR (rd : record_def) : string =
    let match_case =
      List.fold_right
        (fun (fname, fty) acc ->
          sprintf "(Field _ %s, %s)" (ident_to_string fname) acc)
        rd.rd_fields
        "tt"
    in
    let mk_record =
      sprintf
        "mk_%s %s"
        (ident_to_string rd.rd_name)
        (list_to_string
           ~delim:("", "")
           ~sep:" "
           (fun (fname, fty) ->
             let v = ident_to_string fname in
             conv_value_opt_parens BtoR fty v)
           rd.rd_fields)
    in
    sprintf
      "%smatch s with\n%s| %s =>\n%s%s\n%send"
      indent
      indent
      match_case
      (make_indent 3)
      mk_record
      indent

  let gen_conv_record_BtoR (rd : record_def) : string =
    let rid = ident_to_string rd.rd_name in
    sprintf
      "Definition conv_%s_BtoR (s: record Brecordtypes.%s) : %s.%s :=\n%s."
      rid
      rid
      !shallowfile
      rid
      (conv_record_BtoR rd)

  (* Main printing function *)

  let print_conversions (out : out_channel) (records : record_def list) : unit =
    if records <> [] then begin
      fprintf out "\n(** * Barocq <-> Rocq record conversions **)\n\n";
      fprintf
        out
        "Definition transl_array {A B: Type} (f: A -> B) (a: array A) : array \
         B :=\n\
         %sList.map f a.\n\n"
        indent;
      fprintf
        out
        "Definition transl_array_err {A B: Type} (f: A -> res B) (a: array A) \
         : res (array B) :=\n\
         %sErrors.mmap f a.\n\n"
        indent;
      print_list
        out
        ~delim:("", "\n\n")
        ~sep:"\n\n"
        gen_conv_record_RtoB
        records;
      print_list out ~delim:("", "\n") ~sep:"\n\n" gen_conv_record_BtoR records
    end

  (* Correctness theorems *)

  let gen_RtoB_conv_correctness_thm (rd : record_def) : string =
    let rid = ident_to_string rd.rd_name in
    let forall =
      sprintf "forall (r: %s) (b: record Brecordtypes.%s)," rid rid
    in
    let conv_call = sprintf "conv_%s_RtoB r = b" rid in
    let fields_conv =
      list_to_string
        ~delim:("", "")
        ~sep:" /\\\n"
        (fun (fname, fty) ->
          let rproj =
            sprintf
              "r.(%s_%s)"
              (String.lowercase_ascii rid)
              (ident_to_string fname)
          in
          let rproj = conv_value_opt_parens RtoB fty rproj in
          sprintf
            "%s@Brecord.proj Brecordtypes.%s b %s = OK %s"
            indent
            rid
            (Deepgen.ident_to_deep fname)
            rproj)
        rd.rd_fields
    in
    let proof = sprintf "Proof.\n%sintros. subst. repeat split.\nQed." indent in
    sprintf
      "Lemma conv_%s_RtoB_correct :\n%s%s\n%s%s ->\n%s.\n%s"
      rid
      indent
      forall
      indent
      conv_call
      fields_conv
      proof

  let gen_BtoR_conv_correctness_thm (rd : record_def) : string =
    let rid = ident_to_string rd.rd_name in
    let forall =
      sprintf "forall (b: record Brecordtypes.%s) (r: %s)," rid rid
    in
    let conv_call = sprintf "conv_%s_BtoR b = r" rid in
    let field_conv (fname : ident) (fty : mtyp) : string =
      let fid = ident_to_string fname in
      let rval = conv_value BtoR fty fid in
      if rval = fid then
        sprintf
          "%s@Brecord.proj Brecordtypes.%s b %s = OK r.(%s_%s)"
          indent
          rid
          (Deepgen.ident_to_deep fname)
          (String.lowercase_ascii rid)
          fid
      else
        sprintf
          "%s(exists %s, @Brecord.proj Brecordtypes.%s b %s = OK %s /\\ %s = \
           r.(%s_%s))"
          indent
          fid
          rid
          (Deepgen.ident_to_deep fname)
          fid
          rval
          (String.lowercase_ascii rid)
          fid
    in
    let fields_conv =
      list_to_string
        ~delim:("", "")
        ~sep:" /\\\n"
        (fun (fname, fty) -> field_conv fname fty)
        rd.rd_fields
    in
    let record_destruct =
      List.fold_right
        (fun (fname, fty) acc ->
          sprintf "[[%s] %s]" (ident_to_string fname) acc)
        rd.rd_fields
        "[]"
    in
    let proof =
      sprintf
        "Proof.\n\
         %s(* intros b r Hconv. unfold conv_%s_BtoR in Hconv. compute in b.\n\
         %sdestruct b as %s.\n\
         %sdestruct Hconv. simpl. repeat esplit. *)\n\
         Admitted."
        indent
        rid
        indent
        record_destruct
        indent
    in
    sprintf
      "Lemma conv_%s_BtoR_correct :\n%s%s\n%s%s ->\n%s.\n%s"
      rid
      indent
      forall
      indent
      conv_call
      fields_conv
      proof

  let print_correctness_lemmas (out : out_channel) (records : record_def list) :
      unit =
    print_list
      out
      ~delim:("", "\n\n")
      ~sep:"\n\n"
      gen_RtoB_conv_correctness_thm
      records;
    print_list
      out
      ~delim:("", "\n")
      ~sep:"\n\n"
      gen_BtoR_conv_correctness_thm
      records
end

module FFI = struct
  let rec is_simpl_mtyp (ty : mtyp) : bool =
    match ty with
    | MBool | MInt32 _ | MInt64 _ | MAbs _ -> true
    | MRes ty' -> is_simpl_mtyp ty'
    | _ -> false

  let rec mtyp_to_string (ty : mtyp) : string =
    match ty with
    | MBool -> "bool"
    | MInt32 _ -> "int"
    | MInt64 _ -> "int64"
    | MArray ta -> sprintf "array %s" (opt_parens ta)
    | MRecord t -> sprintf "record Brecordtypes.%s" (ident_to_string t)
    | MAbs t -> ident_to_string t
    | MFun (tparams, tret) -> (
        match tparams with
        | [] -> sprintf "unit -> %s" (opt_parens tret)
        | _ ->
            List.fold_right
              (fun t acc -> sprintf "%s -> %s" (opt_parens t) acc)
              tparams
              (opt_parens tret))
    | MRes ty' -> sprintf "res %s" (opt_parens ty')

  and opt_parens (ty : mtyp) : string =
    PrintCommon.opt_parens is_simpl_mtyp mtyp_to_string ty

  let gen_fun_body (fid : ident) (tparams : mtyp list) (tret : mtyp) : string =
    let rec gen_args (n : int) : string =
      if n >= List.length tparams then ""
      else sprintf "a%d %s" n (gen_args (n + 1))
    in
    let conv_args : string =
      snd
        (List.fold_left
           (fun (ctr, str) ty ->
             let arg = sprintf "a%d" ctr in
             let conv_arg = RecordConv.conv_value RecordConv.BtoR ty arg in
             if conv_arg = arg then (ctr + 1, str)
             else
               let str' =
                 sprintf
                   "%s%slet %s := %s in\n"
                   str
                   (make_indent 3)
                   arg
                   (RecordConv.conv_value RecordConv.BtoR ty arg)
               in
               (ctr + 1, str'))
           (0, "")
           tparams)
    in
    let gen_call () : string =
      sprintf
        "%slet* r := %s.%s %sin\n"
        (make_indent 3)
        !shallowfile
        (ident_to_string fid)
        (gen_args 0)
    in
    let gen_return () : string =
      let tret = BarocqShallowgen.Monadification.unwrap_mtyp tret in
      sprintf
        "%sret %s."
        (make_indent 3)
        (RecordConv.conv_value_opt_parens RecordConv.RtoB tret "r")
    in
    sprintf
      "%sfun %s=>\n%s%s%s"
      (make_indent 2)
      (gen_args 0)
      conv_args
      (gen_call ())
      (gen_return ())

  let gen_ffi_fun (fid : ident) (tparams : (param_attr * mtyp) list)
      (tret : mtyp) : string =
    let tparams = List.map snd tparams in
    sprintf
      "Definition %s : %s :=\n%s"
      (ident_to_string fid)
      (mtyp_to_string (MFun (tparams, tret)))
      (gen_fun_body fid tparams tret)

  let print_functions (out : out_channel) (defs : globdef list) : unit =
    fprintf out "Module FFI.\n\n";
    print_list
      out
      ~delim:("", "")
      ~sep:""
      (fun (d : BarocqShallow.Monadic.globdef) ->
        match d with
        | DeclFun (fid, tparams, tret) ->
            sprintf "%s%s\n\n" indent (gen_ffi_fun fid tparams tret)
        | DeclConst (cid, t) ->
            let cid = ident_to_string cid in
            sprintf
              "%sDefinition %s : %s :=\n%s%s.\n\n"
              indent
              cid
              (mtyp_to_string t)
              (make_indent 2)
              (RecordConv.conv_value
                 RecordConv.RtoB
                 t
                 (sprintf "%s.%s" !shallowfile cid))
        | _ -> "")
      defs;
    fprintf out "End FFI.\n"
end

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
      ~delim:("", "")
      ~sep:";\n"
      (fun (d, s) ->
        sprintf "%s(%s, VAL Deeptypes.typof_%s FFI.%s)" prefix d s s)
      l
  in
  let genv_build genv_list l =
    let indent2 = make_indent 2 in
    sprintf
      "List.fold_left\n\
       %s(fun ge '(d, s) => PTree.set d s ge)\n\
       %s[\n\
       %s\n\
       %s]\n\
       %sPTree.Empty"
      indent2
      indent2
      (genv_list (make_indent 3) l)
      indent2
      indent2
  in
  let l = lassoc defs in
  sprintf
    "Definition abs_defs_impl : genv abs_types_impl :=\n%s%s.\n"
    indent
    (match l with
    | [] -> "PTree.Empty"
    | _ -> genv_build genv_list l)

let gen_const_corres (cid : ident) (ty : mtyp) : string =
  let thm =
    sprintf
      "eval_def %s = OK (VAL Deeptypes.typof_%s %s)"
      (Deepgen.ident_to_deep cid)
      (ident_to_string cid)
      (RecordConv.conv_value
         RecordConv.RtoB
         ty
         (sprintf "%s.%s" !shallowfile (ident_to_string cid)))
  in
  sprintf
    "Theorem const_%s_corres :\n%s%s.\nProof.\n%sreflexivity.\nQed."
    (ident_to_string cid)
    indent
    thm
    indent

let gen_deep_call_args (args : (ident * mtyp) list) : string =
  match args with
  | [] -> "tt"
  | _ ->
      list_to_string
        ~delim:("", "")
        ~sep:" "
        (fun (aid, aty) ->
          let aid = ident_to_string aid in
          RecordConv.conv_value_opt_parens RecordConv.RtoB aty aid)
        args

let gen_shallow_call_ret (call : string) (ty : mtyp) : string =
  match ty with
  | MRes tr ->
      let conv_v = RecordConv.conv_value RecordConv.RtoB tr "r" in
      if conv_v = "r" then call
      else sprintf "let* r := %s in\n%s OK (%s)" call indent conv_v
  | _ ->
      sprintf
        "OK (%s)"
        (RecordConv.conv_value RecordConv.RtoB ty (sprintf "(%s)" call))

let gen_function_corres (fid : ident) (params : (ident * mtyp) list)
    (tret : mtyp) : string =
  let forall =
    match params with
    | [] -> ""
    | _ -> sprintf "forall %s," (Shallowgen.param_list_to_rocq params)
  in
  let deep_fun_id = Deepgen.ident_to_deep fid in
  let shallow_fun_id = ident_to_string fid in
  let deep_call =
    sprintf "%s_val %s" shallow_fun_id (gen_deep_call_args params)
  in
  let shallow_call =
    let args =
      match params with
      | [] -> "tt"
      | _ ->
          list_to_string
            ~delim:("", "")
            ~sep:" "
            ident_to_string
            (List.map fst params)
    in
    let call = sprintf "%s.%s %s" !shallowfile shallow_fun_id args in
    gen_shallow_call_ret call tret
  in
  sprintf
    "Theorem fun_%s_corres :\n\
     %sexists %s_val,\n\
     %seval_def %s = OK (VAL Deeptypes.typof_%s %s_val) /\\\n\
     %s(%s\n\
     %s %s =\n\
     %s %s).\n\
     Admitted."
    shallow_fun_id
    indent
    shallow_fun_id
    indent
    deep_fun_id
    shallow_fun_id
    shallow_fun_id
    indent
    forall
    indent
    deep_call
    indent
    shallow_call

let print_defs_corres (out : out_channel) (defs : globdef list) : unit =
  print_list
    out
    ~delim:("", "\n")
    ~sep:"\n\n"
    (fun (d : BarocqShallow.Monadic.globdef) ->
      match d with
      | DefConst (cid, _, ty) | DeclConst (cid, ty) -> gen_const_corres cid ty
      | DefFun (fid, f) -> gen_function_corres fid f.fn_params f.fn_return
      | DeclFun (fid, tparams, tret) ->
          let params =
            List.mapi
              (fun i (_, fty) -> (ident_of_string (sprintf "a%d" i), fty))
              tparams
          in
          gen_function_corres fid params tret)
    defs

let prelude_imports () : string =
  sprintf
    "From Coq Require Import BinPosDef String List.\n\
     From compcert Require Import Integers Maps Clightdefs.\n\
     From BarocqComp Require Import Error Barray Brecord Types Barocq.\n\
     From %s Require Import %s %s.\n\n\
     Import ClightNotations.\n\
     Import ListNotations.\n\n\
     Open Scope string_scope.\n\
     Open Scope clight_scope.\n"
    !coqlib
    !shallowfile
    !deepfile

let imports () : string =
  sprintf
    "From Coq Require Import BinPosDef String List.\n\
     From compcert Require Import Integers Maps Clightdefs.\n\
     From BarocqComp Require Import Target Monads Error Barray Brecord Types \
     Barocq.\n\
     From %s Require Import %s %s %s_CorresPrelude.\n\n\
     Import ClightNotations.\n\
     Import ListNotations.\n\n\
     Open Scope string_scope.\n\
     Open Scope clight_scope.\n"
    !coqlib
    !shallowfile
    !deepfile
    !coqlib

let print_prelude (out : out_channel) (prog : program) : unit =
  let types = prog.prog_types in
  let records = get_record_defs types in
  let defs = prog.prog_defs in
  fprintf out "%s" (prelude_imports ());
  Deeptypes.print out prog;
  Brecordtypes.print out prog;
  fprintf out "\n";
  fprintf out "(** * Abstract types implementation *)\n\n";
  fprintf out "%s" (gen_abs_types_impl_env types);
  if records <> [] then begin
    fprintf out "\n";
    fprintf
      out
      "Local Notation \"# X\" := (Types.eval_typ abs_types_impl X) (at level \
       90).\n";
    RecordConv.print_conversions out records;
    fprintf out "\n";
    RecordConv.print_correctness_lemmas out records
  end;
  let exists_absdef =
    List.exists
      (fun (d : BarocqShallow.Monadic.globdef) ->
        match d with
        | DeclConst _ | DeclFun _ -> true
        | _ -> false)
      defs
  in
  if exists_absdef then begin
    fprintf out "\n";
    fprintf out "(** * FFI *)\n\n";
    FFI.print_functions out defs
  end;
  fprintf out "\n";
  fprintf out "Definition VAL (t: typ) (v: #t) := Val abs_types_impl t v.\n";
  fprintf out "\n";
  fprintf out "%s" (gen_abs_defs_impl_env defs)

let print_corres (arch : Target.archi) (out : out_channel) (prog : program) :
    unit =
  let arch_str =
    match arch with
    | Target.Ptr32 -> "Ptr32"
    | Target.Ptr64 -> "Ptr64"
  in
  let defs = prog.prog_defs in
  fprintf out "%s" (imports ());
  fprintf out "\n";
  fprintf out "(** * Program correspondence theorems *)\n\n";
  fprintf
    out
    "Definition eval_def := Barocq.eval_def %s abs_types_impl abs_defs_impl \
     %s.prog.\n"
    arch_str
    !deepfile;
  if defs <> [] then begin
    fprintf out "\n";
    print_defs_corres out defs
  end
