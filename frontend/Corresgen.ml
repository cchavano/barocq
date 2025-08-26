open Printf
open Syntax
open BarocqShallow.Monadic
open PrintUtils

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
        "Definition tbool := TBool.";
        "Definition tint32 := TInt32 Signed.";
        "Definition tuint32 := TInt32 Unsigned.";
        "Definition tint64 := TInt64 Signed.";
        "Definition tuint64 := TInt64 Unsigned.";
      ]

  let rec is_simpl_mtyp (ty : mtyp) : bool =
    match ty with
    | MBool | MInt32 _ | MInt64 _ | MRecord _ -> true
    | MRes tr -> is_simpl_mtyp tr
    | _ -> false

  let rec mtyp_to_typ_string (ty : mtyp) : string =
    match ty with
    | MBool -> "tbool"
    | MInt32 Types.Signed -> "tint32"
    | MInt32 Types.Unsigned -> "tuint32"
    | MInt64 Types.Signed -> "tint64"
    | MInt64 Types.Unsigned -> "tuint64"
    | MArray ta -> sprintf "TArray %s" (opt_parens ta)
    | MEnum eid -> ident_to_string eid
    | MRecord rid -> ident_to_string rid
    | MFun (tparams, tret) ->
        sprintf
          "TFun %s %s"
          (list_to_string_bracket mtyp_to_typ_string tparams)
          (opt_parens tret)
    | MAbs tid -> ident_to_string tid
    | MRes tr -> mtyp_to_typ_string tr

  and opt_parens (ty : mtyp) : string =
    PrintUtils.opt_parens is_simpl_mtyp mtyp_to_typ_string ty

  let typedef_to_string (indent : string) (td : type_def) : string =
    match td with
    | TdEnum ed ->
        let eid = ident_to_string ed.ed_name in
        let elems =
          sprintf
            "%sDefinition elems_of_%s : list ident := %s.\n"
            indent
            eid
            (list_to_string_bracket Deepgen.ident_to_deep ed.ed_elems)
        in
        sprintf
          "%s\n%sDefinition %s : typ := TEnum %s elems_of_%s."
          elems
          indent
          eid
          (Deepgen.ident_to_deep ed.ed_name)
          eid
    | TdRecord rd ->
        let rid = ident_to_string rd.rd_name in
        let fields =
          sprintf
            "%sDefinition fields_of_%s : list (ident * typ) := %s.\n"
            indent
            rid
            (list_to_string_bracket
               (fun (fname, fty) ->
                 sprintf
                   "(%s, %s)"
                   (Deepgen.ident_to_deep fname)
                   (mtyp_to_typ_string fty))
               rd.rd_fields)
        in
        sprintf
          "%s\n%sDefinition %s : typ := TRecord %s fields_of_%s."
          fields
          indent
          (ident_to_string rd.rd_name)
          (Deepgen.ident_to_deep rd.rd_name)
          rid
    | TdAbstract (tid, _) ->
        sprintf
          "%sDefinition %s : typ := TAbs %s."
          indent
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
      (fun td -> sprintf "%s" (typedef_to_string indent td))
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
      ~sep:";\n"
      (fun (d, s) -> sprintf "%s(%s, %s.%s : Type)" prefix d !shallowfile s)
      l
  in
  let env_build env_list l =
    let indent2 = make_indent 2 in
    sprintf
      "List.fold_left\n\
       %s(fun ge '(d, s) => SMap.set d s ge)\n\
       %s[\n\
       %s\n\
       %s]\n\
       %s(SMap.init (unit : Type))"
      indent2
      indent2
      (env_list (make_indent 3) l)
      indent2
      indent2
  in
  let l = lassoc types in
  sprintf
    "Definition abs_types_impl : SMap.t Type :=\n%s%s.\n"
    indent
    (match l with
    | [] -> "SMap.init (unit : Type)"
    | _ -> env_build env_list (lassoc types))

module Btypedefs = struct
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
    | MEnum te -> sprintf "enum %s" (ident_to_string te)
    | MRecord tr -> sprintf "record %s" (ident_to_string tr)
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
    PrintUtils.opt_parens is_simpl_mtyp mtyp_to_string ty

  let enum_def_to_string (ed : enum_def) : string =
    sprintf
      "Definition %s : list ident := %s."
      (ident_to_string ed.ed_name)
      (list_to_string_bracket Deepgen.ident_to_deep ed.ed_elems)

  let record_def_to_string (rd : record_def) : string =
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

  let type_def_to_string (td : type_def) : string =
    match td with
    | TdEnum ed -> enum_def_to_string ed
    | TdRecord rd -> record_def_to_string rd
    | TdAbstract _ -> assert false

  let print_typedefs (out : out_channel) (types : type_def list) : unit =
    let types =
      List.filter
        (fun (td : BarocqShallow.Monadic.type_def) ->
          match td with
          | TdAbstract _ -> false
          | _ -> true)
        types
    in
    print_list
      out
      ~delim:("", "\n")
      ~sep:"\n\n"
      (fun td -> sprintf "%s%s" indent (type_def_to_string td))
      types

  let print (out : out_channel) (prog : program) : unit =
    let types = prog.prog_types in
    fprintf out "\n";
    fprintf out "Module Btypedefs.\n\n";
    if types <> [] then begin
      print_typedefs out prog.prog_types;
      fprintf out "\n"
    end;
    fprintf out "End Btypedefs.\n"
end

type direction =
  | RtoB
  | BtoR

let direction_to_string (d : direction) : string =
  match d with
  | RtoB -> "RtoB"
  | BtoR -> "BtoR"

let rec conv_mtyp_str (d : direction) (ty : mtyp) : string =
  match ty with
  | MEnum eid ->
      sprintf "econv_%s_%s" (ident_to_string eid) (direction_to_string d)
  | MRecord rid ->
      sprintf "rconv_%s_%s" (ident_to_string rid) (direction_to_string d)
  | MArray ta ->
      let r = conv_mtyp_str d ta in
      if r = "" then ""
      else if
        String.starts_with ~prefix:"rconv" r
        || String.starts_with ~prefix:"econv" r
      then sprintf "transl_array %s" r
      else sprintf "transl_array (%s)" r
  | _ -> ""

let conv_value (d : direction) (fty : mtyp) (v : string) : string =
  let tstr = conv_mtyp_str d fty in
  if tstr = "" then v else sprintf "%s %s" tstr v

let conv_value_opt_parens (d : direction) (fty : mtyp) (v : string) : string =
  let v_conv = conv_value d fty v in
  if v_conv = v then v else sprintf "(%s)" v_conv

module EnumConv = struct
  let econv_elems_RtoB (elems : ident list) : string =
    let rec aux (elems : ident list) (constr : string) (parens : string) :
        string =
      match elems with
      | [] -> assert false
      | i :: [] ->
          sprintf
            "%s| %s => %s (Constr %s)%s"
            indent
            (ident_to_string i)
            constr
            (Deepgen.ident_to_deep i)
            parens
      | i :: elems' ->
          let constr' = sprintf "%s (inr" constr in
          let parens' = sprintf "%s)" parens in
          sprintf
            "%s| %s => %s (inl (Constr %s))%s\n%s"
            indent
            (ident_to_string i)
            constr
            (Deepgen.ident_to_deep i)
            parens
            (aux elems' constr' parens')
    in
    match elems with
    | [] -> assert false
    | i :: elems' ->
        sprintf
          "%s| %s => inl (Constr %s)\n%s"
          indent
          (ident_to_string i)
          (Deepgen.ident_to_deep i)
          (aux elems' "inr" "")

  let gen_econv_RtoB (ed : enum_def) : string =
    let eid = ident_to_string ed.ed_name in
    sprintf
      "Definition econv_%s_RtoB (e: %s) : enum Btypedefs.%s :=\n\
       %smatch e with\n\
       %s\n\
       %send."
      eid
      eid
      eid
      indent
      (econv_elems_RtoB ed.ed_elems)
      indent

  let econv_elems_BtoR (elems : ident list) : string =
    let rec aux (elems : ident list) (constr : string) (parens : string) :
        string =
      match elems with
      | [] -> assert false
      | i :: [] ->
          sprintf "%s| %s _%s => %s" indent constr parens (ident_to_string i)
      | i :: elems' ->
          let constr' = sprintf "%s (inr" constr in
          let parens' = sprintf "%s)" parens in
          sprintf
            "%s| %s (inl _)%s => %s\n%s"
            indent
            constr
            parens
            (ident_to_string i)
            (aux elems' constr' parens')
    in
    match elems with
    | [] -> assert false
    | i :: elems' ->
        sprintf
          "%s| inl _ => %s\n%s"
          indent
          (ident_to_string i)
          (aux elems' "inr" "")

  let gen_econv_BtoR (ed : enum_def) : string =
    let eid = ident_to_string ed.ed_name in
    sprintf
      "Definition econv_%s_BtoR (e: enum Btypedefs.%s) : %s :=\n\
       %smatch e with\n\
       %s\n\
       %send."
      eid
      eid
      eid
      indent
      (econv_elems_BtoR ed.ed_elems)
      indent

  let gen_econv_inv1_thm (ed : enum_def) : string =
    let eid = ident_to_string ed.ed_name in
    sprintf
      "Theorem econv_%s_inv1 :\n\
       %sforall (e: %s.%s),\n\
       %seconv_%s_BtoR (econv_%s_RtoB e) = e.\n\
       Proof.\n\
       %sintro. destruct e; reflexivity.\n\
       Qed."
      eid
      indent
      !shallowfile
      eid
      indent
      eid
      eid
      indent

  let gen_econv_inv2_thm (ed : enum_def) : string =
    let eid = ident_to_string ed.ed_name in
    sprintf
      "Theorem econv_%s_inv2 :\n\
       %sforall (e: enum Btypedefs.%s),\n\
       %seconv_%s_RtoB (econv_%s_BtoR e) = e.\n\
       Proof.\n\
       %sintro. repeat destruct e; simpl; try (destruct c; reflexivity).\n\
       %sdestruct e. reflexivity.\n\
       Qed."
      eid
      indent
      eid
      indent
      eid
      eid
      indent
      indent

  let print_conversions (out : out_channel) (enums : enum_def list) : unit =
    if enums <> [] then begin
      fprintf out "(** * Barocq <-> Rocq enum conversions *)\n\n";
      print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_econv_RtoB enums;
      print_list out ~delim:("", "\n") ~sep:"\n\n" gen_econv_BtoR enums
    end

  let print_inversibility (out : out_channel) (enums : enum_def list) : unit =
    if enums <> [] then begin
      fprintf out "(** * Barocq <-> Rocq enum conversions *)\n\n";
      print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_econv_inv1_thm enums;
      print_list out ~delim:("", "\n") ~sep:"\n\n" gen_econv_inv2_thm enums
    end
end

module RecordConv = struct
  (* Rocq to Barocq *)

  let rconv_field_RtoB (rid : string) (fname : ident) (fty : mtyp)
      (arg : string) : string =
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

  let rconv_RtoB (rd : record_def) (arg : string) : string =
    List.fold_right
      (fun (fname, fty) acc ->
        sprintf
          "(%s, %s)"
          (rconv_field_RtoB (ident_to_string rd.rd_name) fname fty arg)
          acc)
      rd.rd_fields
      "tt"

  let gen_rconv_RtoB (rd : record_def) : string =
    let rid = ident_to_string rd.rd_name in
    sprintf
      "Definition rconv_%s_RtoB (r: %s.%s) : record Btypedefs.%s :=\n%s%s."
      rid
      !shallowfile
      rid
      rid
      indent
      (rconv_RtoB rd "r")

  (* Barocq to Rocq *)

  let rec rconv_letmon_BtoR (fields : (ident * mtyp) list) : string =
    match fields with
    | [] -> ""
    | (fname, fty) :: fields' ->
        let fid = ident_to_string fname in
        let v_conv = conv_value BtoR fty fid in
        if v_conv = fid then rconv_letmon_BtoR fields'
        else
          sprintf
            "%slet* %s := %s in\n%s"
            (make_indent 3)
            fid
            v_conv
            (rconv_letmon_BtoR fields')

  let rconv_BtoR (rd : record_def) : string =
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
           ~sep:" "
           (fun (fname, fty) ->
             conv_value_opt_parens BtoR fty (ident_to_string fname))
           rd.rd_fields)
    in
    sprintf
      "%smatch r with\n%s| %s =>\n%s%s\n%send"
      indent
      indent
      match_case
      (make_indent 3)
      mk_record
      indent

  let gen_rconv_BtoR (rd : record_def) : string =
    let rid = ident_to_string rd.rd_name in
    sprintf
      "Definition rconv_%s_BtoR (r: record Btypedefs.%s) : %s.%s :=\n%s."
      rid
      rid
      !shallowfile
      rid
      (rconv_BtoR rd)

  (* Main printing function *)

  let print_conversions (out : out_channel) (records : record_def list) : unit =
    if records <> [] then begin
      fprintf out "(** * Barocq <-> Rocq record conversions **)\n\n";
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
      print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_rconv_RtoB records;
      print_list out ~delim:("", "\n") ~sep:"\n\n" gen_rconv_BtoR records
    end

  (* Correctness theorems *)

  let gen_rconv_RtoB_correctness_thm (rd : record_def) : string =
    let rid = ident_to_string rd.rd_name in
    let forall = sprintf "forall (r: %s) (b: record Btypedefs.%s)," rid rid in
    let conv_call = sprintf "rconv_%s_RtoB r = b" rid in
    let fields_conv =
      list_to_string
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
            "%s@Brecord.proj Btypedefs.%s b %s = OK %s"
            indent
            rid
            (Deepgen.ident_to_deep fname)
            rproj)
        rd.rd_fields
    in
    let proof = sprintf "Proof.\n%sintros. subst. repeat split.\nQed." indent in
    sprintf
      "Lemma rconv_%s_RtoB_correct :\n%s%s\n%s%s ->\n%s.\n%s"
      rid
      indent
      forall
      indent
      conv_call
      fields_conv
      proof

  let gen_rconv_BtoR_correctness_thm (rd : record_def) : string =
    let rid = ident_to_string rd.rd_name in
    let forall = sprintf "forall (b: record Btypedefs.%s) (r: %s)," rid rid in
    let conv_call = sprintf "rconv_%s_BtoR b = r" rid in
    let field_conv (fname : ident) (fty : mtyp) : string =
      let fid = ident_to_string fname in
      let rval = conv_value BtoR fty fid in
      if rval = fid then
        sprintf
          "%s@Brecord.proj Btypedefs.%s b %s = OK r.(%s_%s)"
          indent
          rid
          (Deepgen.ident_to_deep fname)
          (String.lowercase_ascii rid)
          fid
      else
        sprintf
          "%s(exists %s, @Brecord.proj Btypedefs.%s b %s = OK %s /\\ %s = \
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
         %s(* intros b r Hconv. unfold rconv_%s_BtoR in Hconv. compute in b.\n\
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
      "Lemma rconv_%s_BtoR_correct :\n%s%s\n%s%s ->\n%s.\n%s"
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
      gen_rconv_RtoB_correctness_thm
      records;
    print_list
      out
      ~delim:("", "\n")
      ~sep:"\n\n"
      gen_rconv_BtoR_correctness_thm
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
    | MEnum te -> sprintf "enum Btypedefs.%s" (ident_to_string te)
    | MRecord t -> sprintf "record Btypedefs.%s" (ident_to_string t)
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
    PrintUtils.opt_parens is_simpl_mtyp mtyp_to_string ty

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
             let conv_arg = conv_value BtoR ty arg in
             if conv_arg = arg then (ctr + 1, str)
             else
               let str' =
                 sprintf
                   "%s%slet %s := %s in\n"
                   str
                   (make_indent 3)
                   arg
                   (conv_value BtoR ty arg)
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
      sprintf "%sret %s." (make_indent 3) (conv_value_opt_parens RtoB tret "r")
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
              (conv_value RtoB t (sprintf "%s.%s" !shallowfile cid))
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
      ~sep:";\n"
      (fun (d, s) ->
        sprintf "%s(%s, VAL Deeptypes.typof_%s FFI.%s)" prefix d s s)
      l
  in
  let genv_build genv_list l =
    let indent2 = make_indent 2 in
    sprintf
      "List.fold_left\n\
       %s(fun ge '(d, s) => STree.set d s ge)\n\
       %s[\n\
       %s\n\
       %s]\n\
       %sSTree.empty"
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
    | [] -> "STree.empty"
    | _ -> genv_build genv_list l)

let gen_const_corres (cid : ident) (ty : mtyp) : string =
  let thm =
    sprintf
      "eval_def %s = OK (VAL Deeptypes.typof_%s %s)"
      (Deepgen.ident_to_deep cid)
      (ident_to_string cid)
      (conv_value RtoB ty (sprintf "%s.%s" !shallowfile (ident_to_string cid)))
  in
  sprintf
    "Theorem const_%s_corres :\n%s%s.\nProof.\n%sreflexivity.\nQed."
    (ident_to_string cid)
    indent
    thm
    indent

let fun_corres_deep_call_args (args : (ident * mtyp) list) : string =
  match args with
  | [] -> "tt"
  | _ ->
      list_to_string
        ~sep:" "
        (fun (aid, aty) ->
          let aid = ident_to_string aid in
          conv_value_opt_parens RtoB aty aid)
        args

let fun_corres_shallow_call_ret (indent : string) (call : string) (ty : mtyp) :
    string =
  match ty with
  | MRes tr ->
      let v_conv = conv_value RtoB tr "r" in
      if v_conv = "r" then sprintf "%s%s" indent call
      else sprintf "%slet* r := %s in\n%sOK (%s)" indent call indent v_conv
  | _ ->
      sprintf
        "%sOK %s"
        indent
        (conv_value_opt_parens RtoB ty (sprintf "(%s)" call))

let fun_corres_forall (params : (ident * mtyp) list) : string =
  match params with
  | [] -> ""
  | _ -> sprintf "forall %s," (Shallowgen.param_list_to_rocq params)

let fun_corres_shallow_call (indent : string) (fid : ident)
    (params : (ident * mtyp) list) (tret : mtyp) : string =
  let args =
    match params with
    | [] -> "tt"
    | _ -> list_to_string ~sep:" " ident_to_string (List.map fst params)
  in
  let call = sprintf "%s.%s %s" !shallowfile (ident_to_string fid) args in
  fun_corres_shallow_call_ret indent call tret

let gen_fun_corres (fid : ident) (params : (ident * mtyp) list) (tret : mtyp) :
    string =
  let forall = fun_corres_forall params in
  let fid_deep = Deepgen.ident_to_deep fid in
  let fid_shallow = ident_to_string fid in
  let call_deep =
    sprintf "%s_val %s" fid_shallow (fun_corres_deep_call_args params)
  in
  let call_shallow = fun_corres_shallow_call (indent ^ " ") fid params tret in
  sprintf
    "Theorem fun_%s_corres :\n\
     %sexists %s_val,\n\
     %seval_def %s = OK (VAL Deeptypes.typof_%s %s_val) /\\\n\
     %s(%s\n\
     %s %s =\n\
     %s).\n\
     Admitted."
    fid_shallow
    indent
    fid_shallow
    indent
    fid_deep
    fid_shallow
    fid_shallow
    indent
    forall
    indent
    call_deep
    call_shallow

let params_of_absfun (tparams : (param_attr * mtyp) list) : (ident * mtyp) list
    =
  List.mapi (fun i (_, fty) -> (ident_of_string (sprintf "a%d" i), fty)) tparams

let print_defs_corres (out : out_channel) (defs : globdef list) : unit =
  print_list
    out
    ~delim:("", "\n")
    ~sep:"\n\n"
    (fun (d : BarocqShallow.Monadic.globdef) ->
      match d with
      | DefConst (cid, _, ty) | DeclConst (cid, ty) -> gen_const_corres cid ty
      | DefFun (fid, f) -> gen_fun_corres fid f.fn_params f.fn_return
      | DeclFun (fid, tparams, tret) ->
          let params = params_of_absfun tparams in
          gen_fun_corres fid params tret)
    defs

let gen_def_property (d : globdef) : string =
  let indent3 = make_indent 3 in
  let indent4 = make_indent 4 in
  let gen_const_property (cid : ident) : string =
    let cid_str = ident_to_string cid in
    sprintf
      "(%s,\n\
       %sfun (t: typ) (v: #t) =>\n\
       %smatch typ_eq_dec t Deeptypes.typof_%s with\n\
       %s| left EQ => cast EQ v = %s.%s\n\
       %s| _ => False\n\
       %send)"
      (Deepgen.ident_to_deep cid)
      indent3
      indent4
      cid_str
      indent4
      !shallowfile
      cid_str
      indent4
      indent4
  in
  let gen_fun_property (fid : ident) (params : (ident * mtyp) list)
      (tret : mtyp) : string =
    let fid_deep = Deepgen.ident_to_deep fid in
    let fid_shallow = ident_to_string fid in
    let forall =
      if params = [] then ""
      else sprintf "%s%s\n" (make_indent 6) (fun_corres_forall params)
    in
    let call_deep =
      sprintf "(cast EQ v) %s" (fun_corres_deep_call_args params)
    in
    let call_shallow =
      fun_corres_shallow_call (make_indent 6) fid params tret
    in
    sprintf
      "(%s,\n\
       %sfun (t: typ) (v: #t) =>\n\
       %smatch typ_eq_dec t Deeptypes.typof_%s with\n\
       %s| left EQ =>\n\
       %s%s%s =\n\
       %s\n\
       %s| _ => False\n\
       %send)"
      fid_deep
      indent3
      indent4
      fid_shallow
      indent4
      forall
      (make_indent 6)
      call_deep
      call_shallow
      indent4
      indent4
  in
  match d with
  | DefConst (cid, _, _) | DeclConst (cid, _) -> gen_const_property cid
  | DefFun (fid, f) -> gen_fun_property fid f.fn_params f.fn_return
  | DeclFun (fid, tparams, tret) ->
      let params = params_of_absfun tparams in
      gen_fun_property fid params tret

let print_properties_envs (out : out_channel) (defs : globdef list) : unit =
  let propt =
    "Definition propt : Type := string * (forall t : typ, # t -> Prop)."
  in
  let cast =
    "Definition cast {t1 t2: typ} := @Types.typ_cast t1 t2 abs_types_impl."
  in
  let has_property =
    sprintf
      "Definition has_property (ge : genv abs_types_impl) (p : propt) :=\n\
       %sexists t (v: #t), genv_get abs_types_impl ge (fst p) = OK (VAL t v) \
       /\\ (snd p) t v."
      indent
  in
  fprintf out "%s\n" propt;
  fprintf out "\n";
  fprintf out "%s\n" cast;
  fprintf out "\n";
  let decls =
    List.filter
      (fun (d : BarocqShallow.Monadic.globdef) ->
        match d with
        | DeclConst _ | DeclFun _ -> true
        | _ -> false)
      defs
  in
  let defs =
    List.filter
      (fun (d : BarocqShallow.Monadic.globdef) ->
        match d with
        | DefConst _ | DefFun _ -> true
        | _ -> false)
      defs
  in
  fprintf out "Definition decl_prop : list propt :=\n";
  print_list
    out
    ~delim:(sprintf "%s[\n%s" indent (make_indent 2), sprintf "\n%s].\n" indent)
    ~sep:(sprintf ";\n%s" (make_indent 2))
    gen_def_property
    decls;
  fprintf out "\n";
  fprintf out "Definition def_prop : list propt :=\n";
  print_list
    out
    ~delim:(sprintf "%s[\n%s" indent (make_indent 2), sprintf "\n%s].\n" indent)
    ~sep:(sprintf ";\n%s" (make_indent 2))
    gen_def_property
    defs;
  fprintf out "\n";
  fprintf out "%s\n" has_property

let print_typing_env (out : out_channel) (types : type_def list) : unit =
  let type_def_to_string (td : type_def) : string =
    match td with
    | TdEnum ed ->
        sprintf
          "%s (Adt_enum Deeptypes.elems_of_%s)"
          (Deepgen.ident_to_deep ed.ed_name)
          (ident_to_string ed.ed_name)
    | TdRecord rd ->
        sprintf
          "%s (Adt_record Deeptypes.fields_of_%s)"
          (Deepgen.ident_to_deep rd.rd_name)
          (ident_to_string rd.rd_name)
    | TdAbstract _ -> assert false
  in
  let rec tenv_defs_to_string (indent : string) (types : type_def list) : string
      =
    match types with
    | [] -> "STree.empty"
    | td :: types' ->
        sprintf
          "STree.set %s\n%s(%s)"
          (type_def_to_string td)
          indent
          (tenv_defs_to_string (indent ^ PrintUtils.indent) types')
  in
  let rec tenv_enum_def_constr_types (indent : string) (eid : string)
      (elems : ident list) (next : string) : string =
    match elems with
    | [] -> next
    | e :: elems' ->
        sprintf
          "STree.set %s %s\n%s(%s)"
          (Deepgen.ident_to_deep e)
          eid
          indent
          (tenv_enum_def_constr_types
             (indent ^ PrintUtils.indent)
             eid
             elems'
             next)
  in
  let rec tenv_constr_types_to_string (indent : string) (types : type_def list)
      : string =
    match types with
    | [] -> "STree.empty"
    | TdEnum ed :: types' ->
        let indent' =
          sprintf "%s%s" indent (make_indent (List.length ed.ed_elems))
        in
        tenv_enum_def_constr_types
          indent
          (Deepgen.ident_to_deep ed.ed_name)
          ed.ed_elems
          (tenv_constr_types_to_string indent' types')
    | _ :: types' -> tenv_constr_types_to_string indent types'
  in
  let types =
    List.filter
      (fun (td : BarocqShallow.Monadic.type_def) ->
        match td with
        | TdAbstract _ -> false
        | _ -> true)
      types
  in
  fprintf
    out
    "Definition typing_env : tenv := {|\n\
     %stenv_defs :=\n\
     %s%s;\n\
     %stenv_constr_types :=\n\
     %s%s\n\
     |}.\n"
    indent
    (make_indent 2)
    (tenv_defs_to_string (make_indent 3) types)
    indent
    (make_indent 2)
    (tenv_constr_types_to_string (make_indent 3) types)

module VCgen = struct
  let ident_of_globdef (d : globdef) : ident =
    match d with
    | DefConst (x, _, _) | DefFun (x, _) | DeclConst (x, _) | DeclFun (x, _, _)
      -> x

  let rec print_needed_checked_lists (out : out_channel)
      (bprog : Barocq.program) (sdefs : globdef list) : unit =
    match bprog with
    | [] -> ()
    | bd :: bprog' ->
        begin
          match bd with
          | Barocq.DefFun (fid, f) ->
              let vars =
                BarocqVC.vars_of_expr Maps2.STree.empty f.Syntax.fn_body
              in
              let sdefs_needed =
                List.filter
                  (fun (d : BarocqShallow.Monadic.globdef) ->
                    BarocqVC.has_var (ident_of_globdef d) vars)
                  sdefs
              in
              fprintf
                out
                "%slet needed_checked_%s : list propt := "
                indent
                (ident_to_string fid);
              let delim =
                if sdefs_needed = [] then ("[", "]")
                else (sprintf "[\n%s" (make_indent 2), sprintf "\n%s]\n" indent)
              in
              print_list
                out
                ~delim
                ~sep:(sprintf ";\n%s" (make_indent 2))
                gen_def_property
                sdefs_needed;
              fprintf out "%sin\n" indent
          | Barocq.DeclFun (fid, _, _) ->
              fprintf
                out
                "%slet needed_checked_%s : list propt := [] in\n"
                indent
                (ident_to_string fid)
          | _ -> ()
        end;
        print_needed_checked_lists out bprog' sdefs

  let gen_fun_params (fid : ident) (params : (ident * mtyp) list) : string =
    let params_str =
      list_to_string_bracket
        (fun (pid, pty) ->
          sprintf
            "(%s, Deeptypes.%s)"
            (Deepgen.ident_to_deep pid)
            (Deeptypes.mtyp_to_typ_string pty))
        params
    in
    sprintf
      "%slet params_%s : list (ident * typ) := %s in"
      indent
      (ident_to_string fid)
      params_str

  let rec print_functions_params (out : out_channel) (sdefs : globdef list) :
      unit =
    match sdefs with
    | [] -> ()
    | d :: sdefs' ->
        begin
          match d with
          | DefFun (fid, f) ->
              fprintf out "%s\n" (gen_fun_params fid f.fn_params)
          | DeclFun (fid, tparams, tret) ->
              let params = params_of_absfun tparams in
              fprintf out "%s\n" (gen_fun_params fid params)
          | _ -> ()
        end;
        print_functions_params out sdefs'

  let gen_const_vc (is_abs : bool) (cid : ident) (ty : mtyp) : string =
    let indent2 = make_indent 2 in
    let indent3 = make_indent 3 in
    let cid_str = ident_to_string cid in
    let constval_shallow =
      conv_value RtoB ty (sprintf "%s.%s" !shallowfile cid_str)
    in
    if is_abs then sprintf "%sFFI.%s = %s" indent2 cid_str constval_shallow
    else
      let constval_deep =
        sprintf
          "Barocq.eval_literal abs_types_impl typing_env %s.const_%s"
          !deepfile
          cid_str
      in
      sprintf
        "%smatch %s with\n\
         %s| OK (Val _ tv v) =>\n\
         %smatch typ_eq_dec tv Deeptypes.typof_%s with\n\
         %s| left EQ => cast EQ v = %s\n\
         %s| _ => False\n\
         %send\n\
         %s| Error _ => False\n\
         %send"
        indent2
        constval_deep
        indent2
        indent3
        cid_str
        indent3
        constval_shallow
        indent3
        indent3
        indent2
        indent2

  let gen_fun_vc (is_abs : bool) (fid : ident) (params : (ident * mtyp) list)
      (tret : mtyp) : string =
    let indent3 = make_indent 3 in
    let fid_shallow = ident_to_string fid in
    let forall =
      if params = [] then ""
      else sprintf "%s%s\n" indent3 (fun_corres_forall params)
    in
    let call_deep = sprintf "v %s" (fun_corres_deep_call_args params) in
    let call_shallow = fun_corres_shallow_call indent3 fid params tret in
    let funval_deep =
      if is_abs then sprintf "FFI.%s" fid_shallow
      else
        sprintf
          "Barocq.build_funval arch abs_types_impl typing_env ge params_%s \
           Deeptypes.%s (Syntax.fn_body %s.fun_%s)"
          fid_shallow
          (Deeptypes.mtyp_to_typ_string tret)
          !deepfile
          fid_shallow
    in
    sprintf
      "%sforall (ge: genv abs_types_impl),\n\
       %sForall (has_property ge) needed_checked_%s ->\n\
       %slet v : #Deeptypes.typof_%s := %s in\n\
       %s%s%s =\n\
       %s"
      (make_indent 2)
      indent3
      fid_shallow
      indent3
      fid_shallow
      funval_deep
      forall
      indent3
      call_deep
      call_shallow

  let gen_def_vc (d : globdef) : string =
    match d with
    | DefFun (fid, f) -> gen_fun_vc false fid f.fn_params f.fn_return
    | DeclFun (fid, tparams, tret) ->
        let params = params_of_absfun tparams in
        gen_fun_vc true fid params tret
    | DefConst (cid, _, ty) -> gen_const_vc false cid ty
    | DeclConst (cid, ty) -> gen_const_vc true cid ty

  let archi_to_string (arch : Target.archi) : string =
    match arch with
    | Target.Ptr64 -> "Target.Ptr64"
    | Target.Ptr32 -> "Target.Ptr32"

  let print_vc (out : out_channel) (arch : Target.archi)
      (bprog : Barocq.program) (sprog : BarocqShallow.Monadic.program) : unit =
    let sdefs = sprog.prog_defs in
    fprintf out "Definition arch : Target.archi := %s.\n" (archi_to_string arch);
    fprintf out "\n";
    fprintf out "Definition vc : list Prop :=\n";
    print_needed_checked_lists out bprog sdefs;
    print_functions_params out sdefs;
    print_list
      out
      ~delim:(sprintf "%s[\n" indent, sprintf "\n%s]." indent)
      ~sep:(sprintf ";\n%s(* ========================== *)\n" (make_indent 2))
      gen_def_vc
      sdefs
end

let prelude_imports () : string =
  sprintf
    "From Coq Require Import String List.\n\
     From compcert Require Import Integers.\n\
     From BarocqComp Require Import Ident Error Maps2 Barray Benum Brecord \
     Types Typing Barocq.\n\
     From %s Require Import %s %s.\n\n\
     Import ListNotations.\n\n\
     Open Scope string_scope.\n"
    !coqlib
    !shallowfile
    !deepfile

let imports () : string =
  sprintf
    "From Coq Require Import String.\n\
     From compcert Require Import Integers.\n\
     From BarocqComp Require Import Target Monads Error Barray Brecord Types \
     Barocq.\n\
     From %s Require Import %s %s %s_CorresPrelude.\n\n\
     Open Scope string_scope.\n"
    !coqlib
    !shallowfile
    !deepfile
    !coqlib

let print_prelude (out : out_channel) (arch : Target.archi)
    (bprog : Barocq.program) (sprog : program) : unit =
  let types = sprog.prog_types in
  let records = get_record_defs types in
  let enums = get_enum_defs types in
  let defs = sprog.prog_defs in
  fprintf out "%s" (prelude_imports ());
  Deeptypes.print out sprog;
  Btypedefs.print out sprog;
  fprintf out "\n";
  fprintf out "(** * Abstract types implementation *)\n\n";
  fprintf out "%s" (gen_abs_types_impl_env types);
  if enums <> [] then begin
    fprintf out "\n";
    EnumConv.print_conversions out enums;
    fprintf out "\n";
    EnumConv.print_inversibility out enums
  end;
  if records <> [] then begin
    fprintf out "\n";
    RecordConv.print_conversions out records;
    fprintf out "\n";
    RecordConv.print_correctness_lemmas out records
  end;
  fprintf out "\n";
  fprintf
    out
    "Local Notation \"# X\" := (Types.eval_typ abs_types_impl X) (at level 90).\n";
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
  fprintf out "%s" (gen_abs_defs_impl_env defs);
  if types <> [] then begin
    fprintf out "\n";
    fprintf out "(** Typing environment *)\n";
    fprintf out "\n";
    print_typing_env out types
  end;
  if defs <> [] then begin
    fprintf out "\n";
    fprintf out "(** Properties environments *)\n";
    fprintf out "\n";
    print_properties_envs out defs;
    fprintf out "\n";
    VCgen.print_vc out arch bprog sprog
  end

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
    "Definition eval_def := Barocq.eval_def2 %s abs_types_impl abs_defs_impl \
     %s.prog.\n"
    arch_str
    !deepfile;
  if defs <> [] then begin
    fprintf out "\n";
    print_defs_corres out defs
  end
