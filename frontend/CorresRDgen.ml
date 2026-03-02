open Printf
open Syntax
open BarocqShallow.Monadic
open PrintUtils
open Btypesgen

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

  let type_def_to_string (indent : string)
      ((tname, td) : ident * (mtyp * Types.layout) type_def) : string =
    match td with
    | TdEnum elems ->
        let eid = ident_to_string tname in
        let elems =
          sprintf
            "%sDefinition elems_of_%s : list ident := %s.\n"
            indent
            eid
            (list_to_string_bracket Deepgen.ident_to_deep elems)
        in
        sprintf
          "%s\n%sDefinition %s : typ := TEnum %s elems_of_%s."
          elems
          indent
          eid
          (Deepgen.ident_to_deep tname)
          eid
    | TdRecord fields ->
        let rid = ident_to_string tname in
        let fields =
          sprintf
            "%sDefinition fields_of_%s : list (ident * typ) := %s.\n"
            indent
            rid
            (list_to_string_bracket
               (fun (fname, (fty, _)) ->
                 sprintf
                   "(%s, %s)"
                   (Deepgen.ident_to_deep fname)
                   (mtyp_to_typ_string fty))
               fields)
        in
        sprintf
          "%s\n%sDefinition %s : typ := TRecord %s fields_of_%s."
          fields
          indent
          (ident_to_string tname)
          (Deepgen.ident_to_deep tname)
          rid

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

  let print_typedefs (out : out_channel)
      (types : (mtyp * Types.layout) type_def Maps2.smaplist) : unit =
    print_list
      out
      ~delim:("", "\n")
      ~sep:"\n\n"
      (fun td -> type_def_to_string indent td)
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
      print_typedefs out types;
      fprintf out "\n"
    end;
    if defs <> [] then begin
      print_deftypes out prog.prog_defs;
      fprintf out "\n"
    end;
    fprintf out "End Deeptypes.\n"
end

let gen_const_corres (cid : ident) (ty : mtyp) : string =
  let thm =
    sprintf
      "eval_def %s = Some (VAL Deeptypes.typof_%s (%s))"
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
      else sprintf "%slet* r := %s in\n%sSome (%s)" indent call indent v_conv
  | _ ->
      sprintf
        "%sSome %s"
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
  let corres =
    if forall = "" then sprintf "%s(%s =\n%s)" indent call_deep call_shallow
    else
      sprintf "%s(%s\n%s %s =\n%s)" indent forall indent call_deep call_shallow
  in
  let proof =
    sprintf
      "%spose proof %s_CorresBD.fun_%s_corres as [%s_val [Heval HcorresBD]].\n\
       %sexists %s_val. split.\n\
       %s- exact Heval.\n\
       %s- intros.%s\n\
       %srewrite HcorresBD. rewrite %s_CorresRB.fun_%s_corres.\n\
       %sreflexivity."
      indent
      !coqlib
      fid_shallow
      fid_shallow
      indent
      fid_shallow
      indent
      indent
      (if params <> [] then
         sprintf
           " specialize (HcorresBD %s)."
           (fun_corres_deep_call_args params)
       else "")
      indent2
      !coqlib
      fid_shallow
      indent2
  in
  sprintf
    "Theorem fun_%s_corres :\n\
     %sexists %s_val,\n\
     %seval_def %s = Some (VAL Deeptypes.typof_%s %s_val) /\\\n\
     %s.\n\
     Proof.\n\
     %s\n\
     Qed."
    fid_shallow
    indent
    fid_shallow
    indent
    fid_deep
    fid_shallow
    fid_shallow
    corres
    proof

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

let imports () : string =
  sprintf
    "From Coq Require Import String.\n\
     From compcert Require Import Integers.\n\
     From BarocqComp Require Import Target Monads OptionMonad Barray Brecord \
     Types Barocq.\n\
     From %s Require Import %s_Types %s %s %s_CorresBD_Prelude.\n\
     From %s Require %s_CorresRB %s_CorresBD.\n\n\
     Open Scope string_scope.\n"
    !coqlib
    !coqlib
    !shallowfile
    !deepfile
    !coqlib
    !coqlib
    !coqlib
    !coqlib

let print_corres (out : out_channel) (arch : Target.archi) (prog : program) :
    unit =
  shallowfile := sprintf "%s_ShallowR" !coqlib;
  deepfile := sprintf "%s_Deep" !coqlib;
  let defs = prog.prog_defs in
  fprintf out "%s" (imports ());
  fprintf out "\n";
  fprintf out "(** * Program correspondence theorems *)\n\n";
  fprintf out "Definition eval_def := %s_CorresBD.eval_def.\n" !coqlib;
  if defs <> [] then begin
    fprintf out "\n";
    print_defs_corres out defs
  end
