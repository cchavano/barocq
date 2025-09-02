open Printf
open Syntax
open BarocqShallow.Monadic
open PrintUtils

let coqlib : string ref = ref ""

let gen_const_corres (cid : ident) (ty : mtyp) : string =
  let thm =
    sprintf
      "%s_ShallowB.%s = %s"
      !coqlib
      (ident_to_string cid)
      (Btypesgen.conv_value
         Btypesgen.RtoB
         ty
         (sprintf "%s_ShallowR.%s" !coqlib (ident_to_string cid)))
  in
  sprintf
    "Theorem const_%s_corres :\n%s%s.\nProof.\n%sreflexivity.\nQed."
    (ident_to_string cid)
    indent
    thm
    indent

let fun_corres_shallowB_call_args (args : (ident * mtyp) list) : string =
  match args with
  | [] -> "tt"
  | _ ->
      list_to_string
        ~sep:" "
        (fun (aid, aty) ->
          let aid = ident_to_string aid in
          Btypesgen.conv_value_opt_parens Btypesgen.RtoB aty aid)
        args

let fun_corres_shallowR_call_ret (indent : string) (call : string) (tr : mtyp)
    (tb : mtyp) : string =
  match (tr, tb) with
  | MRes tr, MRes _ ->
      let v_conv = Btypesgen.conv_value Btypesgen.RtoB tr "r" in
      if v_conv = "r" then sprintf "%s%s" indent call
      else
        sprintf
          "%smatch %s with\n%s| OK r => OK (%s)\n%s| Error e => Error e\n%send"
          indent
          call
          indent
          v_conv
          indent
          indent
  | _, MRes _ ->
      sprintf
        "%sOK %s"
        indent
        (Btypesgen.conv_value_opt_parens
           Btypesgen.RtoB
           tr
           (sprintf "(%s)" call))
  | MRes _, _ -> assert false
  | _, _ ->
      sprintf
        "%s%s"
        indent
        (Btypesgen.conv_value_opt_parens Btypesgen.RtoB tr (sprintf "%s" call))

let fun_corres_forall (params : (ident * mtyp) list) : string =
  match params with
  | [] -> ""
  | _ -> sprintf "forall %s," (Shallowgen.param_list_to_rocq params)

let fun_corres_shallowR_call (indent : string) (fid : ident)
    (params : (ident * mtyp) list) (tr : mtyp) (tb : mtyp) : string =
  let args =
    match params with
    | [] -> "tt"
    | _ -> list_to_string ~sep:" " ident_to_string (List.map fst params)
  in
  let call = sprintf "%s_ShallowR.%s %s" !coqlib (ident_to_string fid) args in
  fun_corres_shallowR_call_ret indent call tr tb

let gen_fun_corres (fid : ident) (params : (ident * mtyp) list) (tr : mtyp)
    (tb : mtyp) : string =
  let forall = fun_corres_forall params in
  let fid_shallow = ident_to_string fid in
  let call_shallowB =
    sprintf
      "%s_ShallowB.%s %s"
      !coqlib
      fid_shallow
      (fun_corres_shallowB_call_args params)
  in
  let call_shallowR = fun_corres_shallowR_call indent fid params tr tb in
  let corres =
    if forall = "" then sprintf "%s%s =\n%s" indent call_shallowB call_shallowR
    else
      sprintf
        "%s%s\n%s%s =\n%s"
        indent
        forall
        indent
        call_shallowB
        call_shallowR
  in
  sprintf "Theorem fun_%s_corres : \n%s.\nAdmitted." fid_shallow corres

let params_of_absfun (tparams : (param_attr * mtyp) list) : (ident * mtyp) list
    =
  List.mapi (fun i (_, fty) -> (ident_of_string (sprintf "a%d" i), fty)) tparams

let gen_def_corres (rdef : globdef) (bdef : globdef) : string =
  match (rdef, bdef) with
  | ( (DefConst (rcid, _, rty) | DeclConst (rcid, rty)),
      (DefConst (bcid, _, bty) | DeclConst (bcid, bty)) ) ->
      if rcid = bcid then gen_const_corres rcid rty else assert false
  | DefFun (rfid, rf), DefFun (bfid, bf) ->
      if rfid = bfid then
        gen_fun_corres rfid rf.fn_params rf.fn_return bf.fn_return
      else assert false
  | DeclFun (rfid, rtparams, tr), DeclFun (bfid, btparams, tb) ->
      if rfid = bfid then
        let params = params_of_absfun rtparams in
        gen_fun_corres rfid params tr tb
      else assert false
  | _ -> assert false

let rec print_defs_corres (out : out_channel) (rdefs : globdef list)
    (bdefs : globdef list) : unit =
  match (rdefs, bdefs) with
  | [], [] -> fprintf out "\n"
  | rd :: [], bd :: [] -> fprintf out "%s\n" (gen_def_corres rd bd)
  | rd :: rdefs', bd :: bdefs' ->
      fprintf out "%s\n\n" (gen_def_corres rd bd);
      print_defs_corres out rdefs' bdefs'
  | _ -> assert false

let imports () : string =
  sprintf
    "From compcert Require Import Integers.\n\
     From BarocqComp Require Import Error.\n\
     From %s Require Import %s_Types %s_ShallowR %s_ShallowB.\n"
    !coqlib
    !coqlib
    !coqlib
    !coqlib

let print_corres (out : out_channel) (rprog : program) (bprog : program) : unit
    =
  fprintf out "%s" (imports ());
  fprintf out "\n";
  print_defs_corres out rprog.prog_defs bprog.prog_defs
