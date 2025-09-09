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
      (fun (d, s) -> sprintf "%s(%s, %s : Type)" prefix d s)
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
      (fun (d, s) -> sprintf "%s(%s, VAL Deeptypes.typof_%s %s)" prefix d s s)
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
      (sprintf "%s.%s" !shallowfile (ident_to_string cid))
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
  | _ -> list_to_string ~sep:" " (fun (aid, _) -> ident_to_string aid) args

let fun_corres_shallow_call_ret (indent : string) (call : string) (ty : mtyp) :
    string =
  match ty with
  | MRes tr -> sprintf "%s%s" indent call
  | _ -> sprintf "%sOK (%s)" indent call

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
  sprintf
    "Theorem fun_%s_corres :\n\
     %sexists %s_val,\n\
     %seval_def %s = OK (VAL Deeptypes.typof_%s %s_val) /\\\n\
     %s.\n\
     Admitted."
    fid_shallow
    indent
    fid_shallow
    indent
    fid_deep
    fid_shallow
    fid_shallow
    corres

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
  let gen_const_property (cid : ident) : string =
    let cid_str = ident_to_string cid in
    sprintf
      "(%s,VAL Deeptypes.typof_%s %s.%s)"
      (Deepgen.ident_to_deep cid)
      cid_str
      !shallowfile
      cid_str
  in
  match d with
  | DefConst (cid, _, _) | DeclConst (cid, _) -> gen_const_property cid
  | DefFun (fid, _) -> gen_const_property fid
  | DeclFun (fid, _, _) -> gen_const_property fid

let print_properties_envs (out : out_channel) (defs : globdef list) : unit =
  let propt =
    "Definition propt : Type := string * value abs_types_impl."
  in
  fprintf out "%s\n" propt;
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
    defs

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
    "Definition typing_env : tenv := Eval compute in {|\n\
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
    let constval_shallow = sprintf "%s.%s" !shallowfile cid_str in
    if is_abs then
      sprintf "%s%s.%s = %s" indent2 !shallowfile cid_str constval_shallow
    else
      let constval_deep =
        sprintf
          "Barocq.eval_literal abs_types_impl typing_env %s.const_%s"
          !deepfile
          cid_str
      in
      sprintf
        "%s forall (u:unit),match %s with\n\
         %s| OK v => same_value abs_types_impl v (VAL Deeptypes.typof_%s %s) /\\ \n\
         %s typeof_value abs_types_impl v = Deeptypes.typof_%s \n\
         %s| Error _ => False\n\
         %send"
        indent2
        constval_deep
        (*  *)
        indent3
        cid_str
        constval_shallow
        (*   *)
        indent2
        cid_str
        indent3
        indent2

  let gen_fun_vc (is_abs : bool) (fid : ident) (params : (ident * mtyp) list)
      (tret : mtyp) : string =
    let indent3 = make_indent 3 in
      let fid_shallow = ident_to_string fid in
(*    let forall =
      if params = [] then ""
      else sprintf "%s%s\n" indent3 (fun_corres_forall params) 
      in *)
    (*    let call_deep = sprintf "v %s" (fun_corres_deep_call_args params)  in *)
    (*let call_shallow = fun_corres_shallow_call indent3 fid params tret in *)
    let funval_deep =
      if is_abs then sprintf "%s.%s" !shallowfile fid_shallow
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
      "%slet ge := genv_has_property abs_types_impl STree.empty needed_checked_%s in\n\
       %slet v : #Deeptypes.typof_%s := %s in\n\
       eq_value abs_types_impl (VAL Deeptypes.typof_%s %s) _ v\n"
      (make_indent 2)
      fid_shallow
      indent3
      fid_shallow
      funval_deep
      fid_shallow
      fid_shallow

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
    let isdef = function BarocqShallow.Monadic.DefConst _ | BarocqShallow.Monadic.DefFun _ -> true | _ -> false in
    let sdefs = List.filter isdef sdefs in
    fprintf out "Definition arch : Target.archi := %s.\n" (archi_to_string arch);
    fprintf out "\n";
    fprintf out "Definition vc : list Prop :=\n";
    print_needed_checked_lists out bprog sprog.prog_defs;
    print_functions_params out sdefs;
    print_list
      out
      ~delim:(sprintf "%s[\n" indent, sprintf "\n%s]." indent)
      ~sep:(sprintf ";\n%s(* ========================== *)\n" (make_indent 2))
      gen_def_vc
      (List.rev sdefs)
end

let prelude_imports () : string =
  sprintf
    "From Coq Require Import String List.\n\
     From compcert Require Import Integers.\n\
     From BarocqComp Require Import Ident Error Maps2 Barray Benum Brecord \
     Types Typing Barocq BarocqVC.\n\
     From %s Require Import %s_Types %s %s.\n\n\
     Import ListNotations.\n\n\
     Open Scope string_scope.\n"
    !coqlib
    !coqlib
    !shallowfile
    !deepfile

let imports () : string =
  sprintf
    "From Coq Require Import String.\n\
     From compcert Require Import Integers.\n\
     From BarocqComp Require Import Target Monads Error Barray Brecord Types \
     Barocq.\n\
     From %s Require Import %s_Types %s %s %s_CorresBD_Prelude.\n\n\
     Open Scope string_scope.\n"
    !coqlib
    !coqlib
    !shallowfile
    !deepfile
    !coqlib

let print_prelude (out : out_channel) (arch : Target.archi)
    (bprog : Barocq.program) (sprog : program) : unit =
  shallowfile := sprintf "%s_ShallowB" !coqlib;
  deepfile := sprintf "%s_Deep" !coqlib;
  let types = sprog.prog_types in
  let defs = sprog.prog_defs in
  fprintf out "%s" (prelude_imports ());
  Deeptypes.print out sprog;
  fprintf out "\n";
  fprintf out "(** * Abstract types implementation *)\n\n";
  fprintf out "%s" (gen_abs_types_impl_env types);
  fprintf out "\n";
  fprintf
    out
    "Local Notation \"# X\" := (Types.eval_typ abs_types_impl X) (at level 90).\n";
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

let print_corres (out : out_channel) (arch : Target.archi) (prog : program) :
    unit =
  shallowfile := sprintf "%s_ShallowB" !coqlib;
  deepfile := sprintf "%s_Deep" !coqlib;
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
