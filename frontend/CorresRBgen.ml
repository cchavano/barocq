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
      else sprintf "%slet* r := %s in\n%sSome (%s)" indent call indent v_conv
  | _, MRes _ ->
      sprintf
        "%sSome %s"
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

let param_to_rocq (shver : BarocqShallowgen.shallow_version)
    (param : ident * mtyp) : string =
  sprintf
    "(%s: %s)"
    (ident_to_string (fst param))
    (Btypesgen.mtyp_to_rocq shver (snd param))

let param_list_to_rocq (shver : BarocqShallowgen.shallow_version)
    (params : (ident * mtyp) list) : string =
  match params with
  | [] -> "(_: unit)"
  | _ -> list_to_string ~sep:" " (param_to_rocq shver) params

let fun_corres_forall (params : (ident * mtyp) list) : string =
  match params with
  | [] -> ""
  | _ ->
      sprintf "forall %s," (param_list_to_rocq BarocqShallowgen.ShallowR params)

let args_to_string (args : (ident * mtyp) list) : string =
  match args with
  | [] -> "tt"
  | _ -> list_to_string ~sep:" " ident_to_string (List.map fst args)

let fun_corres_shallowR_call (indent : string) (fid : ident)
    (params : (ident * mtyp) list) (tr : mtyp) (tb : mtyp) : string =
  let call =
    sprintf
      "%s_ShallowR.%s %s"
      !coqlib
      (ident_to_string fid)
      (args_to_string params)
  in
  fun_corres_shallowR_call_ret indent call tr tb

let fun_corres_statement (indent : string) (fid : ident)
    (params : (ident * mtyp) list) (tr : mtyp) (tb : mtyp) : string =
  let forall = fun_corres_forall params in
  let call_shallowB =
    sprintf
      "%s_ShallowB.%s %s"
      !coqlib
      (ident_to_string fid)
      (fun_corres_shallowB_call_args params)
  in
  let call_shallowR = fun_corres_shallowR_call indent fid params tr tb in
  if forall = "" then sprintf "%s%s =\n%s" indent call_shallowB call_shallowR
  else
    sprintf "%s%s\n%s%s =\n%s" indent forall indent call_shallowB call_shallowR

let gen_fun_corres (is_abs : bool) (fid : ident) (params : (ident * mtyp) list)
    (tr : mtyp) (tb : mtyp) : string =
  let fid_shallow = ident_to_string fid in
  let corres = fun_corres_statement indent fid params tr tb in
  let proof =
    if is_abs then
      let rewrites_conv =
        List.fold_left
          (fun acc (_, mty) ->
            match mty with
            | MEnum eid ->
                sprintf
                  "%s%srewrite econv_%s_inv1.\n"
                  acc
                  indent
                  (ident_to_string eid)
            | MRecord rid ->
                sprintf
                  "%s%srewrite rconv_%s_inv1.\n"
                  acc
                  indent
                  (ident_to_string rid)
            | _ -> acc)
          ""
          params
      in
      sprintf
        "Proof.\n\
         %sintros. unfold %s_ShallowB.%s.\n\
         %s%sdestruct (%s_ShallowR.%s %s); reflexivity.\n\
         Qed."
        indent
        !coqlib
        fid_shallow
        rewrites_conv
        indent
        !coqlib
        fid_shallow
        (args_to_string params)
    else
      let admitted = [] in
      if List.exists (String.equal fid_shallow) admitted then
        sprintf
          "Proof.\n\
           %sintros. unfold %s_ShallowB.%s; unfold %s_ShallowR.%s.\n\
           Admitted."
          indent
          !coqlib
          fid_shallow
          !coqlib
          fid_shallow
      else
        sprintf
          "Proof.\n\
           %sintros. unfold %s_ShallowB.%s; unfold %s_ShallowR.%s.\n\
           %scorres_rb_timeout.\n\
           Qed."
          indent
          !coqlib
          fid_shallow
          !coqlib
          fid_shallow
          indent
  in
  sprintf "Theorem fun_%s_corres : \n%s.\n%s" fid_shallow corres proof

let params_of_absfun (tparams : (param_attr * mtyp) list) : (ident * mtyp) list
    =
  List.mapi (fun i (_, fty) -> (ident_of_string (sprintf "a%d" i), fty)) tparams

let gen_def_corres (rdef : globdef) (bdef : globdef) : string =
  let fun_rewrite_material (fid : string) : string =
    sprintf
      "Opaque %s_ShallowR.%s.\n\
       Opaque %s_ShallowB.%s.\n\n\
       Instance RewriteRB_inst_%s : RewriteRB_%s := {\n\
       %scorresRB_%s := fun_%s_corres\n\
       }.\n"
      !coqlib
      fid
      !coqlib
      fid
      fid
      fid
      indent
      fid
      fid
  in
  match (rdef, bdef) with
  | ( (DefConst (rcid, _, rty) | DeclConst (rcid, rty)),
      (DefConst (bcid, _, bty) | DeclConst (bcid, bty)) ) ->
      if rcid = bcid then
        sprintf
          "%s\n\n\
           Hint Opaque %s : corresRB_consts.\n\
           Hint Rewrite const_%s_corres : corresRB_consts.\n"
          (gen_const_corres rcid rty)
          (ident_to_string rcid)
          (ident_to_string rcid)
      else assert false
  | DefFun (rfid, rf), DefFun (bfid, bf) ->
      if rfid = bfid then
        sprintf
          "%s\n\n%s"
          (gen_fun_corres false rfid rf.fn_params rf.fn_return bf.fn_return)
          (fun_rewrite_material (ident_to_string rfid))
      else assert false
  | DeclFun (rfid, rtparams, tr), DeclFun (bfid, btparams, tb) ->
      if rfid = bfid then
        let params = params_of_absfun rtparams in
        sprintf
          "%s\n\n%s"
          (gen_fun_corres true rfid params tr tb)
          (fun_rewrite_material (ident_to_string rfid))
      else assert false
  | _ -> assert false

let globdef_id (def : globdef) : string =
  match def with
  | DefConst (id, _, _) | DeclConst (id, _) | DefFun (id, _) | DeclFun (id, _, _)
    -> ident_to_string id

let globdef_corres_id (def : globdef) : string =
  match def with
  | DefConst (id, _, _) | DeclConst (id, _) ->
      sprintf "const_%s_corres" (ident_to_string id)
  | DefFun (id, _) | DeclFun (id, _, _) ->
      sprintf "fun_%s_corres" (ident_to_string id)

let rec print_defs_corres (out : out_channel) (rdefs : globdef list)
    (bdefs : globdef list) : unit =
  match (rdefs, bdefs) with
  | [], [] -> fprintf out "\n"
  | rd :: [], bd :: [] -> fprintf out "%s" (gen_def_corres rd bd)
  | rd :: rdefs', bd :: bdefs' ->
      fprintf out "%s\n" (gen_def_corres rd bd);
      print_defs_corres out rdefs' bdefs'
  | _ -> assert false

module HelperTactics = struct
  let create_databases (out : out_channel) (prog : program) : unit =
    fprintf
      out
      "Create HintDb corresRB_types.\n\
       Create HintDb corresRB_consts.\n\
       Create HintDb corresRB_pattern_matching.\n"

  let register_enums_constuctors_hints (out : out_channel)
      (enums : ident list Maps2.smaplist) : unit =
    let register_one_enum (ed_name : ident) (ed_elems : ident list) =
      print_list
        out
        ~delim:("", "\n")
        ~sep:"\n"
        (fun constr ->
          let cid = ident_to_string constr in
          sprintf
            "Hint Rewrite constr_%s_RtoB_corres : corresRB_consts.\n\
             Hint Rewrite constr_%s_BtoR_corres : corresRB_pattern_matching.\n\
             Hint Rewrite constr_%s_make_ok : corresRB_pattern_matching."
            cid
            cid
            cid)
        ed_elems
    in
    List.iter
      (fun (ed_name, ed_elems) ->
        register_one_enum ed_name ed_elems;
        fprintf out "\n")
      enums

  let register_enums_op_hints (out : out_channel)
      (enums : ident list Maps2.smaplist) : unit =
    print_list
      out
      ~sep:"\n"
      (fun (ed_name, _) ->
        let eid = ident_to_string ed_name in
        sprintf
          "Hint Rewrite cast_i32_to_%s_corres : corresRB_types.\n\
           Hint Rewrite cast_%s_to_i32_corres : corresRB_types.\n\
           Hint Rewrite enum_eq_%s_corres : corresRB_types.\n\
           Hint Unfold Benum.enum_neq : corresRB_types.\n\
           Hint Unfold %s_neq : corresRB_types.\n"
          eid
          eid
          eid
          eid)
      enums

  let rec register_records_hints (out : out_channel)
      (records : mtyp Maps2.smaplist Maps2.smaplist) : unit =
    match records with
    | [] -> ()
    | (rd_name, rd_fields) :: records' ->
        print_list
          out
          ~delim:("", "\n")
          ~sep:"\n\n"
          (fun (fname, _) ->
            let rid = ident_to_string rd_name in
            let fid = ident_to_string fname in
            sprintf
              "Hint Rewrite rconv_%s_RtoB_proj_%s_correct : corresRB_types.\n\
               Hint Rewrite rconv_%s_RtoB_update_%s_correct : corresRB_types."
              rid
              fid
              rid
              fid)
          rd_fields;
        register_records_hints out records'

  let register_types_hints (out : out_channel) (prog : program) : unit =
    let enums = get_enum_typedefs prog.prog_types in
    let records = get_record_typedefs prog.prog_types in
    register_enums_constuctors_hints out enums;
    register_enums_op_hints out enums;
    fprintf out "\n";
    register_records_hints out records

  let gen_fun_rewrite_class (fid : ident) (params : (ident * mtyp) list)
      (tr : mtyp) (tb : mtyp) : string =
    sprintf
      "Class RewriteRB_%s := {\n%scorresRB_%s:\n%s\n}."
      (ident_to_string fid)
      indent
      (ident_to_string fid)
      (fun_corres_statement indent2 fid params tr tb)

  let create_fun_rewrite_classes (out : out_channel) (rprog : program)
      (bprog : program) : unit =
    let print_def_rewrite_class (rd : globdef) (bd : globdef) (term : string) :
        unit =
      match (rd, bd) with
      | DefFun (rfid, rf), DefFun (bfid, bf) ->
          if rfid = bfid then
            fprintf
              out
              "%s%s"
              (gen_fun_rewrite_class
                 rfid
                 rf.fn_params
                 rf.fn_return
                 bf.fn_return)
              term
          else assert false
      | DeclFun (rfid, rtparams, tr), DeclFun (bfid, btparams, tb) ->
          if rfid = bfid then
            fprintf
              out
              "%s%s"
              (gen_fun_rewrite_class rfid (params_of_absfun rtparams) tr tb)
              term
          else assert false
      | _ -> ()
    in
    let rec create_aux (rdefs : globdef list) (bdefs : globdef list) : unit =
      match (rdefs, bdefs) with
      | [], [] -> ()
      | rd :: [], bd :: [] -> print_def_rewrite_class rd bd "\n"
      | rd :: rdefs', bd :: bdefs' ->
          print_def_rewrite_class rd bd "\n\n";
          create_aux rdefs' bdefs'
      | _, _ -> assert false
    in
    create_aux rprog.prog_defs bprog.prog_defs

  let ltac_fun_rewrite (fid : ident) (tparams : (ident * mtyp) list)
      (tret : mtyp) : string =
    let fid = ident_to_string fid in
    let tac =
      match tret with
      | MRes t ->
          let args_qmark =
            list_to_string
              ~sep:" "
              (fun (pid, _) ->
                sprintf "?%s" (String.uppercase_ascii (ident_to_string pid)))
              tparams
          in
          let args =
            list_to_string
              ~sep:" "
              (fun (pid, _) -> String.uppercase_ascii (ident_to_string pid))
              (* (fun _ -> "_") *)
              tparams
          in
          sprintf
            "%srewrite corresRB_%s\n\
             %s| %s_ShallowR.%s %s =>\n\
             %sdestruct (%s_ShallowR.%s %s); simpl; try reflexivity"
            indent3
            fid
            indent
            !coqlib
            fid
            args_qmark
            indent3
            !coqlib
            fid
            args
      | _ -> sprintf "%srewrite corresRB_%s; simpl" indent3 fid
    in
    sprintf
      "%s| %s_ShallowB.%s %s =>\n%s"
      indent
      !coqlib
      fid
      (list_to_string ~sep:" " (fun _ -> "_") tparams)
      tac

  let ltac_def_rewrite (def : globdef) : string =
    match def with
    | DefConst (cid, _, _) | DeclConst (cid, _) -> assert false
    | DefFun (fid, f) -> ltac_fun_rewrite fid f.fn_params f.fn_return
    | DeclFun (fid, tparams, tret) ->
        ltac_fun_rewrite fid (params_of_absfun tparams) tret

  let print_pattern_match_corres_tac (out : out_channel)
      (enums : ident list Maps2.smaplist) : unit =
    let gen_enum_simpl ((ed_name, ed_elems) : ident * ident list) : string =
      let eid = ident_to_string ed_name in
      sprintf
        "%s| %s_ShallowR.%s =>\n\
         %serewrite Benum.match_with_err_eq_match_with_err2 with\n\
         %s(E_eq_dec := %s_eq_dec)\n\
         %s(econv_to := econv_%s_BtoR)\n\
         %s(econv_from := econv_%s_RtoB);\n\
         %sintros; try (apply econv_%s_inv1 || apply econv_%s_inv2);\n\
         %scbn [Benum.match_with_err2]; rewrite econv_%s_inv1;\n\
         %sautorewrite with corresRB_pattern_matching; simpl;\n\
         %sautorewrite with corresRB_pattern_matching;\n\
         %sdestruct E; simpl"
        indent
        !coqlib
        eid
        indent3
        indent4
        eid
        indent4
        eid
        indent4
        eid
        indent3
        eid
        eid
        indent3
        eid
        indent3
        indent3
        indent3
    in
    if enums = []
    then 
      fprintf out "Ltac pattern_match_err_corres E := fail."
    else begin fprintf
        out
        "Ltac pattern_match_err_corres E :=\n%smatch type of E with\n"
        indent;
      print_list out ~delim:("", "\n") ~sep:"\n" gen_enum_simpl enums;
      fprintf out "%send.\n" indent
        end

  let print_helper_match_tac (out : out_channel) (prog : program) : unit =
    let funs =
      List.filter
        (fun (d : BarocqShallow.Monadic.globdef) ->
          match d with
          | DefFun _ | DeclFun _ -> true
          | _ -> false)
        prog.prog_defs
    in
    let cast_i32_to_enum_destruct (enums : ident list Maps2.smaplist) : string =
      list_to_string
        ~sep:"\n"
        (fun (ed_name, _) ->
          let eid = ident_to_string ed_name in
          sprintf
            "%s| cast_i32_to_%s ?X =>\n\
             %sdestruct (cast_i32_to_%s X); simpl; try reflexivity"
            indent
            eid
            indent3
            eid)
        enums
    in
    let enums = get_enum_typedefs prog.prog_types in
    fprintf
      out
      "Ltac corres_rb_match P :=\n\
       %smatch P with\n\
       %s| ret ?X => corres_rb_match X\n\
       %s| bind (Some _) _ => simpl\n\
       %s| bind ?F _ => corres_rb_match F\n\
       %s| let _ := _ in _ => simpl\n\
       %s| if ?C then _ else _ => destruct C; simpl; try reflexivity\n\
       %s| Intop.I32.div ?X ?Y => destruct (Intop.I32.div X Y); simpl; try \
       reflexivity\n\
       %s| Intop.U32.div ?X ?Y => destruct (Intop.U32.div X Y); simpl; try \
       reflexivity\n\
       %s| Intop.I64.div ?X ?Y => destruct (Intop.I64.div X Y); simpl; try \
       reflexivity\n\
       %s| Intop.U64.div ?X ?Y => destruct (Intop.U64.div X Y); simpl; try \
       reflexivity\n\
       %s| Intop.I32.mod ?X ?Y => destruct (Intop.I32.mod X Y); simpl; try \
       reflexivity\n\
       %s| Intop.U32.mod ?X ?Y => destruct (Intop.U32.mod X Y); simpl; try \
       reflexivity\n\
       %s| Intop.I64.mod ?X ?Y => destruct (Intop.I64.mod X Y); simpl; try \
       reflexivity\n\
       %s| Intop.U64.mod ?X ?Y => destruct (Intop.U64.mod X Y); simpl; try \
       reflexivity\n\
       %s\n\
       %s| Benum.enum_eq (_ ?E) _ => destruct E; try reflexivity\n\
       %s| Benum.match_with_err (_ ?E) _ => pattern_match_err_corres E\n\
       %s| Barray.get ?A ?I =>\n\
       %sdestruct (Barray.get A I); simpl; try reflexivity\n\
       %s| Barray.set ?A ?I ?V =>\n\
       %sdestruct (Barray.set A I V); simpl; try reflexivity\n"
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      (cast_i32_to_enum_destruct enums)
      indent
      indent
      indent
      indent3
      indent
      indent3;
    print_list out ~sep:"\n" ltac_def_rewrite funs;
    fprintf out "\n";
    fprintf out "%send.\n" indent

  let print_rewrite_prelude_tac (out : out_channel) : unit =
    fprintf
      out
      "Ltac rewrite_prelude :=\n\
       %sautounfold with corresRB_types;\n\
       %sautorewrite with corresRB_types; simpl;\n\
       %srepeat (rewrite Barray.get_map_same);\n\
       %srepeat (rewrite Barray.set_map_same).\n"
      indent
      indent
      indent
      indent

  let print_finish_tac (out : out_channel) : unit =
    fprintf
      out
      "Ltac finish :=\n\
       %smatch goal with\n\
       %s| |- context[if ?E then _ else _] =>\n\
       %sdestruct E; try reflexivity; finish\n\
       %s| _ => reflexivity\n\
       %send.\n"
      indent
      indent
      indent3
      indent
      indent

  let print_helper_rec_tac (out : out_channel) (prog : program) : unit =
    fprintf
      out
      "Ltac corres_rb_rec :=\n\
       %srewrite_prelude;\n\
       %smatch goal with\n\
       %s| [ |- bind (ret ?X) _ = _ ]    => rewrite bind_ret with (e:=X); corres_rb_rec\n\
       %s| [ |- _ = bind (ret ?X) _ ]    => rewrite bind_ret with (e:=X); corres_rb_rec\n\
       %s| [ |- (bind (bind ?E1 ?E2) ?E3) = _ ] => rewrite assoc_bind; corres_rb_rec\n\
       %s| [ |- _ = (bind (bind ?E1 ?E2) ?E3) ] => rewrite assoc_bind; corres_rb_rec\n\
       %s| [ |- bind ?X _ = bind ?X _] => apply bind_equal; intros;corres_rb_rec\n\
       %s| [ |- _ = match ?E with _ => _ end ] =>\n\
       %sdestruct E; try reflexivity; corres_rb_rec\n\
       %s| [ |- ret _ = Some _] => finish\n\
       %s| [ |- ?G = _ ] =>\n\
       %sreflexivity ||\n\
       %s(corres_rb_match G; corres_rb_rec)\n\
       %send.\n"
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      indent
      indent3
      indent
      indent
      indent3
      indent3
      indent

  let print_helper_tac (out : out_channel) : unit =
    fprintf
      out
      "Ltac corres_rb :=\n\
       %sautorewrite * with corresRB_consts;\n\
       %scorres_rb_rec.\n"
      indent
      indent;
    fprintf out "\n";
    fprintf out "Ltac corres_rb_timeout :=\n%stimeout 600 corres_rb.\n" indent

  let imports () : string =
    sprintf
      "From Coq Require Import String.\n\
       From compcert Require Import Integers.\n\
       From BarocqComp Require Import OptionMonad.\n\
       From %s Require Import %s_Types %s_ShallowR %s_ShallowB.\n\
       Open Scope option_monad_scope.\n"
      !coqlib
      !coqlib
      !coqlib
      !coqlib

  let print (out : out_channel) (rprog : program) (bprog : program) : unit =
    let enums = get_enum_typedefs rprog.prog_types in
    fprintf out "%s" (imports ());
    fprintf out "\n";
    create_databases out rprog;
    fprintf out "\n";
    register_types_hints out rprog;
    fprintf out "\n";
    create_fun_rewrite_classes out rprog bprog;
    fprintf out "\n";
    print_pattern_match_corres_tac out enums;
    fprintf out "\n";
    print_helper_match_tac out rprog;
    fprintf out "\n";
    print_rewrite_prelude_tac out;
    fprintf out "\n";
    print_finish_tac out;
    fprintf out "\n";
    print_helper_rec_tac out rprog;
    fprintf out "\n";
    print_helper_tac out
end

let imports () : string =
  sprintf
    "From Coq Require Import String.\n\
     From compcert Require Import Integers.\n\
     From BarocqComp Require Import OptionMonad.\n\
     From %s Require Import %s_Types %s_ShallowR %s_ShallowB \
     %s_CorresRB_Tactics.\n\n\
     Open Scope string_scope.\n"
    !coqlib
    !coqlib
    !coqlib
    !coqlib
    !coqlib

let print_opaque_defs (out : out_channel) (prog : program) : unit =
  fprintf
    out
    "Opaque Benum.enum.\n\
     Opaque Benum.match_with_err.\n\
     Opaque Brecord.record.\n\
     Opaque Brecord.project.\n\
     Opaque Brecord.upd.\n\
     Opaque Barray.get.\n\
     Opaque Barray.set.\n";
  let enums = get_enum_typedefs prog.prog_types in
  print_list
    out
    ~delim:("", "\n")
    ~sep:"\n"
    (fun (ed_name, _) ->
      let eid = ident_to_string ed_name in
      sprintf "Opaque econv_%s_RtoB.\nOpaque econv_%s_BtoR." eid eid)
    enums

let print_corres (out : out_channel) (rprog : program) (bprog : program) : unit
    =
  fprintf out "%s" (imports ());
  fprintf out "\n";
  print_opaque_defs out rprog;
  fprintf out "\n";
  print_defs_corres out rprog.prog_defs bprog.prog_defs
