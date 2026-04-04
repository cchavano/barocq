open Printf
open PrintUtils
open Syntax
open BarocqShallow.Monadic

let coqlib : string ref = ref ""

let shallowR_file : string ref = ref ""

let rec is_simpl_mtyp (ty : mtyp) : bool =
  match ty with
  | MBool | MInt32 _ | MInt64 _ | MEnum _ | MRecord _ | MAbs _ -> true
  | MRes ty' -> is_simpl_mtyp ty'
  | _ -> false

let ident_to_shallow (shver : BarocqShallowgen.shallow_version) (id : ident) :
    string =
  match shver with
  | BarocqShallowgen.ShallowR ->
      sprintf "%s.%s" !shallowR_file (ident_to_string id)
  | BarocqShallowgen.ShallowB -> ident_to_string id

let rec mtyp_to_rocq (shver : BarocqShallowgen.shallow_version) (ty : mtyp) :
    string =
  match ty with
  | MBool -> "bool"
  | MInt32 _ -> "int"
  | MInt64 _ -> "int64"
  | MArray ta -> sprintf "array %s" (opt_parens shver ta)
  | MEnum te -> ident_to_shallow shver te
  | MRecord tr -> ident_to_shallow shver tr
  | MAbs t -> ident_to_string t
  | MFun (tparams, tret) ->
      begin match tparams with
      | [] -> sprintf "unit -> %s" (opt_parens shver tret)
      | _ ->
          List.fold_right
            (fun t acc -> sprintf "%s -> %s" (opt_parens shver t) acc)
            tparams
            (opt_parens shver tret)
      end
  | MRes ty' -> sprintf "res %s" (opt_parens shver ty')

and opt_parens (shver : BarocqShallowgen.shallow_version) (ty : mtyp) : string =
  PrintUtils.opt_parens is_simpl_mtyp (mtyp_to_rocq shver) ty

let enum_def_to_rocq (ed_name : ident) (ed_elems : ident list) : string =
  let eid = ident_to_string ed_name in
  sprintf
    "Definition elems_of_%s : list ident := [\n\
     %s\n\
     ].\n\n\
     Notation %s := (enum elems_of_%s)."
    eid
    (list_to_string
       ~sep:";\n"
       (fun cid -> sprintf "%s%s" indent (Deepgen.ident_to_deep cid))
       ed_elems)
    eid
    eid

let field_typ_to_rocq ((fname, fty) : ident * mtyp) : string =
  sprintf
    "(%s, %s : Type)"
    (Deepgen.ident_to_deep fname)
    (mtyp_to_rocq BarocqShallowgen.ShallowB fty)

let record_def_to_rocq (rd_name : ident) (rd_fields : mtyp Maps2.smaplist) :
    string =
  let rid = ident_to_string rd_name in
  sprintf
    "Definition fields_of_%s : list (ident * Type) := [\n\
     %s\n\
     ].\n\n\
     Notation %s := (record fields_of_%s)."
    rid
    (list_to_string
       ~sep:";\n"
       (fun field -> sprintf "%s%s" indent (field_typ_to_rocq field))
       rd_fields)
    rid
    rid

let type_def_to_rocq ((tname, td) : ident * (mtyp * Types.layout) type_def) :
    string =
  match td with
  | TdEnum elems -> enum_def_to_rocq tname elems
  | TdRecord fields -> record_def_to_rocq tname (Maps2.MapList.map fst fields)

let print_btypes (out : out_channel) (prog : program) : unit =
  print_list out ~delim:("", "\n") ~sep:"\n\n" type_def_to_rocq prog.prog_types

let print_enum_constructors (out : out_channel)
    ((ed_name, ed_elems) : ident * ident list) : unit =
  let eid = ident_to_string ed_name in
  let rec aux (elems : ident list) : unit =
    match elems with
    | [] -> ()
    | i :: elems' ->
        fprintf
          out
          "\nDefinition %s : %s :=\n%sBenum.mk_enum elems_of_%s %s eq_refl.\n"
          (ident_to_string i)
          eid
          indent
          eid
          (Deepgen.ident_to_deep i);
        aux elems'
  in
  aux ed_elems

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
      then sprintf "Barray.map %s" r
      else sprintf "Barray.map (%s)" r
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
            "%s| %s.%s => %s (Constr %s)%s"
            indent
            !shallowR_file
            (ident_to_string i)
            constr
            (Deepgen.ident_to_deep i)
            parens
      | i :: elems' ->
          let constr' = sprintf "%s (inr" constr in
          let parens' = sprintf "%s)" parens in
          sprintf
            "%s| %s.%s => %s (inl (Constr %s))%s\n%s"
            indent
            !shallowR_file
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
          "%s| %s.%s => inl (Constr %s)\n%s"
          indent
          !shallowR_file
          (ident_to_string i)
          (Deepgen.ident_to_deep i)
          (aux elems' "inr" "")

  let gen_econv_RtoB ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
    sprintf
      "Definition econv_%s_RtoB (e: %s.%s) : %s :=\n%smatch e with\n%s\n%send."
      eid
      !shallowR_file
      eid
      eid
      indent
      (econv_elems_RtoB ed_elems)
      indent

  let econv_elems_BtoR (elems : ident list) : string =
    let rec aux (elems : ident list) (constr : string) (parens : string) :
        string =
      match elems with
      | [] -> assert false
      | i :: [] ->
          sprintf
            "%s| %s _%s => %s.%s"
            indent
            constr
            parens
            !shallowR_file
            (ident_to_string i)
      | i :: elems' ->
          let constr' = sprintf "%s (inr" constr in
          let parens' = sprintf "%s)" parens in
          sprintf
            "%s| %s (inl _)%s => %s.%s\n%s"
            indent
            constr
            parens
            !shallowR_file
            (ident_to_string i)
            (aux elems' constr' parens')
    in
    match elems with
    | [] -> assert false
    | i :: elems' ->
        sprintf
          "%s| inl _ => %s.%s\n%s"
          indent
          !shallowR_file
          (ident_to_string i)
          (aux elems' "inr" "")

  let gen_econv_BtoR ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
    sprintf
      "Definition econv_%s_BtoR (e: %s) : %s.%s :=\n%smatch e with\n%s\n%send."
      eid
      eid
      !shallowR_file
      eid
      indent
      (econv_elems_BtoR ed_elems)
      indent

  let gen_econv_inv1_thm ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
    sprintf
      "Theorem econv_%s_inv1 :\n\
       %sforall (e: %s.%s),\n\
       %seconv_%s_BtoR (econv_%s_RtoB e) = e.\n\
       Proof.\n\
       %sintro. destruct e; reflexivity.\n\
       Qed."
      eid
      indent
      !shallowR_file
      eid
      indent
      eid
      eid
      indent

  let gen_econv_inv2_thm ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
    sprintf
      "Theorem econv_%s_inv2 :\n\
       %sforall (e: %s),\n\
       %seconv_%s_RtoB (econv_%s_BtoR e) = e.\n\
       Proof.\n\
       %sapply Benum.forallb_enum_equal.\n\
       %sreflexivity.\n\
       Qed."
      eid
      indent
      eid
      indent
      eid
      eid
      indent
      indent

  let gen_enum_of_Z_corres ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
    let proof : string =
      sprintf
        "%sintro. unfold Benum.of_Z. unfold %s_of_Z.\n\
         %sapply castZ_eqb_sound. reflexivity."
        indent
        eid
        indent
    in
    sprintf
      "Lemma %s_of_Z_corres :\n\
       %sforall (z: Z),\n\
       %sBenum.of_Z elems_of_%s z =\n\
       %slet* e := %s.%s_of_Z z in\n\
       %sSome (econv_%s_RtoB e).\n\
       Proof.\n\
       %s\n\
       Qed."
      eid
      indent
      indent
      eid
      indent
      !shallowR_file
      eid
      indent
      eid
      proof

  let gen_enum_to_Z_corres ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
    sprintf
      "Lemma %s_to_Z_corres :\n\
       %sforall (e: %s.%s),\n\
       %sBenum.to_Z (econv_%s_RtoB e) =\n\
       %s%s.%s_to_Z e.\n\
       Proof.\n\
       %sintro; destruct e; reflexivity.\n\
       Qed."
      eid
      indent
      !shallowR_file
      eid
      indent
      eid
      indent
      !shallowR_file
      eid
      indent

  let gen_eq_corres ((ed_name, ed_elems) : ident * ident list) : string =
    let eid = ident_to_string ed_name in
    sprintf
      "Lemma enum_eq_%s_corres :\n\
       %sforall (e1 e2: %s.%s),\n\
       %sBenum.enum_eq (econv_%s_RtoB e1) (econv_%s_RtoB e2) =\n\
       %s%s_eq e1 e2.\n\
       Proof.\n\
       %sintros. eapply bij_eq_iff. split.\n\
       %s- apply econv_%s_inv2.\n\
       %s- apply econv_%s_inv1.\n\
       Qed."
      eid
      indent
      !shallowR_file
      eid
      indent
      eid
      eid
      indent
      eid
      indent
      indent
      eid
      indent
      eid

  let print_constructors_make (out : out_channel)
      (enums : ident list Maps2.smaplist) : unit =
    let enum_def_constructors_make (ed_name : ident) (ed_elems : ident list) :
        unit =
      print_list
        out
        ~delim:("", "\n")
        ~sep:"\n\n"
        (fun constr ->
          let cid = ident_to_string constr in
          sprintf
            "Lemma constr_%s_make_ok :\n\
             %sBenum.make_enum elems_of_%s %s = Some %s.\n\
             Proof.\n\
             %sreflexivity.\n\
             Qed."
            cid
            indent
            (ident_to_string ed_name)
            (Deepgen.ident_to_deep constr)
            cid
            indent)
        ed_elems
    in
    List.iter
      (fun (ed_name, ed_elems) ->
        enum_def_constructors_make ed_name ed_elems;
        fprintf out "\n")
      enums

  let print_constructors_conv_corres (out : out_channel)
      (enums : ident list Maps2.smaplist) : unit =
    let enum_def_constructors_conv_corres (ed_name : ident)
        (ed_elems : ident list) : unit =
      print_list
        out
        ~delim:("", "\n\n")
        ~sep:"\n\n"
        (fun constr ->
          let cid = ident_to_string constr in
          sprintf
            "Lemma constr_%s_RtoB_corres : \n\
             %s%s = econv_%s_RtoB %s.%s.\n\
             Proof.\n\
             %sreflexivity.\n\
             Qed."
            cid
            indent
            cid
            (ident_to_string ed_name)
            !shallowR_file
            cid
            indent)
        ed_elems;
      print_list
        out
        ~delim:("", "\n")
        ~sep:"\n\n"
        (fun constr ->
          let cid = ident_to_string constr in
          sprintf
            "Lemma constr_%s_BtoR_corres : \n\
             %seconv_%s_BtoR %s = %s.%s.\n\
             Proof.\n\
             %sreflexivity.\n\
             Qed."
            cid
            indent
            (ident_to_string ed_name)
            cid
            !shallowR_file
            cid
            indent)
        ed_elems
    in
    List.iter
      (fun (ed_name, ed_elems) ->
        enum_def_constructors_conv_corres ed_name ed_elems;
        fprintf out "\n")
      enums

  let print_conversions (out : out_channel) (enums : ident list Maps2.smaplist)
      : unit =
    fprintf out "(** * Barocq <-> Rocq enum conversions *)\n\n";
    print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_econv_RtoB enums;
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_econv_BtoR enums

  let print_inversibility (out : out_channel)
      (enums : ident list Maps2.smaplist) : unit =
    print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_econv_inv1_thm enums;
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_econv_inv2_thm enums

  let print_i32_casts_corres (out : out_channel)
      (enums : ident list Maps2.smaplist) : unit =
    print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_enum_of_Z_corres enums;
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_enum_to_Z_corres enums

  let print_eq_corres (out : out_channel) (enums : ident list Maps2.smaplist) :
      unit =
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_eq_corres enums
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

  let rconv_RtoB (rd_name : string) (rd_fields : mtyp Maps2.smaplist)
      (arg : string) : string =
    List.fold_right
      (fun (fname, fty) acc ->
        sprintf "(%s, %s)" (rconv_field_RtoB rd_name fname fty arg) acc)
      rd_fields
      "tt"

  let gen_rconv_RtoB
      ((rd_name, rd_fields) : ident * (mtyp * Types.layout) Maps2.smaplist) :
      string =
    let rid = ident_to_string rd_name in
    let fields = Maps2.MapList.map fst rd_fields in
    sprintf
      "Definition rconv_%s_RtoB (r: %s.%s) : %s :=\n%s%s."
      rid
      !shallowR_file
      rid
      rid
      indent
      (rconv_RtoB rid fields "r")

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
            indent3
            fid
            v_conv
            (rconv_letmon_BtoR fields')

  let rconv_BtoR (rd_name : string) (rd_fields : mtyp Maps2.smaplist) : string =
    let match_case =
      List.fold_right
        (fun (fname, fty) acc ->
          sprintf "(Field _ %s, %s)" (ident_to_string fname) acc)
        rd_fields
        "tt"
    in
    let mk_record =
      sprintf
        "mk_%s %s"
        rd_name
        (list_to_string
           ~sep:" "
           (fun (fname, fty) ->
             conv_value_opt_parens BtoR fty (ident_to_string fname))
           rd_fields)
    in
    sprintf
      "%smatch r with\n%s| %s =>\n%s%s\n%send"
      indent
      indent
      match_case
      indent3
      mk_record
      indent

  let gen_rconv_BtoR
      ((rd_name, rd_fields) : ident * (mtyp * Types.layout) Maps2.smaplist) :
      string =
    let rid = ident_to_string rd_name in
    let fields = Maps2.MapList.map fst rd_fields in
    sprintf
      "Definition rconv_%s_BtoR (r: %s) : %s.%s :=\n%s."
      rid
      rid
      !shallowR_file
      rid
      (rconv_BtoR rid fields)

  (* Main printing function *)

  let print_conversions (out : out_channel)
      (records : (mtyp * Types.layout) Maps2.smaplist Maps2.smaplist) : unit =
    fprintf out "(** * Barocq <-> Rocq record conversions **)\n\n";
    print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_rconv_RtoB records;
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_rconv_BtoR records

  (* Correctness theorems *)

  (* let gen_rconv_RtoB_correctness_thm (rd_name: ident) (rd_fields: mtyp smaplist) : string =
    let rid = ident_to_string rd_name in
    let forall = sprintf "forall (r: %s.%s) (b: %s)," !shallowR_file rid rid in
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
            "%s@Brecord.project fields_of_%s b %s eq_refl = %s"
            indent
            rid
            (Deepgen.ident_to_deep fname)
            rproj)
        rd_fields
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
      proof *)

  let print_rconv_RtoB_proj_correctness_thm (out : out_channel)
      ((rd_name, rd_fields) : ident * (mtyp * Types.layout) Maps2.smaplist) :
      unit =
    let rid = ident_to_string rd_name in
    let field_proj_thm ((fid, fty) : ident * mtyp) : string =
      let rproj =
        conv_value
          RtoB
          fty
          (sprintf
             "r.(%s_%s)"
             (String.lowercase_ascii rid)
             (ident_to_string fid))
      in
      let proj_correct =
        sprintf
          "%s@Brecord.project fields_of_%s (rconv_%s_RtoB r) %s eq_refl = %s"
          indent
          rid
          rid
          (Deepgen.ident_to_deep fid)
          rproj
      in
      sprintf
        "Lemma rconv_%s_RtoB_proj_%s_correct :\n\
         %sforall (r: %s.%s),\n\
         %s.\n\
         Proof.\n\
         %sreflexivity.\n\
         Qed."
        rid
        (ident_to_string fid)
        indent
        !shallowR_file
        rid
        proj_correct
        indent
    in
    let fields = Maps2.MapList.map fst rd_fields in
    print_list out ~delim:("", "\n\n") ~sep:"\n\n" field_proj_thm fields

  let print_rconv_RtoB_update_correctness_thm (out : out_channel)
      ((rd_name, rd_fields) : ident * (mtyp * Types.layout) Maps2.smaplist) :
      unit =
    let rid = ident_to_string rd_name in
    let field_update_thm ((fid, fty) : ident * mtyp) =
      let update_correct =
        sprintf
          "%s@Brecord.upd fields_of_%s (rconv_%s_RtoB r) %s (%s) %s eq_refl = \
           rconv_%s_RtoB (r <| %s_%s := v |>)"
          indent
          rid
          rid
          (Deepgen.ident_to_deep fid)
          (mtyp_to_rocq BarocqShallowgen.ShallowB fty)
          (conv_value_opt_parens RtoB fty "v")
          rid
          (String.lowercase_ascii rid)
          (ident_to_string fid)
      in
      sprintf
        "Lemma rconv_%s_RtoB_update_%s_correct : \n\
         %sforall (r: %s.%s) (v: %s),\n\
         %s.\n\
         Proof.\n\
         %sreflexivity.\n\
         Qed."
        rid
        (ident_to_string fid)
        indent
        !shallowR_file
        rid
        (mtyp_to_rocq BarocqShallowgen.ShallowR fty)
        update_correct
        indent
    in
    let fields = Maps2.MapList.map fst rd_fields in
    print_list out ~delim:("", "\n\n") ~sep:"\n\n" field_update_thm fields

  let gen_rconv_BtoR_correctness_thm
      ((rd_name, rd_fields) : ident * (mtyp * Types.layout) Maps2.smaplist) :
      string =
    let rid = ident_to_string rd_name in
    let forall = sprintf "forall (b: %s) (r: %s.%s)," rid !shallowR_file rid in
    let conv_call = sprintf "rconv_%s_BtoR b = r" rid in
    let field_conv (fname : ident) (fty : mtyp) : string =
      let fid = ident_to_string fname in
      let proj =
        sprintf
          "@Brecord.project fields_of_%s b %s eq_refl"
          rid
          (Deepgen.ident_to_deep fname)
      in
      let proj_conv =
        let proj_paren = sprintf "(%s)" proj in
        let v = conv_value BtoR fty proj_paren in
        if v = proj_paren then proj else v
      in
      sprintf
        "%s%s = r.(%s_%s)"
        indent
        proj_conv
        (String.lowercase_ascii rid)
        fid
    in
    let fields_conv =
      list_to_string
        ~sep:" /\\\n"
        (fun (fname, fty) -> field_conv fname fty)
        (Maps2.MapList.map fst rd_fields)
    in
    let proof =
      sprintf
        "Proof.\n\
         %sBrecord.apply_decomp_field.\n\
         %scompute. intros. subst. repeat esplit.\n\
         Qed."
        indent
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

  let rec rconv_field_proof_inv (inv_kind : string) (ty : mtyp) : string =
    match ty with
    | MArray ta ->
        let pr = rconv_field_proof_inv inv_kind ta in
        if pr <> "" then
          sprintf
            "apply array_map_conv_inv; %s"
            (rconv_field_proof_inv inv_kind ta)
        else ""
    | MEnum eid ->
        sprintf "apply econv_%s_inv%s." (ident_to_string eid) inv_kind
    | MRecord rid ->
        sprintf "apply rconv_%s_inv%s." (ident_to_string rid) inv_kind
    | _ -> ""

  let gen_rconv_inv1_thm
      ((rd_name, rd_fields) : ident * (mtyp * Types.layout) Maps2.smaplist) :
      string =
    let rid = ident_to_string rd_name in
    let fields = Maps2.MapList.map fst rd_fields in
    let proof =
      sprintf
        "%sintro. destruct r; simpl. f_equal.\n%s"
        indent
        (list_to_string
           (fun s -> if s <> "" then sprintf "%s- %s\n" indent s else s)
           (List.map (fun (_, fty) -> rconv_field_proof_inv "1" fty) fields))
    in
    sprintf
      "Theorem rconv_%s_inv1 :\n\
       %sforall (r: %s.%s),\n\
       %srconv_%s_BtoR (rconv_%s_RtoB r) = r.\n\
       Proof.\n\
       %sQed."
      rid
      indent
      !shallowR_file
      rid
      indent
      rid
      rid
      proof

  let gen_rconv_inv2_thm
      ((rd_name, rd_fields) : ident * (mtyp * Types.layout) Maps2.smaplist) :
      string =
    let rec field_need_conv (fty : mtyp) : bool =
      match fty with
      | MArray ta -> field_need_conv ta
      | MEnum _ | MRecord _ -> true
      | _ -> false
    in
    let rid = ident_to_string rd_name in
    let fields = Maps2.MapList.map fst rd_fields in
    let proof =
      let refl_of_f_equal =
        if List.exists (fun (_, fty) -> field_need_conv fty) fields then
          "simpl; repeat apply Brecord.field_eq;auto"
        else "reflexivity"
      in
      sprintf
        "%sBrecord.apply_decomp_field. unfold rconv_%s_RtoB.\n%s%s.\n%s"
        indent
        rid
        indent
        refl_of_f_equal
        (list_to_string
           (fun s -> if s <> "" then sprintf "%s- %s\n" indent s else s)
           (List.map (fun (_, fty) -> rconv_field_proof_inv "2" fty) fields))
    in
    sprintf
      "Theorem rconv_%s_inv2 :\n\
       %sforall (r: %s),\n\
       %srconv_%s_RtoB (rconv_%s_BtoR r) = r.\n\
       Proof.\n\
       %sQed."
      rid
      indent
      rid
      indent
      rid
      rid
      proof

  let print_correctness_lemmas (out : out_channel)
      (records : (mtyp * Types.layout) Maps2.smaplist Maps2.smaplist) : unit =
    List.iter (print_rconv_RtoB_proj_correctness_thm out) records;
    List.iter (print_rconv_RtoB_update_correctness_thm out) records;
    print_list
      out
      ~delim:("", "\n")
      ~sep:"\n\n"
      gen_rconv_BtoR_correctness_thm
      records

  let print_array_conv_inversibility (out : out_channel) : unit =
    fprintf
      out
      "Theorem array_map_conv_inv :\n\
       %sforall (A B: Type) (f: A -> B) (g: B -> A) (Hinv: forall x, g (f x) = \
       x),\n\
       %sforall (a: array A), Barray.map g (Barray.map f a) = a.\n\
       Proof.\n\
       %sinduction a as [|a0 a']; intros.\n\
       %s- reflexivity.\n\
       %s- simpl. rewrite (Hinv a0). f_equal. apply IHa'.\n\
       Qed.\n"
      indent
      indent
      indent
      indent
      indent

  let print_inversibility (out : out_channel)
      (records : (mtyp * Types.layout) Maps2.smaplist Maps2.smaplist) : unit =
    print_array_conv_inversibility out;
    fprintf out "\n";
    print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_rconv_inv1_thm records;
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_rconv_inv2_thm records
end

let imports () : string =
  sprintf
    "From Stdlib Require Import List String BinIntDef.\n\
     From compcert Require Import Integers.\n\
     From RecordUpdate Require Import RecordUpdate.\n\
     From BarocqComp Require Import Ident Option Barray Benum Brecord Utils.\n\
     From %s Require Import %s.\n\
     Import ListNotations.\n\n\
     Open Scope Z_scope.\n\
     Open Scope string_scope.\n\
     Local Open Scope option_monad_scope.\n"
    !coqlib
    !shallowR_file

let print (out : out_channel) (prog : program) : unit =
  shallowR_file := sprintf "%s_ShallowR" !coqlib;
  fprintf out "%s" (imports ());
  let types = prog.prog_types in
  let tabs = prog.prog_tabs in
  if tabs <> [] then begin
    fprintf out "\n";
    fprintf out "(** * Abstract types *)\n\n";
    print_list
      out
      ~sep:"\n\n"
      (fun (tid, _) ->
        sprintf
          "Definition %s : Type := %s.%s.\n"
          (ident_to_string tid)
          !shallowR_file
          (ident_to_string tid))
      tabs
  end;
  fprintf out "\n";
  fprintf out "(** * Type definitions *)\n\n";
  print_btypes out prog;
  let enums = Syntax.get_enum_typedefs types in
  let records = Syntax.get_record_typedefs types in
  if enums <> [] then begin
    fprintf out "\n";
    fprintf out "(** * Enum constructors *)\n";
    List.iter (print_enum_constructors out) enums;
    fprintf out "\n";
    EnumConv.print_constructors_make out enums;
    fprintf out "\n";
    EnumConv.print_conversions out enums;
    fprintf out "\n";
    EnumConv.print_constructors_conv_corres out enums;
    fprintf out "\n";
    EnumConv.print_inversibility out enums;
    fprintf out "\n";
    EnumConv.print_i32_casts_corres out enums;
    fprintf out "\n";
    EnumConv.print_eq_corres out enums
  end;
  if records <> [] then begin
    fprintf out "\n";
    RecordConv.print_conversions out records;
    fprintf out "\n";
    RecordConv.print_correctness_lemmas out records;
    fprintf out "\n";
    RecordConv.print_inversibility out records
  end
