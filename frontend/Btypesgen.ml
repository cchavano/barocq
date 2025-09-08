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

let rec mtyp_to_rocq (ty : mtyp) : string =
  match ty with
  | MBool -> "bool"
  | MInt32 _ -> "int"
  | MInt64 _ -> "int64"
  | MArray ta -> sprintf "array %s" (opt_parens ta)
  | MEnum te -> ident_to_string te
  | MRecord tr -> ident_to_string tr
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
  PrintUtils.opt_parens is_simpl_mtyp mtyp_to_rocq ty

let enum_def_to_rocq (ed : enum_def) : string =
  let eid = ident_to_string ed.ed_name in
  sprintf
    "Definition elems_of_%s : list ident := [\n\
     %s\n\
     ].\n\n\
     Notation %s := (enum elems_of_%s)."
    eid
    (list_to_string
       ~sep:";\n"
       (fun cid -> sprintf "%s%s" indent (Deepgen.ident_to_deep cid))
       ed.ed_elems)
    eid
    eid

let field_typ_to_rocq ((fname, fty) : ident * mtyp) : string =
  sprintf "(%s, %s : Type)" (Deepgen.ident_to_deep fname) (mtyp_to_rocq fty)

let record_def_to_rocq (rd : record_def) : string =
  let rid = ident_to_string rd.rd_name in
  sprintf
    "Definition fields_of_%s : list (ident * Type) := [\n\
     %s\n\
     ].\n\n\
     Notation %s := (record fields_of_%s)."
    rid
    (list_to_string
       ~sep:";\n"
       (fun field -> sprintf "%s%s" indent (field_typ_to_rocq field))
       rd.rd_fields)
    rid
    rid

let type_def_to_rocq (td : type_def) : string =
  match td with
  | TdEnum ed -> enum_def_to_rocq ed
  | TdRecord rd -> record_def_to_rocq rd
  | TdAbstract _ -> ""

let print_btypes (out : out_channel) (prog : program) : unit =
  let types =
    List.filter
      (fun (td : BarocqShallow.Monadic.type_def) ->
        match td with
        | TdAbstract _ -> false
        | _ -> true)
      prog.prog_types
  in
  print_list out ~delim:("", "\n") ~sep:"\n\n" type_def_to_rocq types

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
      "Definition econv_%s_RtoB (e: %s.%s) : %s :=\n%smatch e with\n%s\n%send."
      eid
      !shallowR_file
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
      "Definition econv_%s_BtoR (e: %s) : %s.%s :=\n%smatch e with\n%s\n%send."
      eid
      eid
      !shallowR_file
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
      !shallowR_file
      eid
      indent
      eid
      eid
      indent

  let gen_econv_inv2_thm (ed : enum_def) : string =
    let eid = ident_to_string ed.ed_name in
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

  let print_conversions (out : out_channel) (enums : enum_def list) : unit =
    if enums <> [] then begin
      fprintf out "(** * Barocq <-> Rocq enum conversions *)\n\n";
      print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_econv_RtoB enums;
      print_list out ~delim:("", "\n") ~sep:"\n\n" gen_econv_BtoR enums
    end

  let print_inversibility (out : out_channel) (enums : enum_def list) : unit =
    if enums <> [] then begin
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
      "Definition rconv_%s_RtoB (r: %s.%s) : %s :=\n%s%s."
      rid
      !shallowR_file
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
      "Definition rconv_%s_BtoR (r: %s) : %s.%s :=\n%s."
      rid
      rid
      !shallowR_file
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
            "%s@Brecord.proj fields_of_%s b %s = OK %s"
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
    let forall = sprintf "forall (b: %s) (r: %s.%s)," rid !shallowR_file rid in
    let conv_call = sprintf "rconv_%s_BtoR b = r" rid in
    let field_conv (fname : ident) (fty : mtyp) : string =
      let fid = ident_to_string fname in
      let rval = conv_value BtoR fty fid in
      if rval = fid then
        sprintf
          "%s@Brecord.proj fields_of_%s b %s = OK r.(%s_%s)"
          indent
          rid
          (Deepgen.ident_to_deep fname)
          (String.lowercase_ascii rid)
          fid
      else
        sprintf
          "%s(exists %s, @Brecord.proj fields_of_%s b %s = OK %s /\\ %s = \
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
    let proof =
      sprintf
        "Proof.\n\
         %sBrecord.apply_decomp_field.\n\
         %sunfold rconv_Types_proc_t_BtoR.\n\
         %sintros. compute. subst. repeat esplit.\n\
         Qed."
        indent
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
            "apply transl_array_conv_inv; %s"
            (rconv_field_proof_inv inv_kind ta)
        else ""
    | MEnum eid ->
        sprintf "apply econv_%s_inv%s." (ident_to_string eid) inv_kind
    | MRecord rid ->
        sprintf "apply rconv_%s_inv%s." (ident_to_string rid) inv_kind
    | _ -> ""

  let gen_rconv_inv1_thm (rd : record_def) : string =
    let rid = ident_to_string rd.rd_name in
    let proof =
      sprintf
        "%sintro. destruct r; simpl. f_equal.\n%s"
        indent
        (list_to_string
           (fun s -> if s <> "" then sprintf "%s- %s\n" indent s else s)
           (List.map
              (fun (_, fty) -> rconv_field_proof_inv "1" fty)
              rd.rd_fields))
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

  let gen_rconv_inv2_thm (rd : record_def) : string =
    let rec field_need_conv (fty : mtyp) : bool =
      match fty with
      | MArray ta -> field_need_conv ta
      | MEnum _ | MRecord _ -> true
      | _ -> false
    in
    let rid = ident_to_string rd.rd_name in
    let proof =
      let refl_of_f_equal =
        if List.exists (fun (_, fty) -> field_need_conv fty) rd.rd_fields then
          "simpl; repeat f_equal"
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
           (List.map
              (fun (_, fty) -> rconv_field_proof_inv "2" fty)
              rd.rd_fields))
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

  let print_array_conv_inversibility (out : out_channel) : unit =
    fprintf
      out
      "Theorem transl_array_conv_inv :\n\
       %sforall (A B: Type) (f: A -> B) (g: B -> A) (Hinv: forall x, g (f x) = \
       x),\n\
       %sforall (a: array A), transl_array g (transl_array f a) = a.\n\
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

  let print_inversibility (out : out_channel) (records : record_def list) : unit
      =
    print_array_conv_inversibility out;
    fprintf out "\n";
    print_list out ~delim:("", "\n\n") ~sep:"\n\n" gen_rconv_inv1_thm records;
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_rconv_inv2_thm records
end

let gen_i32_enum_cast_corres (ed : enum_def) : string =
  let eid = ident_to_string ed.ed_name in
  let nb_elems = List.length ed.ed_elems in
  let proof : string =
    sprintf
      "%sintro. unfold Benum.of_i32. unfold cast_i32_to_%s.\n\
       %sassert (Hlength: List.length elems_of_%s = %d%%nat). reflexivity. \
       rewrite Hlength.\n\
       %sdestruct (Int.cmp Clt i Int.zero). reflexivity.\n\
       %sdestruct (Nat.leb %d%%nat (Intop.I32.to_nat i)). reflexivity.\n\
       %sapply cast_eqb_sound. reflexivity."
      indent
      eid
      indent
      eid
      nb_elems
      indent
      indent
      nb_elems
      indent
  in
  sprintf
    "Lemma cast_i32_to_%s_corres :\n\
     %sforall (i: int),\n\
     %sBenum.of_i32 %s_Types.elems_of_%s i =\n\
     %slet* e := %s_ShallowR.cast_i32_to_%s i in\n\
     %sOK (econv_%s_RtoB e).\n\
     Proof.\n\
     %s\n\
     Qed."
    eid
    indent
    indent
    !coqlib
    eid
    indent
    !coqlib
    eid
    indent
    eid
    proof

let imports () : string =
  sprintf
    "From Coq Require Import List String BinIntDef.\n\
     From compcert Require Import Integers.\n\
     From BarocqComp Require Import Ident Error Barray Benum Brecord.\n\
     From %s Require Import %s_ShallowR.\n\
     Import ListNotations.\n\n\
     Open Scope Z_scope.\n\
     Open Scope string_scope.\n"
    !coqlib
    !coqlib

let print (out : out_channel) (prog : program) : unit =
  shallowR_file := sprintf "%s_ShallowR" !coqlib;
  fprintf out "%s" (imports ());
  let types = prog.prog_types in
  let abstypes = get_abstract_typedefs types in
  if abstypes <> [] then begin
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
      abstypes
  end;
  fprintf out "\n";
  fprintf out "(** * Type definitions *)\n\n";
  print_btypes out prog;
  let enums = get_enum_typedefs types in
  let records = get_record_typedefs types in
  if enums <> [] then begin
    fprintf out "\n";
    EnumConv.print_conversions out enums;
    fprintf out "\n";
    EnumConv.print_inversibility out enums;
    fprintf out "\n";
    fprintf
      out
      "(** * Correspondence between the i32 to enum cast operations *)\n\n";
    print_list out ~delim:("", "\n") ~sep:"\n\n" gen_i32_enum_cast_corres enums
  end;
  if records <> [] then begin
    fprintf out "\n";
    RecordConv.print_conversions out records;
    fprintf out "\n";
    RecordConv.print_correctness_lemmas out records;
    fprintf out "\n";
    RecordConv.print_inversibility out records
  end
