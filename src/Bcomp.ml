open Lexing
open Printf

exception CompilerError of string

let source = ref ""

let c_output = ref ""

let opt_interp = ref false

let opt_typecheck = ref false

let opt_print_tokens = ref false

let opt_print_bbnf = ref false

let opt_print_imp1 = ref false

let opt_gen_shallow = ref false

let opt_gen_deep = ref false

let opt_gen_corres = ref false

let flag_simpl_bbnf = ref false

let flag_bbnf_v2 = ref false

let usage_msg = "Usage: barocq [options] <file> \noptions:"

let options =
  [
    ("-interp", Arg.Set opt_interp, "\t\tInterpret the given file");
    ( "-typecheck",
      Arg.Set opt_typecheck,
      "\t\tTypecheck the input program (do not compile)" );
    ("-o", Arg.Set_string c_output, "<file>\t\tGenerate C output in <file>");
    ( "-print-tokens",
      Arg.Set opt_print_tokens,
      "\tPrint parsed tokens (stop after lexing)" );
    ("-print-bbnf", Arg.Set opt_print_bbnf, "\t\tPretty-print B-normal form IR");
    ("-print-imp1", Arg.Set opt_print_imp1, "\t\tPretty-print Imp1 IR");
    ( "-gen-shallow",
      Arg.Set opt_gen_shallow,
      "\t\tGenerate the Rocq shallow-embedding" );
    ("-gen-deep", Arg.Set opt_gen_deep, "\t\tGenerate the Rocq deep-embedding");
    ( "-gen-proofs",
      Arg.Set opt_gen_corres,
      "\t\tGenerate the correspondance proofs between the shallow and the \
       deep-embedding" );
    ( "-fsimplify-bbnf",
      Arg.Set flag_simpl_bbnf,
      "\tSimplify the BNF IR (does nothing with -fbbnf-v2)" );
    ( "-fbbnf-v2",
      Arg.Set flag_bbnf_v2,
      "\t\tUses a one-pass BNF normalization with simplification" );
  ]

let set_source (file : string) : unit = source := file

let get_raw_filename (file : string) : string =
  Filename.remove_extension (Filename.basename file)

let get_full_filename (file : string) (suffix : string) : string =
  let rawname = get_raw_filename file in
  let dirname = Filename.dirname file in
  Printf.sprintf "%s/%s%s" dirname rawname suffix

let set_c_filename (file : string) : unit =
  if !c_output = "" then c_output := get_full_filename file ".c" else ()

let rec record_idents (ids : string list) : unit =
  match ids with
  | [] -> ()
  | h :: t ->
      let _ = Camlcoq.intern_string h in
      record_idents t

let () =
  Arg.parse options set_source usage_msg;

  if !source = "" then begin
    eprintf "Error: no source file provided\n";
    exit 1
  end;

  try
    let input = open_in !source in
    let lexbuf = from_channel input in

    lexbuf.lex_curr_p <-
      { pos_fname = !source; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 };

    if !opt_print_tokens then begin
      PrintTokens.print lexbuf;
      exit 0
    end;

    let xprog = Bparser.xprogram Blexer.read_token lexbuf in
    let prog = Barocq.xprog_to_prog xprog in

    begin
      match Barocq.Typing.typecheck_program prog with
      | Errors.OK _ ->
          if !opt_typecheck then begin
            printf "Typechecking succeeds\n";
            exit 0
          end
      | Errors.Error msg ->
          failwith
            (sprintf "Typechecking error: %s\n" (C2C.string_of_errmsg msg))
    end;

    if !opt_print_bbnf then begin
      let norm =
        if !flag_bbnf_v2 then BarocqBNFgen2.normalize_program
        else BarocqBNFgen.normalize_program !flag_simpl_bbnf
      in
      let bbnf = norm prog in
      begin
        match bbnf with
        | Errors.OK prog -> PrintBarocqBNF.print_program stdout prog
        | Errors.Error msg -> raise @@ CompilerError (C2C.string_of_errmsg msg)
      end;
      exit 0
    end;

    if !opt_print_imp1 then begin
      let comp =
        if !flag_bbnf_v2 then Compiler.compile2_to_imp1
        else Compiler.compile_to_imp1 !flag_simpl_bbnf
      in
      let imp1 = comp prog in
      begin
        match imp1 with
        | Errors.OK prog -> PrintImp1.print_program stdout prog
        | Errors.Error msg -> raise @@ CompilerError (C2C.string_of_errmsg msg)
      end;
      exit 0
    end;

    if !opt_interp then begin
      let _ = Interpreter.interpret xprog in
      exit 0
    end;

    if !opt_gen_corres then begin
      opt_gen_shallow := true;
      opt_gen_deep := true;
      let rawname = get_raw_filename !source in
      let coqlib =
        let bytes = String.to_bytes rawname in
        Bytes.fill bytes 0 1 (Char.uppercase_ascii (String.get rawname 0));
        Bytes.to_string bytes
      in
      Proofsgen.coqlib := coqlib;
      Proofsgen.shallowfile := rawname ^ "_Shallow";
      Proofsgen.deepfile := rawname ^ "_Deep";
      let proofs_output = get_full_filename !source "_Corres.v" in
      let oc = open_out proofs_output in
      match BarocqShallowgen.monadify_norm_program prog with
      | Errors.OK prog ->
          Proofsgen.print_proofs oc prog;
          printf "Correspondence proofs generated at %s\n" proofs_output
      | Errors.Error _ ->
          failwith "Error: fail to generate the correspondence proofs\n"
    end;

    if !opt_gen_shallow then begin
      let shallow_output = get_full_filename !source "_Shallow.v" in
      let oc = open_out shallow_output in
      match BarocqShallowgen.monadify_norm_program prog with
      | Errors.OK prog ->
          Shallowgen.print_program oc prog;
          printf "Shallow-embedding generated at %s\n" shallow_output
      | Errors.Error _ ->
          failwith "Error: fail to generate the shallow-embedding\n"
    end;

    if !opt_gen_deep then begin
      let deep_output = get_full_filename !source "_Deep.v" in
      let oc = open_out deep_output in
      Deepgen.print_program oc prog;
      printf "Deep-embedding generated at %s\n" deep_output
    end;

    let comp =
      if !flag_bbnf_v2 then Compiler.compile2
      else Compiler.compile !flag_simpl_bbnf
    in
    match comp prog with
    | Errors.OK prog ->
        Camlcoq.use_canonical_atoms := true;
        let ids = Clightgen.program_idents prog in
        record_idents (List.map PrintCommon.ident_to_string ids);
        set_c_filename !source;
        PrintClight.destination := Some !c_output;
        PrintClight.print_if_2 prog;
        printf "C file generated at %s\n" !c_output
    | Errors.Error msg -> raise @@ CompilerError (C2C.string_of_errmsg msg)
  with
  | Sys_error msg -> eprintf "System error: %s\n" msg
  | Blexer.Error msg -> eprintf "Lexer error: %s\n" msg
  | Bparser.Error -> eprintf "Parsing error\n"
  | Interpreter.Error msg -> eprintf "Interpretation error: %s\n" msg
  | CompilerError msg -> eprintf "Compilation error: %s\n" msg
  | Failure msg -> eprintf "%s" msg
