open Lexing
open Printf

exception TypingError of string

exception CompilerError of string

let syntax_error_msg lexbuf msg =
  let startpos = Lexing.lexeme_start_p lexbuf in
  let endpos = Lexing.lexeme_end_p lexbuf in
  let from_single_pos pos =
    let l = pos.pos_lnum in
    let c = pos.pos_cnum - pos.pos_bol + 1 in
    Printf.sprintf "line %d, character %d" l c
  in
  let from_interval pos1 pos2 =
    let l = pos1.pos_lnum in
    let c1 = pos1.pos_cnum - pos1.pos_bol + 1 in
    let c2 = pos2.pos_cnum - pos1.pos_bol in
    Printf.sprintf "line %d, characters %d-%d" l c1 c2
  in
  let errloc =
    if startpos.pos_cnum = endpos.pos_cnum - 1 then from_single_pos startpos
    else from_interval startpos endpos
  in
  let msg = if msg = "" then "" else Printf.sprintf ": %s" msg in
  Printf.sprintf
    "Syntax error in file \"%s\", %s%s"
    startpos.pos_fname
    errloc
    msg

let source = ref ""

let c_output = ref ""

let opt_interp = ref false

let opt_parse = ref false

let opt_typecheck = ref false

let opt_print_tokens = ref false

let opt_print_bbnf = ref false

let opt_print_imp1 = ref false

let opt_gen_shallow = ref false

let opt_gen_deep = ref false

let opt_gen_corres = ref false

let opt_gen_alias_call_state_of = ref ""

let opt_gen_alias_return_state_of = ref ""

let opt_debug_aliasing = ref false

let usage_msg = "Usage: barocq [options] <file> \noptions:"

let options =
  [
    ("-interp", Arg.Set opt_interp, "\t\tInterpret the given file");
    ( "-parse",
      Arg.Set opt_parse,
      "\t\tParse the given file (stop after parsing)" );
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
    ( "-gen-corres",
      Arg.Set opt_gen_corres,
      "\t\tGenerate the correspondance proofs between the shallow and the \
       deep-embedding" );
    ( "-gen-call-state-of",
      Arg.Set_string opt_gen_alias_call_state_of,
      "\tGenerate the aliaising call state of the given function" );
    ( "-gen-return-state-of",
      Arg.Set_string opt_gen_alias_return_state_of,
      "\tGenerate the aliasing state after a complete execution of the given \
       function" );
    ( "-debug-aliasing",
      Arg.Set opt_debug_aliasing,
      "\tDisplay the alias analysis debugging information on stderr" );
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

    try
      lexbuf.lex_curr_p <-
        { pos_fname = !source; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 };

      if !opt_print_tokens then begin
        PrintTokens.print lexbuf;
        exit 0
      end;

      let xprog = Bparser.xprogram Blexer.read_token lexbuf in

      close_in input;

      if !opt_parse then begin
        printf "Parsing succeeded\n";
        exit 0
      end;

      let prog = Barocq.xprog_to_prog xprog in

      let prog_typed =
        match Barocq.Typing.typecheck_program prog with
        | Errors.OK p -> p
        | Errors.Error msg -> raise (TypingError (C2C.string_of_errmsg msg))
      in

      if !opt_typecheck then begin
        printf "Typechecking succeeded\n";
        exit 0
      end;

      if !opt_print_bbnf then begin
        let bbnf = BarocqBNFgen.normalize_program prog_typed in
        begin
          match bbnf with
          | Errors.OK prog -> PrintBarocqBNF.print_program stdout prog
          | Errors.Error msg ->
              raise @@ CompilerError (C2C.string_of_errmsg msg)
        end;
        exit 0
      end;

      if !opt_print_imp1 then begin
        let imp1 = Compiler.compile_to_imp1 prog in
        begin
          match imp1 with
          | Errors.OK prog -> PrintImp1.print_program stdout prog
          | Errors.Error msg ->
              raise @@ CompilerError (C2C.string_of_errmsg msg)
        end;
        exit 0
      end;

      if !opt_gen_alias_call_state_of <> "" then begin
        let imp1 = Compiler.compile_to_imp1 prog in
        begin
          match imp1 with
          | Errors.OK prog -> begin
              match Imp1.Typing.typecheck_program prog with
              | Errors.OK prog -> begin
                  let fid = "_" ^ !opt_gen_alias_call_state_of in
                  match Aliasing_impl.get_fun_descr prog fid with
                  | Some fdescr ->
                      let dotfile =
                        get_full_filename
                          !source
                          (sprintf "%s_call_state.dot" fid)
                      in
                      let dotfile_rev =
                        get_full_filename
                          !source
                          (sprintf "%s_call_state_rev.dot" fid)
                      in
                      let out = open_out dotfile in
                      let out_rev = open_out dotfile_rev in
                      Aliasing_impl.DotExport.print_state
                        out
                        (Aliasing_defs.AbsDom.AbsState
                           fdescr.Aliasing_defs.fd_callstate);
                      Aliasing_impl.DotExport.print_rev_state
                        out_rev
                        (Aliasing_defs.AbsDom.AbsState
                           fdescr.Aliasing_defs.fd_callstate);
                      close_out out;
                      close_out out_rev
                  | None ->
                      failwith
                        (sprintf
                           "Error: function \"%s\" is not defined"
                           !opt_gen_alias_call_state_of)
                end
              | Errors.Error msg ->
                  failwith
                    (sprintf "Imp1 typing error: %s" (C2C.string_of_errmsg msg))
            end
          | Errors.Error msg ->
              raise @@ CompilerError (C2C.string_of_errmsg msg)
        end
      end;

      if !opt_gen_alias_return_state_of <> "" then begin
        let imp1 = Compiler.compile_to_imp1 prog in
        begin
          match imp1 with
          | Errors.OK prog -> begin
              match Imp1.Typing.typecheck_program prog with
              | Errors.OK prog -> begin
                  let fid = "_" ^ !opt_gen_alias_return_state_of in
                  match Aliasing_impl.get_fun_descr prog fid with
                  | Some fdescr ->
                      let dotfile =
                        get_full_filename
                          !source
                          (sprintf "%s_return_state.dot" fid)
                      in
                      let dotfile_rev =
                        get_full_filename
                          !source
                          (sprintf "%s_return_state_rev.dot" fid)
                      in
                      let out = open_out dotfile in
                      let out_rev = open_out dotfile_rev in
                      Aliasing_impl.DotExport.print_state
                        out
                        fdescr.Aliasing_defs.fd_returnstate;
                      Aliasing_impl.DotExport.print_rev_state
                        out_rev
                        fdescr.Aliasing_defs.fd_returnstate;
                      close_out out;
                      close_out out_rev
                  | None ->
                      failwith
                        (sprintf
                           "Error: function \"%s\" is not defined"
                           !opt_gen_alias_call_state_of)
                end
              | Errors.Error msg ->
                  failwith
                    (sprintf "Imp1 typing error: %s" (C2C.string_of_errmsg msg))
            end
          | Errors.Error msg ->
              raise @@ CompilerError (C2C.string_of_errmsg msg)
        end
      end;

      begin
        if !opt_interp then
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
            printf "Correspondence proofs generated at %s\n" proofs_output;
            close_out oc
        | Errors.Error msg ->
            close_out oc;
            failwith "Error: fail to generate the correspondence proofs"
      end;

      if !opt_gen_shallow then begin
        let shallow_output = get_full_filename !source "_Shallow.v" in
        let oc = open_out shallow_output in
        match BarocqShallowgen.monadify_norm_program prog with
        | Errors.OK prog ->
            Shallowgen.print_program oc prog;
            printf "Shallow-embedding generated at %s\n" shallow_output;
            close_out oc
        | Errors.Error msg ->
            close_out oc;
            failwith "Error: fail to generate the shallow-embedding"
      end;

      if !opt_gen_deep then begin
        let deep_output = get_full_filename !source "_Deep.v" in
        let oc = open_out deep_output in
        Deepgen.print_program oc prog;
        printf "Deep-embedding generated at %s\n" deep_output;
        close_out oc
      end;

      match Compiler.compile !opt_debug_aliasing prog with
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
    | Blexer.Error msg -> eprintf "%s\n" (syntax_error_msg lexbuf msg)
    | Bparser.Error -> eprintf "%s\n" (syntax_error_msg lexbuf "")
    | Interpreter.Error msg -> eprintf "Interpretation error: %s\n" msg
    | TypingError msg -> eprintf "Typing error: %s\n" msg
    | CompilerError msg -> eprintf "Compilation error: %s\n" msg
    | Failure msg -> eprintf "Unexpected error: %s\n" msg
    | Aliasing_impl.UnsupportedFeature msg ->
        eprintf "Compilation error: %s\n" msg
    | Assert_failure (src, _, _) ->
        eprintf
          "Impossible error coming from %s. Please, make a bug report.\n"
          src
  with Sys_error msg -> eprintf "System error: %s\n" msg
