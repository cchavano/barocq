open Lexing
open Printf

exception CompilerError of string

exception SyntaxError of lexbuf * string

let syntax_error_msg lexbuf msg =
  let startpos = Lexing.lexeme_start_p lexbuf in
  let endpos = Lexing.lexeme_end_p lexbuf in
  let sep = if msg = "" then "" else ": " in
  sprintf
    "Syntax error %s%s%s"
    (Location.to_string (Location.make startpos endpos ()))
    sep
    msg

let source_files = ref []

let c_output = ref "a.c"

let opt_interp = ref false

let opt_parse = ref false

let opt_typecheck = ref false

let opt_print_tokens = ref false

let opt_print_bbnf = ref false

let opt_print_imp1 = ref false

let opt_gen_header = ref false

let opt_gen_shallow = ref false

let opt_gen_deep = ref false

let opt_gen_corres = ref false

let opt_gen_alias_call_state_of = ref ""

let opt_gen_alias_return_state_of = ref ""

let opt_debug_aliasing = ref false

let usage_msg = "Usage: barocq [options] <files> \noptions:"

let options =
  [
    ("-interp", Arg.Set opt_interp, "\t\tInterpret the given files");
    ( "-parse",
      Arg.Set opt_parse,
      "\t\tParse the given files (stop after parsing)" );
    ( "-typecheck",
      Arg.Set opt_typecheck,
      "\t\tTypecheck the input files (do not compile)" );
    ("-o", Arg.Set_string c_output, "<file>\t\tGenerate C output in <file>");
    ( "-print-tokens",
      Arg.Set opt_print_tokens,
      "\tPrint parsed tokens (stop after lexing)" );
    ("-print-bbnf", Arg.Set opt_print_bbnf, "\t\tPretty-print B-normal form IR");
    ("-print-imp1", Arg.Set opt_print_imp1, "\t\tPretty-print Imp1 IR");
    ("-gen-header", Arg.Set opt_gen_header, "\t\tGenerate the C header file");
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

let set_source_files (file : string) : unit =
  source_files := file :: !source_files

let get_raw_filename (file : string) : string =
  Filename.remove_extension (Filename.basename file)

let get_full_filename (file : string) (suffix : string) : string =
  let rawname = get_raw_filename file in
  let dirname = Filename.dirname file in
  Printf.sprintf "%s/%s%s" dirname rawname suffix

(* let set_c_filename (file : string) : unit =
  if !c_output = "" then c_output := get_full_filename file ".c" else () *)

let rec record_idents (ids : string list) : unit =
  match ids with
  | [] -> ()
  | h :: t ->
      let _ = Camlcoq.intern_string h in
      record_idents t

let init_lexbuf (file : string) (lexbuf : lexbuf) : unit =
  lexbuf.lex_curr_p <-
    { pos_fname = file; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 }

let parse_one_file (file : string) : SurfaceAST.imodul =
  let input = open_in file in
  let lexbuf = from_channel input in
  init_lexbuf file lexbuf;
  try
    let imod = Bparser.imodul Blexer.read_token lexbuf in
    close_in input;
    imod
  with
  | Blexer.Error msg -> raise (SyntaxError (lexbuf, msg))
  | Bparser.Error -> raise (SyntaxError (lexbuf, ""))

let parse_all_files (files : string list) : SurfaceAST.iprogram =
  List.map parse_one_file files

let print_tokens (files : string list) : unit =
  let aux file =
    let input = open_in file in
    let lexbuf = from_channel input in
    init_lexbuf file lexbuf;
    try
      printf "Start of file \"%s\" ========\n" file;
      PrintTokens.print lexbuf;
      close_in input;
      printf "End of file \"%s\" ========\n" file
    with
    | Blexer.Error msg -> raise (SyntaxError (lexbuf, msg))
    | Bparser.Error -> raise (SyntaxError (lexbuf, ""))
  in
  List.iter aux files

let print_header file prog =
  let aux p prog =
    Format.fprintf p "@[<v 0>";
    List.iter (PrintCsyntax.declare_composite p) prog.Ctypes.prog_types;
    List.iter (PrintCsyntax.define_composite p) prog.Ctypes.prog_types;
    List.iter (PrintClight.print_globdecl p) prog.Ctypes.prog_defs;
    Format.fprintf p "@]@."
  in
  let oc = open_out file in
  aux (Format.formatter_of_out_channel oc) prog;
  close_out oc

let () =
  begin
    Arg.parse options set_source_files usage_msg;

    if !source_files = [] then begin
      eprintf "Error: no source file provided\n";
      exit 1
    end;

    source_files := List.rev !source_files;

    try
      if !opt_print_tokens then begin
        print_tokens !source_files;
        exit 0
      end;

      let s_iprog = parse_all_files !source_files in

      if !opt_parse then begin
        printf "Parsing succeeded\n";
        exit 0
      end;

      let iprog = SurfaceTyping.typecheck_iprogram s_iprog in

      let prog = Barocq.iprog_to_prog iprog in

      if !opt_typecheck then begin
        printf "Typechecking succeeded\n";
        exit 0
      end;

      if !opt_print_bbnf then begin
        let bbnf = BarocqBNFgen.norm_program prog in
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
                          !c_output
                          (sprintf "%s_call_state.dot" fid)
                      in
                      let dotfile_rev =
                        get_full_filename
                          !c_output
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
                          !c_output
                          (sprintf "%s_return_state.dot" fid)
                      in
                      let dotfile_rev =
                        get_full_filename
                          !c_output
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
          let _ = Interpreter.interpret iprog in
          exit 0
      end;

      if !opt_gen_corres then begin
        opt_gen_shallow := true;
        opt_gen_deep := true;
        let rawname = get_raw_filename !c_output in
        let coqlib =
          let bytes = String.to_bytes rawname in
          Bytes.fill bytes 0 1 (Char.uppercase_ascii (String.get rawname 0));
          Bytes.to_string bytes
        in
        Proofsgen.coqlib := coqlib;
        Proofsgen.shallowfile := rawname ^ "_Shallow";
        Proofsgen.deepfile := rawname ^ "_Deep";
        let proofs_output = get_full_filename !c_output "_Corres.v" in
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
        let shallow_output = get_full_filename !c_output "_Shallow.v" in
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
        let deep_output = get_full_filename !c_output "_Deep.v" in
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
          PrintClight.destination := Some !c_output;
          (* Program printing *)
          PrintClight.print_if_2 prog;
          printf "C file generated at %s\n" (get_full_filename !c_output ".c");
          (* Header printing *)
          if !opt_gen_header then begin
            let header_file = get_full_filename !c_output ".h" in
            print_header header_file prog;
            printf "Header file generated at %s\n" header_file
          end;
          exit 0
      | Errors.Error msg -> raise @@ CompilerError (C2C.string_of_errmsg msg)
    with
    | Sys_error msg -> eprintf "System error: %s\n" msg
    | SyntaxError (lexbuf, msg) -> eprintf "%s\n" (syntax_error_msg lexbuf msg)
    | Interpreter.Error msg -> eprintf "Interpretation error: %s\n" msg
    | SurfaceTyping.Error (cause, loc) -> begin
        let msg = SurfaceTyping.msg_from_failure cause in
        match loc with
        | Some loc ->
            eprintf "Typing error %s\n> %s\n" (Location.to_string loc) msg
        | None -> assert false
      end
    | CompilerError msg -> eprintf "Compilation error: %s\n" msg
    | Failure msg -> eprintf "Unexpected error: %s\n" msg
    | Aliasing_impl.UnsupportedFeature msg ->
        eprintf "Compilation error: %s\n" msg
    | Assert_failure (src, _, _) ->
        eprintf
          "Impossible error coming from %s. Please, make a bug report.\n"
          src
  end;
  exit 1
