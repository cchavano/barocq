open Lexing
open Printf

exception CompilerError of string

exception UnexpectedError of string

exception SyntaxError of lexbuf * string

exception UnknownTargetArch

let syntax_error_msg lexbuf msg =
  let startpos = Lexing.lexeme_start_p lexbuf in
  let endpos = Lexing.lexeme_end_p lexbuf in
  let sep = if msg = "" then "" else "\n>> " in
  sprintf
    "%s: Syntax error%s%s"
    (Location.to_string (Location.make startpos endpos ()))
    sep
    msg

let source_files = ref []

let c_output = ref "a.c"

let opt_interp = ref false

let opt_parse = ref false

let opt_typecheck = ref false

let opt_aliascheck = ref false

let opt_print_tokens = ref false

let opt_print_bbnf = ref false

let opt_print_imp1 = ref false

let opt_gen_header = ref false

let opt_gen_shallow = ref false

let opt_gen_deep = ref false

let opt_gen_corres = ref false

let opt_gen_corres_all = ref false

let opt_gen_alias_call_state_of = ref ""

let opt_gen_alias_return_state_of = ref ""

let opt_debug_aliasing = ref false

let target_arch = ref (if Archi.ptr64 then "ptr64" else "ptr32")

let file_types_impl = ref ""

let dot_png_cmd = sprintf "dot -Tpng %s > %s.png"

let usage_msg = "Usage: barocq [options] <files> \noptions:"

let options =
  [
    ("-interp", Arg.Set opt_interp, "\t\t\t\tInterpret the given files");
    ( "-parse",
      Arg.Set opt_parse,
      "\t\t\t\tParse the given files (stop after parsing)" );
    ("-typecheck", Arg.Set opt_typecheck, "\t\t\t\tTypecheck the input files");
    ( "-aliascheck",
      Arg.Set opt_aliascheck,
      "\t\t\t\tRun the alias analysis on the input files" );
    ("-o", Arg.Set_string c_output, "<file>\t\t\t\tGenerate C output in <file>");
    ( "-print-tokens",
      Arg.Set opt_print_tokens,
      "\t\t\tPrint parsed tokens (stop after lexing)" );
    ( "-print-bbnf",
      Arg.Set opt_print_bbnf,
      "\t\t\t\tPretty-print B-normal form IR" );
    ("-print-imp1", Arg.Set opt_print_imp1, "\t\t\t\tPretty-print Imp1 IR");
    ( "-debug-aliasing",
      Arg.Set opt_debug_aliasing,
      "\t\t\tDisplay the alias analysis debugging information on stderr" );
    ( "-types-impl",
      Arg.Set_string file_types_impl,
      "<file>\t\t\tUse <file> as the C implementation for abstract types" );
    ("-gen-header", Arg.Set opt_gen_header, "\t\t\t\tGenerate the C header file");
    ( "-gen-shallow",
      Arg.Set opt_gen_shallow,
      "\t\t\t\tGenerate the Rocq shallow embedding" );
    ( "-gen-deep",
      Arg.Set opt_gen_deep,
      "\t\t\t\tGenerate the Rocq deep embedding" );
    ( "-gen-corres",
      Arg.Set opt_gen_corres,
      "\t\t\t\tGenerate the correspondance theorems between the Rocq embeddings"
    );
    ( "-gen-corres-all",
      Arg.Set opt_gen_corres_all,
      "\t\t\tGenerate the embeddings and the correspondence theorems" );
    ( "-gen-call-state-of",
      Arg.Set_string opt_gen_alias_call_state_of,
      "<fun_name>\t\tGenerate the aliasing call state of <fun_name>" );
    ( "-gen-return-state-of",
      Arg.Set_string opt_gen_alias_return_state_of,
      "<fun_name>\tGenerate the aliasing return state of <fun_name>" );
    ( "-target-arch",
      Arg.Set_string target_arch,
      "\t\t\t\tSet the target architecture for which the generated C will be \
       compiled (ptr32 or ptr64)" );
  ]

let set_source_files (file : string) : unit =
  source_files := file :: !source_files

let get_raw_filename (file : string) : string =
  Filename.remove_extension (Filename.basename file)

let get_full_filename (file : string) (suffix : string) : string =
  let rawname = get_raw_filename file in
  let dirname = Filename.dirname file in
  Printf.sprintf "%s/%s%s" dirname rawname suffix

let arch_of_string (s : string) : Target.archi =
  if s = "ptr32" then Target.Ptr32
  else if s = "ptr64" then Target.Ptr64
  else raise @@ UnknownTargetArch

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

let print_token_stream (files : string list) : unit =
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
        print_token_stream !source_files;
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

      if !opt_interp then begin
        let _ = Binterpreter.interpret (arch_of_string !target_arch) iprog in
        exit 0
      end;

      if !opt_aliascheck then begin
        begin
          match
            Compiler.aliascheck_program
              !opt_debug_aliasing
              (arch_of_string !target_arch)
              prog
          with
          | Errors.OK _ -> printf "Alias checking succeeded\n"
          | Errors.Error msg ->
              raise @@ CompilerError (C2C.string_of_errmsg msg)
        end;
        exit 0
      end;

      if !opt_print_bbnf then begin
        let bbnf =
          BarocqBNFgen.norm_program (arch_of_string !target_arch) prog
        in
        begin
          match bbnf with
          | Errors.OK prog -> PrintBarocqBNF.print_program stdout prog
          | Errors.Error msg ->
              raise @@ CompilerError (C2C.string_of_errmsg msg)
        end;
        exit 0
      end;

      if !opt_print_imp1 then begin
        let imp1 =
          Compiler.compile_to_imp1 (arch_of_string !target_arch) prog
        in
        begin
          match imp1 with
          | Errors.OK prog -> PrintImp1.print_program stdout prog
          | Errors.Error msg ->
              raise @@ CompilerError (C2C.string_of_errmsg msg)
        end;
        exit 0
      end;

      if !opt_gen_alias_call_state_of <> "" then begin
        let imp1 =
          Compiler.compile_to_imp1 (arch_of_string !target_arch) prog
        in
        begin
          match imp1 with
          | Errors.OK prog -> begin
              match
                Imp1.Typing.typecheck_program (arch_of_string !target_arch) prog
              with
              | Errors.OK prog -> begin
                  let fid = !opt_gen_alias_call_state_of in
                  match Aliasing_impl.get_fun_descr prog fid with
                  | Some fdescr ->
                      let callstate = fdescr.Aliasing_defs.fd_callstate in
                      let dotfile = sprintf "%s_call_state.dot" fid in
                      let dotfile_rev = sprintf "%s_call_state_rev.dot" fid in
                      let out = open_out dotfile in
                      let out_rev = open_out dotfile_rev in
                      Aliasing_impl.DotExport.print_state
                        out
                        (Aliasing_defs.AbsDom.AbsState callstate);
                      Aliasing_impl.DotExport.print_rev_state
                        out_rev
                        (Aliasing_defs.AbsDom.AbsState callstate);
                      close_out out;
                      close_out out_rev;
                      let _ = Unix.system (dot_png_cmd dotfile dotfile) in
                      let _ =
                        Unix.system (dot_png_cmd dotfile_rev dotfile_rev)
                      in
                      ()
                  | _ ->
                      eprintf "Error: function \"%s\" is not defined" fid;
                      exit 1
                end
              | Errors.Error msg ->
                  raise
                  @@ UnexpectedError
                       (sprintf
                          "Imp1 typing failed: %s"
                          (C2C.string_of_errmsg msg))
            end
          | Errors.Error msg ->
              raise @@ CompilerError (C2C.string_of_errmsg msg)
        end
      end;

      if !opt_gen_alias_return_state_of <> "" then begin
        let imp1 =
          Compiler.compile_to_imp1 (arch_of_string !target_arch) prog
        in
        begin
          match imp1 with
          | Errors.OK prog -> begin
              match
                Imp1.Typing.typecheck_program (arch_of_string !target_arch) prog
              with
              | Errors.OK prog -> begin
                  let fid = !opt_gen_alias_return_state_of in
                  match Aliasing_impl.get_fun_descr prog fid with
                  | Some fdescr ->
                      let returnstate = fdescr.Aliasing_defs.fd_returnstate in
                      let dotfile = sprintf "%s_return_state.dot" fid in
                      let dotfile_rev = sprintf "%s_return_state_rev.dot" fid in
                      let out = open_out dotfile in
                      let out_rev = open_out dotfile_rev in
                      Aliasing_impl.DotExport.print_state out returnstate;
                      Aliasing_impl.DotExport.print_rev_state
                        out_rev
                        returnstate;
                      close_out out;
                      close_out out_rev;
                      let _ = Unix.system (dot_png_cmd dotfile dotfile) in
                      let _ =
                        Unix.system (dot_png_cmd dotfile_rev dotfile_rev)
                      in
                      ()
                  | _ ->
                      eprintf "function \"%s\" is not defined" fid;
                      exit 1
                end
              | Errors.Error msg ->
                  raise
                  @@ UnexpectedError
                       (sprintf
                          "Imp1 typing failed: %s"
                          (C2C.string_of_errmsg msg))
            end
          | Errors.Error msg ->
              raise @@ CompilerError (C2C.string_of_errmsg msg)
        end
      end;

      if !opt_gen_corres_all then begin
        opt_gen_corres := true;
        opt_gen_shallow := true;
        opt_gen_deep := true
      end;

      if !opt_gen_corres then begin
        let rawname = get_raw_filename !c_output in
        (* let coqlib =
          let bytes = String.to_bytes rawname in
          Bytes.fill bytes 0 1 (Char.uppercase_ascii (String.get rawname 0));
          Bytes.to_string bytes
        in *)
        Corresgen.coqlib := rawname;
        Corresgen.shallowfile := rawname ^ "_Shallow";
        Corresgen.deepfile := rawname ^ "_Deep";
        let proofs_output = get_full_filename !c_output "_Corres.v" in
        let oc = open_out proofs_output in
        match
          BarocqShallowgen.monadify_norm_program
            (arch_of_string !target_arch)
            prog
        with
        | Errors.OK prog ->
            Corresgen.print_program (arch_of_string !target_arch) oc prog;
            printf "Correspondence theorems generated at %s\n" proofs_output;
            close_out oc
        | Errors.Error msg ->
            close_out oc;
            raise
            @@ UnexpectedError
                 (sprintf
                    "fail to generate the correspondence theorems: %s"
                    (C2C.string_of_errmsg msg))
      end;

      if !opt_gen_shallow then begin
        let shallow_output = get_full_filename !c_output "_Shallow.v" in
        let oc = open_out shallow_output in
        match
          BarocqShallowgen.monadify_norm_program
            (arch_of_string !target_arch)
            prog
        with
        | Errors.OK prog ->
            Shallowgen.print_program oc prog;
            printf "Shallow-embedding generated at %s\n" shallow_output;
            close_out oc
        | Errors.Error msg ->
            close_out oc;
            raise
            @@ UnexpectedError
                 (sprintf
                    "fail to generate the shallow-embedding: %s"
                    (C2C.string_of_errmsg msg))
      end;

      if !opt_gen_deep then begin
        let deep_output = get_full_filename !c_output "_Deep.v" in
        let oc = open_out deep_output in
        Deepgen.print_program oc prog;
        printf "Deep-embedding generated at %s\n" deep_output;
        close_out oc
      end;

      match
        Compiler.compile !opt_debug_aliasing (arch_of_string !target_arch) prog
      with
      | Errors.OK prog ->
          Camlcoq.use_canonical_atoms := true;
          let ids = ClightCegen.program_idents prog in
          record_idents (List.map PrintCommon.ident_to_string ids);
          PrintClightCe.destination := Some !c_output;
          (* Program printing *)
          PrintCprog.print_clightce !file_types_impl prog;
          printf "C file generated at %s\n" !c_output;
          (* Header printing *)
          if !opt_gen_header then begin
            let header_file = get_full_filename !c_output ".h" in
            PrintCprog.print_header !file_types_impl header_file prog;
            printf "Header file generated at %s\n" header_file
          end;
          exit 0
      | Errors.Error msg -> raise @@ CompilerError (C2C.string_of_errmsg msg)
    with
    | Sys_error msg -> eprintf "System error: %s\n" msg
    | SyntaxError (lexbuf, msg) -> eprintf "%s\n" (syntax_error_msg lexbuf msg)
    | Binterpreter.Error msg ->
        let suffix = if msg = "" then "" else sprintf ": %s" msg in
        eprintf "Interpretation error%s\n" suffix
    | SurfaceTyping.Error (cause, loc) -> begin
        let msg = SurfaceTyping.msg_from_failure cause in
        match loc with
        | Some loc ->
            eprintf "%s: Typing error\n>> %s\n" (Location.to_string loc) msg
        | None -> assert false
      end
    | CompilerError msg -> eprintf "Compilation error: %s\n" msg
    | UnexpectedError msg ->
        eprintf "Unexpected error: %s\nPlease, make a bug report.\n" msg
    | Aliasing_impl.UnsupportedFeature msg ->
        eprintf "Compilation error: %s\n" msg
    | UnknownTargetArch ->
        eprintf "Error: the target architecture must be \"ptr32\" or \"ptr64\""
  end;
  exit 1
