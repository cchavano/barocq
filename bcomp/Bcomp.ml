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

let debug = ref false

let source_files = ref []

let c_output = ref "a.c"

let rocq_output_prefix = ref "a"

let output_dir = ref "."

let opt_interp = ref false

let opt_parse = ref false

let opt_typecheck = ref false

let opt_aliascheck = ref false

let opt_print_tokens = ref false

let opt_print = ref []

let opt_gen_header = ref false

let opt_gen_corres = ref false

let opt_gen_alias_call_state_of = ref ""

let opt_gen_alias_return_state_of = ref ""

let opt_debug_aliasing = ref false

let opt_export_csyntax = ref false

let opt_copy = ref false

let target_arch = ref (if Archi.ptr64 then Target.Ptr64 else Target.Ptr32)

let set_target_arch (s : string) : unit =
  let arch =
    if s = "ptr32" then Target.Ptr32
    else if s = "ptr64" then Target.Ptr64
    else raise @@ UnknownTargetArch
  in
  target_arch := arch

let set_opt_print s =
  opt_print :=
    (match s with
    | "barocq" -> Compiler.Ir_Barocq
    | "bbnf" -> Compiler.Ir_BBNF
    | "ibnf" -> Compiler.Ir_IBNF
    | "imp1" -> Compiler.Ir_Imp1
    | "copy" -> Compiler.Ir_Copy
    | "imp2" -> Compiler.Ir_Imp2
    | _ -> failwith "Invalid intermediate language")
    :: !opt_print

let file_types_impl = ref ""

let dot_png_cmd = sprintf "dot -Tpng %s > %s.png"

let usage_msg = "Usage: barocq [options] <files> \noptions:"

let options =
  [
    ("-debug", Arg.Set debug, "\t\t\t\tdebug flag");
    ("-interp", Arg.Set opt_interp, "\t\t\t\tInterpret the given files");
    ( "-parse",
      Arg.Set opt_parse,
      "\t\t\t\tParse the given files (stop after parsing)" );
    ("-typecheck", Arg.Set opt_typecheck, "\t\t\t\tTypecheck the input files");
    ( "-aliascheck",
      Arg.Set opt_aliascheck,
      "\t\t\t\tRun the alias analysis on the input files" );
    ("-o", Arg.Set_string c_output, "<file>\t\t\t\tGenerate C output in <file>");
    ( "-orocq",
      Arg.Set_string rocq_output_prefix,
      "<prefix>\t\t\tPrefix all Rocq generated files with <prefix_> (default: \
       name of the C output)" );
    ( "-odir",
      Arg.Set_string output_dir,
      "<dir>\t\t\t\tPlace all generated files in <dir>" );
    ( "-print-tokens",
      Arg.Set opt_print_tokens,
      "\t\t\tPrint parsed tokens (stop after lexing)" );
    ( "-print",
      Arg.Symbol (["barocq"; "bbnf"; "ibnf"; "imp1"; "copy"; "imp2"], set_opt_print),
      "\tPretty-print the IR" );
    ("-export-csyntax", Arg.Set opt_export_csyntax, "Export the Csyntax AST");
    ( "-debug-aliasing",
      Arg.Set opt_debug_aliasing,
      "\t\t\tDisplay the alias analysis debugging information on stderr" );
    ( "-opt-copy", Arg.Set opt_copy,"\tPerform copy propagation");
    ( "-types-impl",
      Arg.Set_string file_types_impl,
      "<file>\t\t\tUse <file> as the C implementation for abstract types" );
    ("-gen-header", Arg.Set opt_gen_header, "\t\t\t\tGenerate the C header file");
    ( "-gen-corres",
      Arg.Set opt_gen_corres,
      "\t\t\t\tGenerate the Rocq embeddings correspondence material" );
    ( "-target-arch",
      Arg.String set_target_arch,
      "\t\t\t\tSet the target architecture for which the generated C will be \
       compiled (ptr32 or ptr64)" );
  ]

let set_source_files (file : string) : unit =
  source_files := file :: !source_files

let get_raw_filename (file : string) : string =
  Filename.remove_extension (Filename.basename file)

let get_full_filename (file : string) (suffix : string) : string =
  let file = sprintf "%s/%s" !output_dir file in
  let rawname = get_raw_filename file in
  let dirname = Filename.dirname file in
  Printf.sprintf "%s/%s%s" dirname rawname suffix

let clean_filename (file : string) : string =
  if String.starts_with ~prefix:"./" file then
    String.sub file 2 (String.length file - 2)
  else file

let gen_rocq_prefix () : string =
  if !rocq_output_prefix <> "a" then !rocq_output_prefix
  else get_raw_filename !c_output

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
      PrintTokens.print lexbuf;
      close_in input
    with
    | Blexer.Error msg -> raise (SyntaxError (lexbuf, msg))
    | Bparser.Error -> raise (SyntaxError (lexbuf, ""))
  in
  List.iter aux files

let irname = function
 | Compiler.Ir_Barocq  -> "barocq"
 | Compiler.Ir_BBNF    -> "bbnf"
 | Compiler.Ir_IBNF    -> "ibnf"
 | Compiler.Ir_Imp1    -> "imp1"
 | Compiler.Ir_Copy    -> "copy"
 | Compiler.Ir_Imp2    -> "imp2"
 | Compiler.Ir_Csyntax ->  "csyntax"



let gen_compile_opt () =
  let irs_log = !opt_print in
  (* Always generate C *)
  let irs_gen = if !opt_gen_corres then [Compiler.Ir_BBNF; Compiler.Ir_Csyntax;]
    else  [Compiler.Ir_Csyntax] in 
  let optim = if !opt_copy then [Compiler.Opt_Copy] else [] in 
  let opt = { Compiler.dbg_analysis = !opt_debug_aliasing;
              Compiler.ir_log = irs_log;
              Compiler.ir_gen = irs_gen;
              Compiler.ir_opt = optim;
            } in
  if !debug then
    begin
      Printf.fprintf stdout "[debug]";
      List.iter (fun s -> Printf.fprintf stdout "%s, " (irname s)) opt.Compiler.ir_gen;
      output_string stdout "\n"
    end ;
  opt

let output_log o l =
  let output_string o s =
    Stdlib.output_string o (Camlcoq.camlstring_of_coqstring s);
    o
  in
  Pp.Log.pp output_string o l

let rec get_csyntax (l : Compiler.ir_prog list) : Csyntax.program option =
  match l with
  | [] -> None
  | Compiler.Csyntax p :: l -> Some p
  | _ :: l -> get_csyntax l

let rec get_bnf (l : Compiler.ir_prog list) : BarocqBNF.program option =
  match l with
  | [] -> None
  | Compiler.BarocqBNF p :: l -> Some p
  | _ :: l -> get_bnf l

let generate_c (gen_csyntax : bool) (gen_header : bool)
    (l : Compiler.ir_prog list) =
  match get_csyntax l with
  | None ->
      raise
        (CompilerError "C code cannot be generated (add option for Ir_csyntax)")
  | Some prog ->
      Camlcoq.use_canonical_atoms := true;
      let ids = Csyntaxgen.program_idents prog in
      record_idents
        (List.map
           (fun id ->
             Camlcoq.camlstring_of_coqstring (Ctypesdefs.string_of_ident id))
           ids);
      begin
        let cfile = get_full_filename !c_output ".c" in
        PrintCprog.destination := Some cfile;
        (* Program printing *)
        PrintCprog.print_csyntax !file_types_impl prog;
        printf "C file generated at %s\n" (clean_filename cfile)
      end;
      (* Rocq Csyntax export *)
      if gen_csyntax then begin
        let csyntax_file = get_full_filename !c_output ".v" in
        PrintCprog.export_csyntax !c_output prog csyntax_file;
        printf "Csyntax exported at %s\n" (clean_filename csyntax_file)
      end;
      (* Header printing *)
      if gen_header then begin
        let hfile = get_full_filename !c_output ".h" in
        PrintCprog.print_header !file_types_impl hfile prog;
        printf "Header file generated at %s\n" (clean_filename hfile)
      end

let gen_rocq_program (prog : Barocq.program) =
  match
    BarocqShallowgen.monadify_norm_program
      !target_arch
      BarocqShallowgen.ShallowR
      prog
  with
  | Res.OK prog -> prog
  | Res.Error msg ->
      raise
      @@ UnexpectedError
           (sprintf
              "fail to generate the ShallowR embedding: %s"
              (PrintUtils.string_of_errmsg msg))

let gen_shallowB_program (l : Compiler.ir_prog list) =
  match get_bnf l with
  | None -> raise @@ UnexpectedError (sprintf "BarocqBNF is not generated")
  | Some bnf -> (
      let prog = BarocqBNFUndo.decompile_program bnf in
      match
        BarocqShallowgen.monadify_norm2_program
          !target_arch
          BarocqShallowgen.ShallowB
          prog
      with
      | Res.OK bprog -> bprog
      | Res.Error msg ->
          raise
          @@ UnexpectedError
               (sprintf
                  "fail to generate the ShallowB embedding: %s"
                  (PrintUtils.string_of_errmsg msg)))

let generate_corres (prog : Barocq.program) (tprog : Barocq.Typed.program)
    (l : Compiler.ir_prog list) =
  if !debug then Printf.fprintf stdout "gen_corress := %b\n" !opt_gen_corres;
  if not !opt_gen_corres then ()
  else begin
    if !debug then Printf.fprintf stdout "generate embeddings\n";
    (* Generate Rocq Shallow embedding *)
    Printf.fprintf stdout "Generation in directory %s\n" !output_dir;
    let rprog = gen_rocq_program prog in
    let rawname = gen_rocq_prefix () in
    let full_filename = get_full_filename rawname in
    let file = get_full_filename rawname "_ShallowR.v" in
    let oc = open_out file in
    Shallowgen.coqlib := rawname;
    Shallowgen.SR.print_program oc rprog;
    close_out oc;
    printf "ShallowR embedding generated at %s\n" (Filename.basename file);
    (* Generate Rocq Deep embedding *)
    let rawname = gen_rocq_prefix () in
    let file = get_full_filename rawname "_Deep.v" in
    let oc = open_out file in
    let dprog =
      match get_bnf l with
      | None -> raise @@ UnexpectedError "Barocq BNF is not generated"
      | Some p -> p
    in
    Deepgen.BarocqBNFDeep.print_program oc dprog;
    close_out oc;
    printf "Deep embedding generated at %s\n" (Filename.basename file);

    (* Generation of ShallowB types *)
    let types_file = get_full_filename rawname "_Types.v" in
    let types_oc = open_out types_file in
    Btypesgen.coqlib := rawname;
    Btypesgen.print types_oc rprog;
    printf "ShallowB types generated at %s\n" (Filename.basename types_file);
    (* Generation of ShallowB program *)
    let bprog = gen_shallowB_program l in
    let shallowB_file = get_full_filename rawname "_ShallowB.v" in
    let shallowB_oc = open_out shallowB_file in
    Shallowgen.coqlib := rawname;
    Shallowgen.SB.print_program shallowB_oc bprog;
    close_out shallowB_oc;
    printf
      "ShallowB embedding generated at %s\n"
      (Filename.basename shallowB_file);
    (* ShallowR <-> ShallowB correspondence *)
    CorresRBgen.coqlib := rawname;
    let corresRB_tactics_file = full_filename "_CorresRB_Tactics.v" in
    let corresRB_tactics_oc = open_out corresRB_tactics_file in
    CorresRBgen.HelperTactics.print corresRB_tactics_oc rprog bprog;
    close_out corresRB_tactics_oc;
    printf
      "ShallowR <-> ShallowB helper tactics generated at %s\n"
      (Filename.basename corresRB_tactics_file);
    let corresRB_file = full_filename "_CorresRB.v" in
    let corresRB_oc = open_out corresRB_file in
    CorresRBgen.print_corres corresRB_oc rprog bprog;
    close_out corresRB_oc;
    printf
      "ShallowR <-> ShallowB correspondence theorems generated at %s\n"
      (Filename.basename corresRB_file);

    (* ShallowB <-> Deep correspondence *)
    CorresBDgen.coqlib := rawname;
    let preludeBD_file = full_filename "_CorresBD_Prelude.v" in
    let corresBD_proof = full_filename "_CorresBD_Proof.v" in
    let corresBD_file = full_filename "_CorresBD.v" in
    let preludeBD_oc = open_out preludeBD_file in
    let corresBD_oc = open_out corresBD_file in
    CorresBDgen.print_prelude preludeBD_oc !target_arch tprog bprog;
    CorresBDgen.print_proof !target_arch corresBD_proof;
    CorresBDgen.print_corres corresBD_oc !target_arch bprog;
    close_out preludeBD_oc;
    close_out corresBD_oc;
    printf
      "ShallowB <-> Deep correspondence prelude generated at %s\n"
      (clean_filename preludeBD_file);
    printf
      "ShallowB <-> Deep correspondence theorems generated at %s\n"
      (clean_filename corresBD_file);

    (* ShallowR <-> Deep correspondence *)
    CorresRDgen.coqlib := rawname;
    let corresRD_file = full_filename "_CorresRD.v" in
    let corresRD_oc = open_out corresRD_file in
    CorresRDgen.print_corres corresRD_oc !target_arch rprog;
    printf
      "ShallowR <-> Deep correspondence theorems generated at %s\n"
      (clean_filename corresRD_file);
    close_out corresRD_oc
  end

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

      SurfaceTyping.set_arr_index_btyp !target_arch;

      let iprog, ginfo = SurfaceTyping.typecheck_iprogram s_iprog in

      if !opt_typecheck then begin
        printf "Typechecking succeeded\n";
        exit 0
      end;

      let prog = Barocq.iprog_to_prog iprog in

      let tiprog =
        match Barocq.Typing.typecheck_iprogram !target_arch iprog with
        | Res.OK p -> p
        | Res.Error msg ->
            raise @@ UnexpectedError (PrintUtils.string_of_errmsg msg)
      in

      let tprog = Barocq.Typing.program_of_iprogram tiprog in

      if !opt_interp then begin
        let _ = Binterpreter.interpret !target_arch tiprog in
        exit 0
      end;

      if !opt_aliascheck then begin
        begin match
          Compiler.aliascheck_program (gen_compile_opt ()) !target_arch prog
        with
        | Res.OK _ -> printf "Alias checking succeeded\n"
        | Res.Error msg ->
            raise @@ CompilerError (PrintUtils.string_of_errmsg msg)
        end;
        exit 0
      end;

      match Compiler.compile (gen_compile_opt ()) !target_arch ginfo prog with
      | Res.OK (progs, log) -> begin
          ignore (output_log stdout log);
          generate_c !opt_export_csyntax !opt_gen_header progs;
          generate_corres prog tprog progs
        end
      | Res.Error msg ->
          raise @@ CompilerError (PrintUtils.string_of_errmsg msg)
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
    | UnknownTargetArch ->
        eprintf "Error: the target architecture must be \"ptr32\" or \"ptr64\""
  end
