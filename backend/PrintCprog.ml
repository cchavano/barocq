open Format
open PrintCsyntax
open AST

let _ = PrintCsyntax.src := Lang_barocq

let destination : string option ref = ref None

let print_csyntax (types_header : string) (prog : Csyntax.program) : unit =
  match !destination with
  | None -> ()
  | Some f ->
      PrintCsyntax.destination := !destination;
      Barocq2C.glob_arrays := Csyntaxgen.program_glob_arrays prog;
      let oc = open_out f in
      if types_header <> "" then
        Printf.fprintf oc "#include \"%s\"\n\n" types_header;
      PrintCsyntax.print_program (formatter_of_out_channel oc) prog;
      close_out oc

let print_header_globvar (p : formatter) (id : ident)
    (v : Ctypes.coq_type globvar) : unit =
  let name1 = Camlcoq.extern_atom id in
  if not (String.starts_with ~prefix:"g" name1) then begin
    let name2 = if v.gvar_readonly then "const " ^ name1 else name1 in
    fprintf p "extern @[<hov 2>%s" (name_cdecl name2 v.gvar_info);
    fprintf p ";@]@ @ "
  end
  else ()

let print_header_globdef (p : formatter)
    ((id, gd) : ident * ('a, Ctypes.coq_type) globdef) : unit =
  match gd with
  | Gfun _ -> ()
  | Gvar v -> print_header_globvar p id v

let print_header_globdecl (p : formatter)
    ((id, gd) : ident * ('a, Ctypes.coq_type) globdef) : unit =
  if Barocq2C.fun_is_static id then ()
  else PrintCsyntax.print_globdecl p (id, gd)

let print_inttype_aliases (oc : out_channel) : unit =
  Printf.fprintf
    oc
    "typedef int i32;\n\
     typedef unsigned int u32;\n\
     typedef long long i64;\n\
     typedef unsigned long long u64;\n\n"

let print_header (types_header : string) (hfile : string)
    (prog : Csyntax.program) : unit =
  let aux p prog =
    fprintf p "@[<v 0>";
    List.iter (PrintCsyntax.define_composite p) prog.Ctypes.prog_types;
    List.iter (print_header_globdef p) prog.Ctypes.prog_defs;
    List.iter (print_header_globdecl p) prog.Ctypes.prog_defs;
    fprintf p "@]@."
  in
  let oc = open_out hfile in
  Printf.fprintf oc "#pragma once\n\n";
  if types_header <> "" then
    Printf.fprintf oc "#include \"%s\"\n\n" types_header;
  print_inttype_aliases oc;
  aux (formatter_of_out_channel oc) prog;
  close_out oc

let export_csyntax sourcename csyntax ofile =
  let oc = open_out ofile in
  ExportCsyntax.print_program
    (Format.formatter_of_out_channel oc)
    csyntax
    sourcename;
  close_out oc
