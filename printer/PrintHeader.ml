open Format
open PrintCsyntax
open AST

let print_globvar p id v =
  let name1 = Camlcoq.extern_atom id in
  if not (String.starts_with ~prefix:"g" name1) then begin
    let name2 = if v.gvar_readonly then "const " ^ name1 else name1 in
    fprintf p "extern @[<hov 2>%s" (name_cdecl name2 v.gvar_info);
    fprintf p ";@]@ @ "
  end
  else ()

let print_globdef p (id, gd) =
  match gd with
  | Gfun _ -> ()
  | Gvar v -> print_globvar p id v

let print file prog =
  let aux p prog =
    fprintf p "@[<v 0>";
    List.iter (PrintCsyntax.define_composite p) prog.Ctypes.prog_types;
    List.iter (print_globdef p) prog.Ctypes.prog_defs;
    List.iter (PrintClight.print_globdecl p) prog.Ctypes.prog_defs;
    fprintf p "@]@."
  in
  let oc = open_out file in
  Printf.fprintf oc "#pragma once\n\n";
  aux (formatter_of_out_channel oc) prog;
  close_out oc
