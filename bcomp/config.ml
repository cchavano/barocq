(** TODO - generate from Makefile.config *)
let run_command cmd =
  let buf = Unix.open_process_in cmd in
  let result = Stdlib.input_line buf in
  ignore (Unix.close_process_in buf);
  result

let install_dev_dir =
  let opam_switch = run_command "opam var lib" in
  Filename.concat opam_switch "coq/user-contrib/BarocqComp"
