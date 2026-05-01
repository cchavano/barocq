open Lexing

type 'a t = {
  startpos : Lexing.position;
  endpos : Lexing.position;
  content : 'a;
}

let make stp edp cn = { startpos = stp; endpos = edp; content = cn }

let apply (f : 'a -> 'b) (loc : 'a t) : 'b t =
  { loc with content = f loc.content }

let from_single_pos (pos : position) : string =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  Printf.sprintf "line %d, character %d" l c

let from_interval (pos1 : position) (pos2 : position) : string =
  let l1 = pos1.pos_lnum in
  let l2 = pos2.pos_lnum in
  let lines =
    if l1 = l2 then Printf.sprintf "line %d" l1
    else Printf.sprintf "lines %d-%d" l1 l2
  in
  let c1 = pos1.pos_cnum - pos1.pos_bol + 1 in
  let c2 = pos2.pos_cnum - pos1.pos_bol in
  Printf.sprintf "%s, characters %d-%d" lines c1 c2

let to_string (loc : 'a t) : string =
  let startpos = loc.startpos in
  let endpos = loc.endpos in
  let srcloc =
    if startpos.pos_cnum = endpos.pos_cnum - 1 then from_single_pos startpos
    else from_interval startpos endpos
  in
  Printf.sprintf "File \"%s\", %s" startpos.pos_fname srcloc
