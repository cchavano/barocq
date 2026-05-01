type 'a t = {
  startpos : Lexing.position;
  endpos : Lexing.position;
  content : 'a;
}

val make : Lexing.position -> Lexing.position -> 'a -> 'a t

val apply : ('a -> 'b) -> 'a t -> 'b t

val to_string : 'a t -> string
