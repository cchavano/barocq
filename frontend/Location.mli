type 'a t = {
  startpos : Lexing.position;
  endpos : Lexing.position;
  content : 'a;
}

val make : Lexing.position -> Lexing.position -> 'a -> 'a t

val to_string : 'a t -> string
