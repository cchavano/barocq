val destination : string option ref

val print_csyntax : string -> Csyntax.program -> unit

val print_header : string -> string -> Csyntax.program -> unit

val export_csyntax : string -> Csyntax.program -> string -> unit
