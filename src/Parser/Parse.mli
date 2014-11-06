open ParserTypes

(*s Wrapper functions for parser with error handling. *)

val ty : string -> parse_ty

val expr : string -> parse_expr

val odef : string -> odef

val gdef : string -> gdef

val instruction : string -> instr

val theory : string -> theory
