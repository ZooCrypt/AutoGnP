(** Wrapper functions for parser with error handling. *)

val ty : string -> ParserUtil.parse_ty

val expr : string -> ParserUtil.parse_expr

val odef : string -> ParserUtil.odef

val gdef : string -> ParserUtil.gdef

val instruction : string -> ParserUtil.instr

val theory : string -> ParserUtil.theory
