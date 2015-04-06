(*s Wrapper functions for parser with error handling. *)

(*i*)
module S = String
module PU = ParserUtil
(*i*)

(** Convert lexer and parser errors to ParseError exception *)
let wrap_error f s =
  let sbuf = Lexing.from_string s in
  try
    f sbuf
  with
  | Lexer.Error msg ->
      raise (PU.ParseError (Printf.sprintf "%s%!" msg))
  | Parser.Error ->
      let start = Lexing.lexeme_start sbuf in
      let err = Printf.sprintf
                  "Syntax error at offset %d (length %d): parsed ``%s'',\nerror at ``%s''"
                  start
                  (S.length s)
                  (if start >= S.length s then s  else (S.sub s 0 start))
                  (if start >= S.length s then "" else (S.sub s start (S.length s - start)))
      in
      print_endline err;
      raise (PU.ParseError err)
  | _ -> raise (PU.ParseError "Unknown error while lexing/parsing.")

(** Parse type declaration. *)
let ty = wrap_error (Parser.typ Lexer.lex)

(** Parse expression. *)
let expr = wrap_error (Parser.expr Lexer.lex)

(** Parse oracle definition. *)
let odef = wrap_error (Parser.odef Lexer.lex)

(** Parse game definition. *)
let gdef = wrap_error (Parser.gdef Lexer.lex)


(** Parse instruction definition. *)
let instruction = wrap_error (Parser.instruction Lexer.lex)

(** Parse theory definition. *)
let theory = wrap_error (Parser.theory Lexer.lex)
