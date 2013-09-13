(** Wrapper functions for parser with error handling. *)

module S = String

(** Parser error with explanation *)
exception ParseError of string

(** Convert lexer and parser errors to ParseError exception *)
let wrap_error f s =
  let sbuf = Lexing.from_string s in
  try
    f sbuf
  with
  | Lexer.Error msg ->
      raise (ParseError (Printf.sprintf "%s%!" msg))
  | Parser.Error ->
      let start = Lexing.lexeme_start sbuf in
      raise (ParseError (Printf.sprintf
                           "Syntax error at offset %d: parsed ``%s'', error at ``%s''"
                           (Lexing.lexeme_start sbuf)
                           (S.sub s 0 start)
                           (S.sub s start (S.length s - start))))
  | _ -> raise (ParseError "Unknown error while lexing/parsing.")

(** Parse operator declaration. *)
let op_decls = wrap_error (Parser.op_decls Lexer.lex)

(** Parse constant declaration. *)
let const_decls = wrap_error (Parser.const_decls Lexer.lex)

(** Parse type declaration. *)
let ty = wrap_error (Parser.typ Lexer.lex)

(** Parse expression. *)
let expr = wrap_error (Parser.expr Lexer.lex)

(** Parse sequence of commands. *)
let cmds = wrap_error (Parser.lcmds Lexer.lex)

(** Parse description of scheme. *)
let scheme_descr = wrap_error (Parser.scheme_descr Lexer.lex)