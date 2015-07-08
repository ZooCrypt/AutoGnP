{
  open Parser
  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")
  let unterminated_string () =
    raise (Error "unterminated string")

  let keyword_table = Hashtbl.create 53
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      [ "split_ineq", RSPLIT_INEQ
      ; "permutation", PERMUTATION (* test *)
      ; "case_ev", RCASE_EV
      ; "adversary", ADVERSARY
      ; "admit", ADMIT
      ; "last", LAST
      ; "qed", QED
      ; "restart", RESTART
      ; "back", BACK
      ; "oracle",ORACLE
      ; "operator", OPERATOR
      ; "assumption", ASSUMPTION
      ; "assumption_decisional", ASSUMPTION_DECISIONAL
      ; "assumption_computational", ASSUMPTION_COMPUTATIONAL
      ; "random", RANDOM
      ; "bilinear", BILINEAR
      ; "map", MAP
      ; "succ", SUCC
      ; "adv", ADV
      ; "bound_dist", BOUNDDIST
      ; "bound_succ", BOUNDSUCC
      ; "bound_adv", BOUNDADV
      ; "print_goals", PRINTGOALS
      ; "print_goal", PRINTGOAL
      ; "print_proof", PRINTPROOF
      ; "print_debug", PRINTDEBUG
      ; "print_games", PRINTGAMES
      ; "print_game", PRINTGAME
      ; "norm_unknown", RNORM_UNKNOWN
      ; "norm_solve", RNORM_SOLVE
      ; "norm", RNORM
      ; "add_test", RADD_TEST
      ; "guard", RGUARD
      ; "guess", RGUESS
      ; "find", RFIND
      ; "hybrid", RHYBRID
      ; "remove_ev", RREMOVE_EV
      ; "dist_sym", RDIST_SYM
      ; "dist_eq", RDIST_EQ
      ; "norm_nounfold", RNORM_NOUNFOLD
      ; "abstract" , RLET_ABSTRACT
      ; "unfold" , RLET_UNFOLD
      ; "subst", RSUBST
      ; "inf", INFTHEO
      ; "ppt", PPT
      ; "rename", RRENAME
      ; "assert", ASSERT
      ; "rewrite_oracle" , RREWRITE_ORACLE
      ; "rewrite_ev", RREWRITE_EV
      ; "crush", RCRUSH
      ; "deduce", DEDUCE
      ; "field_exprs", LISTFE
      ; "bycrush", BYCRUSH
      ; "simp", RSIMP
      ; "bysimp", BYSIMP
      ; "split_ev", RSPLIT_EV
      ; "false_ev", RFALSE_EV
      ; "with" , WITH
      ; "except", REXCEPT
      ; "except_oracle", REXCEPT_ORACLE
      ; "rnd", RRND
      ; "rnd_exp", RRND_EXP
      ; "swap", RSWAP
      ; "swap_main", RSWAP_MAIN
      ; "conv", RCONV
      ; "insert", RINSERT
      ; "trans", RTRANS
      ; "indep", RINDEP
      ; "rnd_oracle", RRND_ORACLE
      ; "bad1", RBAD1
      ; "bad2", RBAD2
      ; "undo_back", UNDOBACK
      ; "ctxt_ev", RCTXT_EV
      ; "extract", EXTRACT
      ; "return", RETURN
      ; "forall", FORALL
      ; "exists", EXISTS
      ; "in",     IN
      ]
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'

rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | "(**"    { comment lexbuf; lex lexbuf }
  | "\"" { STRING (Buffer.contents (string (Buffer.create 0) lexbuf)) }
  | [' ' '\t']
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | "("     { LPAREN }
  | ")"     { RPAREN }
  | "{"     { LCBRACE }
  | "}"     { RCBRACE }
  | "+"     { PLUS }
  | "++"    { XOR }
  | "-"     { MINUS }
  | "*"     { STAR }
  | "!"     { EXCL }
  | "Fq"    { TFQ }
  | "not"   { NOT }
  | "log"   { LOG }
  | "true"  { TRUE }
  | "false" { FALSE }
  | "trans*" { RTRANSSTAR }
(*  | "in"    { IN }
    | "Log"   { QUERIES } *)
  | "let"   { LET }
  | "R:" { INRIGHT }
  | "LR:"  { INBOTH }
  | "abstract*"  { RLET_ABSTRACT_DEDUCE }
  | "L_"
    (['A'-'Z']
     ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']* as s)
    { LIST (s) }
  | "BS_"(['a'-'z']['a'-'z' '0'-'9']* as s) { TBS(s) }
  | "0_"(['a'-'z']['0'-'9']* as s) { ZBS(s) }
  | "Bool" { TBOOL }
  | "g" { GEN("") }
  | "g_"(['a'-'z''0'-'9']* as s) { GEN(s) }
  | "G" { TG("") }
  | "G_"(['a'-'z''0'-'9']* as s) { TG(s) }
  | ((['a'-'z' 'A'-'Z' ]
	['a'-'z' 'A'-'Z' '\'' '0'-'9']* ) as s)"_inv" (* Parsing 'f_inv'-like patterns *)
      { try Hashtbl.find keyword_table (s ^ "_inv")
      with Not_found -> F_INV s }
  | "GetPK_"((['a'-'z' 'A'-'Z' ]
		['a'-'z' 'A'-'Z' '\'' '0'-'9']* ) as s) {GETPK s}
  | "GetSK_"((['a'-'z' 'A'-'Z' ]
	    ['a'-'z' 'A'-'Z' '\'' '0'-'9']* ) as s) {GETSK s}	 
  | "KeyPair_"((['a'-'z' 'A'-'Z' ]
		 ['a'-'z' 'A'-'Z' '\'' '0'-'9']* ) as s) {KEYPAIR s}	 
  | "PKey_"((['a'-'z' 'A'-'Z' ]
		 ['a'-'z' 'A'-'Z' '\'' '0'-'9']* ) as s) {PKEY s}	 
  | "SKey_"((['a'-'z' 'A'-'Z' ]
		 ['a'-'z' 'A'-'Z' '\'' '0'-'9']* ) as s) {SKEY s}
  (*  (((['a'-'z'])(['a'-'z''0'-'9']* )) as s)"_inv" { F_INV(s) } (*Test *) *)
  | ['0'-'9']['0'-'9']* as s { NAT(int_of_string(s)) }
  | ['a'-'z' 'A'-'Z' ]
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']* as s
    { try Hashtbl.find keyword_table s
      with Not_found -> ID s }
  | ":"     { COLON }
  | ";"     { SEMICOLON }
  | "?"     { QUESTION }
  | ","     { COMMA }
  | "^"     { CARET }
  | "/"     { SLASH }
  | "//"    { SLASH2 }
  | "/="    { SLASHEQ }
  | "//="   { SLASH2EQ }
  | "///="  { SLASH3EQ }
  | "/\\"   { LAND }
  | "<-"    { LEFTARROW }
  | "<>"    { NEQ }
  | "<-$"   { SAMP }
  | "\\"    { BACKSLASH }
  | "#"     { SHARP }
  | "`"     { BACKTICK }
  | "["     { LBRACK }
  | "]"     { RBRACK }
  | "="     { EQUAL }
  | "->"    { TO }
  | "<"     { LESS }
  | ">"     { GREATER }
  | "."     { DOT }
  | "_"     { UNDERSCORE }


and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

and string buf = parse
  | "\""          { buf }
  | "\\n"         { Buffer.add_char buf '\n'; string buf lexbuf }
  | "\\r"         { Buffer.add_char buf '\r'; string buf lexbuf }
  | "\\" (_ as c) { Buffer.add_char buf c   ; string buf lexbuf }
  | newline       { Buffer.add_string buf (Lexing.lexeme lexbuf); string buf lexbuf }
  | _ as c        { Buffer.add_char buf c   ; string buf lexbuf }

  | eof           { unterminated_string () }
