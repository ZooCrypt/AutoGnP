{
  open Parser
  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")
  let unterminated_string () =
    raise (Error "unterminated string")

}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'

rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | "\"" { STRING (Buffer.contents (string (Buffer.create 0) lexbuf)) }
  | [' ' '\t']
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | "("     { LPAREN }
  | ")"     { RPAREN }
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
  | "in"    { IN }
  | "Log"   { QUERIES }
  | "let"   { LET }
  | "undo_back"  { UNDOBACK }
  | "undo_back!"  { UNDOBACK_EXCL }
  | "adversary" { ADVERSARY }
  | "admit" { ADMIT }
  | "last" { LAST }
  | "qed" { QED }
  | "back" { BACK }
  | "oracle" { ORACLE }
  | "operator" { OPERATOR }
  | "assumption" { ASSUMPTION }
  | "assumption_decisional" { ASSUMPTION_DECISIONAL }
  | "assumption_computational" { ASSUMPTION_COMPUTATIONAL }
  | "random" { RANDOM }
  | "bilinear" { BILINEAR }
  | "map" { MAP }
  | "succ" { SUCC }
  | "adv" { ADV }
  | "bound_dist" { BOUNDDIST }
  | "bound_succ" { BOUNDSUCC }
  | "bound_adv" { BOUNDADV }
  | "print_goals" { PRINTGOALS }
  | "print_goal" { PRINTGOAL }
  | "print_proof" { PRINTPROOF }
  | "print_proof!" { PRINTPROOF_EX }
  | "print_debug" { PRINTDEBUG }
  | "print_games" { PRINTGAMES }
  | "print_game" { PRINTGAME }

  | "norm_unknown" { RNORM_UNKNOWN }
  | "norm_solve" { RNORM_SOLVE }
  | "norm" { RNORM }
  | "add_test" { RADD_TEST }
  | "case_ev" { RCASE_EV }
  | "hybrid" { RHYBRID }
  | "remove_ev" { RREMOVE_EV }
  | "dist_sym" { RDIST_SYM }
  | "dist_eq" { RDIST_EQ }
  | "norm_nounfold" { RNORM_NOUNFOLD }
  | "abstract*"  { RLET_ABSTRACT_DEDUCE }
  | "abstract"  { RLET_ABSTRACT }
  | "unfold"  { RLET_UNFOLD }
  | "subst" { RSUBST }
  | "inf" { INFTHEORETIC }
  | "ppt" { PPT }
  | "rename" { RRENAME }
  | "assert" { ASSERT }
  | "rewrite_oracle"  { RREWRITE_ORACLE }
  | "rewrite_ev" { RREWRITE_EV }
  | "crush" { RCRUSH }
  | "deduce" { DEDUCE }
  | "field_exprs" { LISTFE }
  | "bycrush" { BYCRUSH }
  | "simp" { RSIMP }
  | "bysimp" { BYSIMP }
  | "split_ev" { RSPLIT_EV }
  | "false_ev" { RFALSE_EV }
  | "with"  { WITH }
  | "except" { REXCEPT }
  | "except_oracle" { REXCEPT_ORACLE }
  | "rnd" { RRND }
  | "swap" { RSWAP }
  | "swap_main" { RSWAP_MAIN }
  | "conv" { RCONV }
  | "trans" { RTRANS }
  | "indep" { RINDEP }
  | "rnd_oracle" { RRND_ORACLE }
  | "bad"           { RBAD }
  | "ctxt_ev"       { RCTXT_EV }
  | "exists"    { EXISTS }
  | "extract"   { EXTRACT }
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
  | ['0'-'9']['0'-'9']* as s { NAT(int_of_string(s)) }
  | ['a'-'z' 'A'-'Z' ]
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']*
    as s { ID s }
  | ":"     { COLON }
  | ";"     { SEMICOLON }
  | "()"    { UNIT }
  | "?"     { QUESTION }
  | ","     { COMMA }
  | "^"     { CARET }
  | "/"     { SLASH }
  | "//"     { SLASH2 }
  | "/="     { SLASHEQ }
  | "//="    { SLASH2EQ }
  | "/\\"   { LAND }
  | "<-"    { LEFTARROW }
  | "<>"    { NEQ }
  | "<-$"   { SAMP }
  | "\\"     { BACKSLASH }
  | "#"     { SHARP }
  | "`"     { BACKTICK }
  | "["     { LBRACK }
  | "]"     { RBRACK }
  | "="     { EQUAL }
  | "|"     { MID }
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
