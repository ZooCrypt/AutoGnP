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
  | "let"   { LET }
  | "adversary" { ADVERSARY }
  | "admit" { ADMIT }
  | "last" { LAST }
  | "qed" { QED }
  | "back" { BACK }
  | "oracle" { ORACLE }
  | "operator" { OPERATOR }
  | "assumption_decisional" { ASSUMPTION_DECISIONAL }
  | "assumption_computational" { ASSUMPTION_COMPUTATIONAL }
  | "assumption_decisional!" { ASSUMPTION_DECISIONAL_EX }
  | "assumption_computational!" { ASSUMPTION_COMPUTATIONAL_EX }
  | "random" { RANDOM }
  | "bilinear" { BILINEAR }
  | "map" { MAP }
  | "prove" { PROVE }
  | "print_goals" { PRINTGOALS }
  | "print_goal" { PRINTGOAL }
  | "print_proof" { PRINTPROOF }
  | "print_proof!" { PRINTPROOF_EX }
  | "rnorm_unknown" { RNORM_UNKNOWN }
  | "rnorm" { RNORM }
  | "radd_test" { RADD_TEST }
  | "rcase_ev" { RCASE_EV }
  | "rremove_ev" { RREMOVE_EV }
  | "rnorm_nounfold" { RNORM_NOUNFOLD }  
  | "rlet_abstract"  { RLET_ABSTRACT }
  | "rlet_unfold"  { RLET_UNFOLD }
  | "rrewrite_oracle"  { RREWRITE_ORACLE }  
  | "rrewrite_ev" { RREWRITE_EV }
  | "crush" { RCRUSH }
  | "deduce" { DEDUCE }
  | "bycrush" { BYCRUSH }
  | "rsimp" { RSIMP }
  | "rsplit_ev" { RSPLIT_EV }
  | "rfalse_ev" { RFALSE_EV }
  | "with"  { WITH }
  | "rexcept" { REXCEPT }
  | "rexcept_oracle" { REXCEPT_ORACLE }  
  | "rrnd" { RRND }
  | "rswap" { RSWAP }
  | "rconv" { RCONV }
  | "rindep" { RINDEP }
  | "rindep!" { RINDEP_EX }
  | "rrnd_oracle" { RRND_ORACLE }
  | "rbad"           { RBAD }
  | "rctxt_ev"       { RCTXT_EV }
  | "exists"    { EXISTS }
  | "extract"   { EXTRACT }
  | "L_"
    (['A'-'Z']
     ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']* as s)
    { LIST (s) }
  | "BS_"(['a'-'z']['0'-'9']* as s) { TBS(s) }
  | "0_"(['a'-'z']['0'-'9']* as s) { ZBS(s) }
  | "Bool" { TBOOL }
  | "g" { GEN("") }
  | "g_"(['a'-'z''0'-'9']* as s) { GEN(s) }
  | "G" { TG("") }
  | "G_"(['a'-'z''0'-'9']* as s) { TG(s) } 
  | ['0'-'9']['0'-'9']* as s { NAT(int_of_string(s)) }
  | ['a'-'z']
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']*
    as s { ID s }
  | ['A'-'Z']
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']*
    as s { AID s }
  | ":"     { COLON }
  | ";"     { SEMICOLON }
  | "()"    { UNIT }
  | "?"     { QUESTION }
  | ","     { COMMA }
  | "^"     { CARET }
  | "/"     { SLASH }
  | "/\\"   { LAND }
  | "<-"    { LEFTARROW }
  | "<-$"   { SAMP }
  | "\\"    { BACKSLASH }
  | "["     { LBRACKET }
  | "]"     { RBRACKET }
  | "="     { EQUAL }
  | "|"     { MID }
  | "->"    { TO }
  | "."     { DOT }
  | "_"     { UNDERSCORE }

(*  | "{"     { LBRACE } *)
(*  | "}"     { RBRACE } *)
(*  | "^-1"   { INV } *)
(*  | ":"     { COLON } *)

(*  | "."     { DOT }   *)
(*  | ['0'-'9']+ as s {INT (int_of_string s)} *)    

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
