{
  open Parser
  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'

rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | [' ' '\t']
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | "("     { LPAREN }
  | ")"     { RPAREN }
  | "+"     { PLUS }
  | "++"    { XOR }
  | "-"     { MINUS }  
  | "*"     { STAR }
  | "BS_"(['a'-'z']['0'-'9']* as s) { TBS(s) }
  | "0_"(['a'-'z']['0'-'9']* as s) { ZBS(s) }
  | "Bool" { TBOOL }
  | "g" { GEN("") }
  | "g_"(['a'-'z']['0'-'9']* as s) { GEN(s) }
  | "G" { TG("") }
  | "G_"(['a'-'z']['0'-'9']* as s) { TG(s) } 
  | "Fq"    { TFQ }
  | "not"   { NOT }
  | "log"   { LOG }
  | "true"  { TRUE }
  | "false" { FALSE }
  | "let"   { LET }
  | "adversary" { ADVERSARY }
  | "oracle" { ORACLE }
  | "assumption" { ASSUMPTION }
  | "random" { RANDOM }
  | "bilinear" { BILINEAR }
  | "map" { MAP }
  | "prove" { PROVE }
  | "print_goals" { PRINTGOALS }
  | "rnorm_unknown" { RNORM_UNKNOWN }
  | "rnorm" { RNORM }
  | "radd_test" { RADD_TEST }
  | "rnorm_nounfold" { RNORM_NOUNFOLD }  
  | "rlet_abstract"  { RLET_ABSTRACT }
  | "rlet_unfold"  { RLET_UNFOLD }  
  | "with"  { WITH }
  | "rexcept" { REXCEPT }
  | "rexcept_oracle" { REXCEPT_ORACLE }  
  | "rrandom" { RRANDOM }
  | "rswap" { RSWAP }
  | "requiv" { REQUIV }
  | "rbddh" { RBDDH }
  | "rddh" { RDDH }
  | "rindep" { RINDEP }
  | "rrandom_oracle" { RRANDOM_ORACLE }
  | "rbad"           { RBAD }
  | "rctxt_ev"       { RCTXT_EV }
  | "in"    { IN }
  | "L_"    { LIST }
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

