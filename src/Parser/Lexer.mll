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
  | "-"     { MINUS }  
  | "*"     { STAR }
  | "BS_"   { TBS }
  | "Bool"  { TBOOL }
  | "g"     { GEN }
  | "G"     { TG }
  | "GT"    { TGT }
  | "Fq"    { TFQ }
  | "not"   { NOT }
  | "log"   { LOG }
  | "true"  { TRUE }
  | "false" { FALSE }
  | "let"   { LET }
  | "adversary" { ADVERSARY }
  | "oracle" { ORACLE }
  | "prove" { PROVE }
  | "print_goals" { PRINTGOALS }
  | "rnorm" { RNORM }
  | "with"  { WITH }
  | "rrandom" { RRANDOM }
  | "rswap" { RSWAP }
  | "requiv" { REQUIV }
  | "rbddh" { RBDDH }
  | "rindep" { RINDEP }
  | "rrandom_oracle" { RRANDOM_ORACLE }
  | ['1'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | ['k']['0'-'9']* as s { LV_ID s }
  | ['a'-'f' 'h'-'j' 'm'-'v' 'x'-'z']
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']*
    as s { ID s }
  | ['A'-'E' 'H'-'Z']
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']*
    as s { AID s }
  | ":"     { COLON }
  | ";"     { SEMICOLON }
  | "()"    { UNIT }
  | "?"     { QUESTION }
  | "e("    { EMAP }
  | ","     { COMMA }
  | "^"     { CARET }
  | "/"     { SLASH }
  | "/\\"   { LAND }
  | "L_"    { LIST }
  | "<-"    { LEFTARROW }
  | "<-$"   { SAMP }
  | "\\"    { BACKSLASH }
  | "["     { LBRACKET }
  | "]"     { RBRACKET }
  | "="     { EQUAL }
  | "|"     { MID }
  | "->"    { TO }
  | "."     { DOT }

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

