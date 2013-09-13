{
  open Parser
  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'

rule lex = parse
  | blank+ { lex lexbuf }
  | "(*"   { comment lexbuf; lex lexbuf }
  | [' ' '\t']
  | newline     { Lexing.new_line lexbuf; lex lexbuf }
  | "start_proof"  { STARTPROOF }
  | "norm"  { NORM }
  | "conj"  { CONJ }
  | "opt"   { OPT }
  | "perm"  { PERM }
  | "split" { SPLIT }
  | "merge" { MERGE }
  | "fail1" { FAIL1 }
  | "fail2" { FAIL2 }
  | "ind"   { IND }
  | "rnd"   { RND }
  | "ow"    { OW }
  | "admit" { ADMIT }
  | "@"     { AT }
  | "("     { LPAREN }
  | ")"     { RPAREN }
  | "{"     { LBRACE }
  | "}"     { RBRACE }
  | "["     { LBRACKET }
  | "]"     { RBRACKET }
  | "^-1"   { INV }
  | "+"     { PLUS }
  | "0"     { ZERO }
  | "|"     { CONC }
  | ","     { COMMA }
  | "*"     { STAR }
  | ":"     { COLON }
  | "m_b"   { MSG }
  | eof     { EOF }
  | "->"    { TO }
  | ";"     { SEMICOLON }
  | "^"     { CARET }
  | ['0'-'9']+ as s {INT (int_of_string s)}
  | ['k']['0'-'9']* as s { TV_ID s }
  | ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']+ as s { ID s }


and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

