{ type sing_tokens = INT of int | VAR of int | PLUS | TIMES | POW | DIV | OPEN | CLOSE | EOF | MINUS }
rule lex = parse
  | [' ' '\n' '\t'] { lex lexbuf }
  | ['0'-'9']+ as s { INT(int_of_string s) }
  | 'x'['0'-'9']+ as s { VAR(int_of_string (String.sub s 1 (String.length s -1))) }
  | '+'             { PLUS }
  | '-'             { MINUS }
  | '*'             { TIMES }
  | '^'             { POW }
  | '/'             { DIV }
  | '('             { OPEN }
  | ')'             { CLOSE }
  | eof             { EOF }
