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
  | "("     { LPAREN }
  | ")"     { RPAREN }
  | "+"     { PLUS }
  | "-"     { MINUS }  
  | "*"     { STAR }
  | eof     { EOF }
  | "_"     { UNDERSCORE }  
  | "BS"    { TBS }
  | "Bool"  { TBOOL }
  | "G"     { TG }
  | "GT"    { TGT }
  | "Fq"    { TFQ }
  | "0"     { ZERO }
  | "not"  { NOT }
  | "true"  { TRUE }
  | "false" { FALSE }
  | ['l']['0'-'9']* as s { LV_ID s }
  | ['a'-'f' 'h'-'k' 'm'-'z']
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']*
    as s { ID s }
  | ":"     { COLON }  
  | "?"     { QUESTION }
  | "1"     { ONE }
  | "e("     { EMAP }   
  | "g"     { GEN }
  | ","     { COMMA }
  | "^"     { CARET }
  | "/"     { SLASH }  
  | "/\\"   { LAND }  
(*  | "{"     { LBRACE } *)
(*  | "}"     { RBRACE } *)
(*  | "["     { LBRACKET } *)
(*  | "]"     { RBRACKET } *)
(*  | "^-1"   { INV } *)
(*  | ":"     { COLON } *)
(*  | "->"    { TO } *)
(*  | "."     { DOT }   *)
(*  | ['0'-'9']+ as s {INT (int_of_string s)} *)    

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

