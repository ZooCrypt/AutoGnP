%{
	open ParserUtil

%}

%token EOF

/************************************************************************/
/* Tokens for types */
%token PLUS
%token <string> TV_ID /* always k<int> */
%token ZERO

%left PLUS

/************************************************************************/
/* Tokens for expressions */
%token <string> ID
%token MSG
%token STAR

%token CONC
%left CONC

%token COMMA
%token INV
%token CARET

%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET

/************************************************************************/
/* Tokens for commands */
%token AT
%token TO
%token <int> INT
%token SEMICOLON
%token COLON

%token STARTPROOF
%token ADMIT
%token NORM
%token CONJ
%token OPT
%token PERM
%token SPLIT
%token MERGE
%token FAIL1
%token FAIL2
%token IND
%token RND
%token OW

/************************************************************************/
/* Production types */

%type <ParserUtil.ity> typ

%type <ParserUtil.iexpr> expr

%type <(string * ParserUtil.ity * ParserUtil.ity) list> op_decls
%type <(string * ParserUtil.ity) list> const_decls

%type <int list> intlist

%type <(ParserUtil.cmd * ParserUtil.cloc) list> lcmds

%type <ParserUtil.descr> scheme_descr

/************************************************************************/
/* Start productions */
%start typ

%start expr

%start op_decls

%start const_decls

%start scheme_descr

%start lcmds

%%

/************************************************************************/
/* Types */

typ :
| t = typ0 EOF { t }

typ0 :
| s = TV_ID { [s] }
| ZERO { [] }
| t1 = typ0 PLUS t2 = typ0 { t1@t2 }

/************************************************************************/
/* Expressions */

expr :
| e = expr0 EOF { e }

expr0 :
| e = expr1 { e }
| e1 = expr0 CONC e2 = expr0 { IApp [e1; e2] }

expr1 :
| e1 = expr1 PLUS e2 = expr1 { IXor(e1, e2) }
| LPAREN e = expr0 RPAREN {e}
| s = ID LPAREN e=expr0 RPAREN { IFun(s, e) }
| s = ID INV LPAREN e=expr0 RPAREN { IPinv(s,e) }
| s = ID { IR s }
| ZERO CARET tv = TV_ID { IZ [tv] }
| ZERO CARET LBRACE t = typ0 RBRACE { IZ t }
| MSG   { IMsg }
| STAR  { IStar }
| LBRACKET e = expr0 RBRACKET LBRACE t1 = typ0 COMMA t2 = typ0 RBRACE
    { IProj((t1,t2),e) }

/************************************************************************/
/* Commands and scheme descriptions */

intlist:
| ZERO { [0] }
| i = INT { [i] }
| ZERO COMMA is = intlist { 0::is }
| i = INT COMMA is = intlist { i::is }


idlist:
| LPAREN RPAREN { [] }
| LPAREN is = idlist0 RPAREN { is }

idlist0:
| id = ID { [id] }
| id = ID COMMA ids = idlist { id::ids }


const_decls:
| EOF { [] }
| cds = const_decls0 EOF { cds }

const_decls0 :
| c = const_decl { [c] }
| c = const_decl SEMICOLON cs = const_decls0 { c::cs }

const_decl :
| s = ID COLON t = typ0 { (s,t) }


op_decls:
| EOF { [] }
| ods = op_decls0 EOF { ods }

op_decls0 :
| o = op_decl { [o] }
| o = op_decl SEMICOLON os = op_decls0 { o::os }

op_decl :
| s = ID COLON t1 = typ0 TO t2 = typ0 { (s,t1,t2) }

scheme_descr :
| STARTPROOF LPAREN t = typ0 RPAREN LPAREN hd = op_decls0 RPAREN LPAREN fd = const_decls0 RPAREN
             LPAREN rd = const_decls0 RPAREN LPAREN e = expr0 RPAREN EOF
  { Descr(t , hd, fd , rd, e) }

lcmds:
| lcs = lcmds0 EOF { lcs }
| lcs = lcmds0 SEMICOLON EOF { lcs }

lcmds0:
| LPAREN lcs = lcmds0 RPAREN AT l = loc { List.map (fun (x,_) -> (x,l)) lcs }
| c = lcmd {[c]}
| c = lcmd SEMICOLON {[c]}
| c = lcmd SEMICOLON cs = lcmds0 {c::cs}

lcmd:
| c = cmd0 AT l = loc { (c,l) }
| c = cmd0 { (c, LAdmit(0)) }

loc:
| LPAREN RPAREN { LPath([]) }
| LPAREN il = intlist RPAREN { LPath(il) }
| ZERO { LAdmit(0) }
| i = INT { LAdmit(i) }

cmd0:
| NORM { CNorm }
| CONJ i = INT { CConj i }
| CONJ ZERO { CConj 0 }
| OPT   LPAREN r = ID RPAREN LPAREN e = expr0 RPAREN { COpt(r,e) }
| PERM  LPAREN r = ID RPAREN LPAREN f = ID RPAREN { CPerm(r,f) }
| SPLIT LPAREN r = ID RPAREN LPAREN t1 = typ0 RPAREN LPAREN r1 = ID RPAREN LPAREN r2 = ID RPAREN { CSplit(r,t1,r1,r2) }
| MERGE LPAREN r1 = ID RPAREN LPAREN r2 = ID RPAREN LPAREN r3 = ID RPAREN { CMerge(r1,r2,r3) }
| FAIL1 LPAREN h = ID RPAREN LPAREN r = ID RPAREN { CFail1(h,r) }
| FAIL2 LPAREN h = ID RPAREN LPAREN r = ID RPAREN { CFail2(h,r) }
| IND { CInd }
| RND LPAREN r = ID RPAREN LPAREN c = expr0 RPAREN { CRnd(r, c) }
| OW LPAREN f = ID RPAREN
     LPAREN r_finput = ID RPAREN
     LPAREN tdrop = typ0 RPAREN
     LPAREN ttake = typ0 RPAREN
     r_known = idlist
     LPAREN c_cipher = expr0 RPAREN
     LPAREN c_input = expr0 RPAREN
    { COw(f, r_finput, tdrop, ttake, r_known, c_cipher, c_input) }
| ADMIT { CAdmit }

