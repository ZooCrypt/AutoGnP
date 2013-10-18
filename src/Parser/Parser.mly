%{
	open ParserUtil

%}

%token EOF

/************************************************************************/
/* Tokens for types */
%token IN
%token TBS
%token TBOOL
%token TG
%token TGT
%token TFQ
%token STAR
%left  STAR
%token LPAREN
%token RPAREN
%token <string> LV_ID /* always k<int> */

/************************************************************************/
/* Tokens for expressions */
%token <string> ID
%token PLUS
%left PLUS
%token XOR
%left XOR

%token MINUS
%left MINUS

%token CARET

%token SLASH

%token TRUE
%token FALSE
%token NOT
%token COLON
%token QUESTION
%token LAND
%left  LAND

%token EQUAL

%token COMMA

%token GEN
%token EMAP
%token UNIT
%token LOG

/************************************************************************/
/* Tokens for games */

%token LEFTARROW
%token LET
%token SAMP
%token BACKSLASH
%token LBRACKET
%token RBRACKET
%token MID
%token SEMICOLON
%token LIST
%token WITH
%token <string> AID
%token <int> INT

/************************************************************************/
/* Tokens for theories */

%token TO
%token ADVERSARY
%token ORACLE
%token RANDOM
%token PROVE
%token DOT
%token PRINTGOALS
%token RNORM
%token RNORM_UNKNOWN
%token RRANDOM
%token RRANDOM_ORACLE
%token RSWAP
%token REQUIV
%token RBDDH
%token RDDH
%token RINDEP
%token RBAD
%token RLET_ABSTRACT
%token RCTXT_EV
/************************************************************************/
/* Production types */

%type <ParserUtil.parse_ty> typ

%type <ParserUtil.parse_expr> expr

%type <ParserUtil.lcmd> lcmd

%type <ParserUtil.odef> odef

%type <ParserUtil.gcmd> gcmd

%type <ParserUtil.gdef> gdef

%type <ParserUtil.theory> theory

/************************************************************************/
/* Start productions */
%start typ

%start expr

%start odef

%start gdef

%start theory

%%

/************************************************************************/
/* Types */

typ :
| t=typ0 EOF { t }

typ0 :
| TBS s=LV_ID { BS(s) }
| TBOOL { Bool }
| TG { G }
| TGT { GT }
| TFQ { Fq }
| UNIT { Prod([]) }
| LPAREN l = typlist0 RPAREN { Prod(l) }

typlist0 :
| t=typ0 STAR l=typlist0 { t::l }
| t=typ0 { [t] }

/************************************************************************/
/* Expressions */

/* FIXME: check operator precedence */

expr :
| e = expr0 EOF { e }

expr0 :
| e1 = expr0 IN LBRACKET e2=expr0 MID bd=hbindings RBRACKET
     { ElemH(e1,e2,bd) }
| e1 = expr1 EQUAL e2 = expr1 { Eq(e1,e2) }
| e1 = expr1 QUESTION e2 = expr1 COLON e3 = expr1 { Ifte(e1, e2, e3) }
| e = expr1 { e }

expr1 :
| e1 = expr1 PLUS e2 = expr1 { Plus(e1, e2) }
| e1 = expr1 XOR e2 = expr1  { Xor (e1, e2) }
| e = expr2 { e }

expr2:
| e1 = expr2 MINUS e2 = expr2 { Minus(e1, e2) }
| e = expr3 { e }

expr3:
| e1 = expr4 SLASH e2 = expr4 { Div(e1, e2) }
| e = expr4 { e }

expr4 :
| e1 = expr4 STAR e2 = expr4 { Mult(e1,e2) }
| e1 = expr4 LAND e2 = expr4 { Land(e1,e2) }
| e = expr5 { e }

expr5:
| e1 = expr6 CARET e2 = expr6 { Exp(e1, e2) }
| e  = expr6 { e }

exprlist0 :
| e = expr0 { [e] }
| e = expr0 COMMA l = exprlist0 { e::l }

expr6 :
| s = ID { V(s) }
| UNIT   { Tuple [] }
| i = INT
  { Cnst( if i = 1 then Expr.FOne
          else if i = 0 then Expr.FZ
          else failwith "only 0/1 allowed in expressions" ) }
| GEN    { Cnst(Expr.GGen) }
| TRUE   { Cnst(Expr.B true) }
| FALSE  { Cnst(Expr.B false) }
| s = AID LPAREN l = exprlist0 RPAREN { SApp(s,l) }
| MINUS e1 = expr6 { Opp(e1) }
| NOT e = expr6 { Not(e) }
| EMAP e1 = expr0 COMMA e2 = expr0 RPAREN { EMap(e1,e2) }
| LOG LPAREN e1 = expr0 RPAREN { Log(e1) }
| LPAREN e = expr0 RPAREN {e}
| LPAREN e = expr0 COMMA l = exprlist0 RPAREN { Tuple(e::l) }
;

hbinding:
| x=ID LEFTARROW LIST h=AID {x,h}
;
hbindings:
| b=hbinding { [b] }
| b=hbinding COMMA bs= hbindings { b::bs }
;
/************************************************************************/
/* List comprehensions */
/* FIXME: handle shift-reduce conflict */

idlist :
| UNIT { [] }
| LPAREN is = idlist0 RPAREN { is }
| is = idlist0 { is }

idlist0 :
| i = ID { [i] }
| i = ID COMMA is = idlist0 { i :: is }

lcmd :
| LET i = ID EQUAL e = expr0 { LLet(i,e) }
| is = idlist LEFTARROW LIST hsym = ID { LBind(is,hsym) }
| i = ID SAMP t = typ0 BACKSLASH es = exprlist0 { LSamp(i,t,es) }
| i = ID SAMP t = typ0                          { LSamp(i,t,[]) }
| e = expr0 { LGuard(e) }

lcmdlist :
| c = lcmd { [c] }
| c = lcmd COMMA cs = lcmdlist { c::cs }

lcomp :
| LBRACKET e = expr0 MID cmds = lcmdlist RBRACKET { (cmds, e) }

odef :
| oname = AID UNIT EQUAL lc = lcomp { (oname,[],lc) }
| oname = AID LPAREN args = idlist RPAREN EQUAL lc = lcomp { (oname, args, lc) }

/************************************************************************/
/* games */

odeflist :
| od = odef { [od] }
| od = odef COMMA ods = odeflist { od::ods }

mexprlist0 :
| e = expr0 COMMA es = exprlist0 { Tuple(e::es) }
| e = expr0  { e }

gcmd :
| LET i = ID EQUAL e = expr0 { GLet(i,e) }
| is = idlist LEFTARROW asym = AID LPAREN e = mexprlist0 RPAREN WITH os = odeflist { GCall(is,asym,e,os) }
| is = idlist LEFTARROW asym = AID LPAREN e = mexprlist0 RPAREN                    { GCall(is,asym,e,[]) }
| is = idlist LEFTARROW asym = AID UNIT WITH os = odeflist { GCall(is,asym,Tuple [],os) }
| is = idlist LEFTARROW asym = AID UNIT                    { GCall(is,asym,Tuple [],[]) }
| i = ID SAMP t = typ0 BACKSLASH es = exprlist0 { GSamp(i,t,es) }
| i = ID SAMP t = typ0                          { GSamp(i,t,[]) }

gcmdlist0 :
| c = gcmd { [c] }
| c = gcmd SEMICOLON cs = gcmdlist0 { c::cs }

gdef0 :
| cs = gcmdlist0 { cs }

gdef :
| gdef0 EOF { [] }

/************************************************************************/
/* instructions and theory */

int:
| i=INT {i}
| MINUS i=INT {-i}
;

event:
| COLON e = expr0 { e }
;
instr :
| ADVERSARY i = AID  COLON t1 = typ0 TO t2 = typ0 DOT { ADecl(i,t1,t2) }
| ORACLE    i = AID  COLON t1 = typ0 TO t2 = typ0 DOT { ODecl(i,t1,t2) }
| RANDOM ORACLE i = AID COLON t1 = typ0 TO t2 = typ0 DOT { RODecl(i,t1,t2) }
| PROVE  LBRACKET g = gdef0 RBRACKET e=event DOT { Judgment(g,e) }
| PRINTGOALS COLON i = ID DOT { PrintGoals(i) }
| PRINTGOALS DOT { PrintGoals("") }
| RNORM DOT { Apply(Rnorm) }
| RNORM_UNKNOWN DOT { Apply(Rnorm_unknown([])) }
| RNORM_UNKNOWN is = idlist DOT { Apply(Rnorm_unknown(is)) }
| RINDEP DOT { Apply(Rindep) }
| RSWAP i = INT j =int DOT { Apply(Rswap(i-1,j)) }
| RBDDH s = ID DOT { Apply(Rbddh(s)) }
| RDDH s = ID DOT { Apply(Rddh(s)) }
| REQUIV LBRACKET gd = gdef0 RBRACKET e=event? DOT { Apply(Requiv(gd,e)) }
| RLET_ABSTRACT i = INT i1 = ID e1 = expr0 DOT { Apply(Rlet_abstract(i-1,i1,e1)) }
| RRANDOM i = INT LPAREN i1 = ID TO e1 = expr0 RPAREN LPAREN i2 = ID TO e2 = expr0 RPAREN
          i3 = ID DOT { Apply(Rrandom(i-1,i1,e1,i2,e2,i3)) }
| RRANDOM_ORACLE LPAREN i = INT COMMA j = INT COMMA k = INT RPAREN
                 LPAREN i1 = ID TO e1 = expr0 RPAREN LPAREN i2 = ID TO e2 = expr0 RPAREN
                 i3 = ID DOT
                 { Apply(Rrandom_oracle(i-1,j-1,k-1,i1,e1,i2,e2,i3)) }
| RBAD i=INT s = ID DOT { Apply(Rbad (i-1,s)) }
| RCTXT_EV LPAREN i1 = ID TO e1 = expr0 RPAREN  DOT
   { Apply(Rctxt_ev(i1,e1)) }

theory :
| i = instr EOF { [i] }
| i = instr t = theory { i::t }
