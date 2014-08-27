%{
  (** Parser for expressions, games, judgments, and tactic command. *)
	open ParserUtil

%}

%token EOF

/************************************************************************/
/* Tokens for types */
%token EXISTS
%token <string> TBS
%token TBOOL
%token <string> TG
%token TFQ
%token STAR
%left  STAR
%token LPAREN
%token RPAREN

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

%token <string> GEN
%token UNIT
%token LOG
%token <string> ZBS

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
%token <int> NAT

/************************************************************************/
/* Tokens for theories */

%token TO
%token ADVERSARY
%token ORACLE
%token OPERATOR
%token ASSUMPTION_DECISIONAL
%token ASSUMPTION_COMPUTATIONAL
%token RANDOM
%token BILINEAR
%token MAP
%token PROVE
%token DOT
%token PRINTGOALS
%token PRINTGOAL
%token RNORM
%token RNORM_UNKNOWN
%token RNORM_NOUNFOLD
%token RRANDOM
%token RRANDOM_ORACLE
%token RSWAP
%token REQUIV
%token RINDEP
%token RBAD
%token RCASE_EV
%token RFALSE_EV
%token RREWRITE_EV
%token RSPLIT_EV
%token RREMOVE_EV
%token RLET_ABSTRACT
%token RLET_UNFOLD
%token RCTXT_EV
%token REXCEPT
%token RADD_TEST
%token REXCEPT_ORACLE
%token RREWRITE_ORACLE
%token UNDERSCORE
%token ADMIT
%token LAST
%token EXTRACT
%token <string> STRING

/************************************************************************/
/* Production types */

%type <ParserUtil.parse_ty> typ

%type <ParserUtil.parse_expr> expr

%type <ParserUtil.lcmd> lcmd

%type <ParserUtil.odef> odef

%type <ParserUtil.gcmd> gcmd

%type <ParserUtil.gdef> gdef

%type <ParserUtil.theory> theory

%type <ParserUtil.instr> instruction

/************************************************************************/
/* Start productions */
%start typ

%start expr

%start odef

%start gdef

%start instruction

%start theory

%%

/************************************************************************/
/* Types */

typ :
| t=typ0 EOF { t }

typ0 :
| i = TBS { BS(i) }
| TBOOL { Bool }
| i = TG { G(i) }
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
| EXISTS bd=hbindings MID e1 = expr1 EQUAL e2 = expr1
     { Exists(e1,e2,bd) }
| e1 = expr0 BACKSLASH i = NAT { Proj(i,e1) }
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
| s = ID  { V(s) }
| UNIT    { Tuple [] }
| i = NAT { CFNat i }
| i = GEN { CGen(i) }
| i = ZBS { CZ(i) }
| TRUE    { CB(true) }
| FALSE   { CB(false) }
| s = AID LPAREN l = exprlist0 RPAREN { HApp(s,l) }
| s = ID LPAREN l = exprlist0 RPAREN { SApp(s,l) }
| MINUS e1 = expr6 { Opp(e1) }
| NOT e = expr6 { Not(e) }
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
| c = gcmd SEMICOLON { [c] }
| c = gcmd SEMICOLON cs = gcmdlist0 { c::cs }

gdef0 :
| cs = gcmdlist0 { cs }

gdef :
| gdef0 EOF { [] }

/************************************************************************/
/* instructions and theory */

int:
| i=NAT {i}
| MINUS i=NAT {-i}
;

event:
| COLON e = expr0 { e }
;

dir:
| LEFTARROW { Util.RightToLeft }
| TO        { Util.LeftToRight }
;

opos:
| LPAREN i = NAT COMMA j = NAT COMMA k = NAT RPAREN { (i-1,j-1,k-1) }

instr :
| ADMIT { Admit }
| LAST { Last }
| ADVERSARY i = AID  COLON t1 = typ0 TO t2 = typ0 { ADecl(i,t1,t2) }
| ORACLE    i = AID  COLON t1 = typ0 TO t2 = typ0 { ODecl(i,t1,t2) }
| RANDOM ORACLE i = AID COLON t1 = typ0 TO t2 = typ0 { RODecl(i,true,t1,t2) }
| OPERATOR i = AID COLON t1 = typ0 TO t2 = typ0 { RODecl(i,false,t1,t2) }
| BILINEAR MAP i = ID COLON g1 = TG STAR g2 = TG TO g3 = TG { EMDecl(i,g1,g2,g3) }
| ASSUMPTION_DECISIONAL i = ID LBRACKET g0 = gdef0 RBRACKET LBRACKET g1 = gdef0 RBRACKET
   p=ID*
    { AssmDec(i,g0,g1,p) }
| ASSUMPTION_COMPUTATIONAL i1 = ID LBRACKET g = gdef0 RBRACKET LPAREN i2 = ID COLON t = typ0 TO e = expr0 RPAREN p=ID*
    { AssmComp(i1,g,i2,t,e,p) }
| PROVE  LBRACKET g = gdef0 RBRACKET e=event { Judgment(g,e) }
| PRINTGOALS COLON i = ID { PrintGoals(i) }
| PRINTGOAL COLON i = ID { PrintGoal(i) }
| PRINTGOALS { PrintGoals("") }
| RNORM { Apply(Rnorm) }
| RNORM_NOUNFOLD { Apply(Rnorm_nounfold) }
| RNORM_UNKNOWN is = ID* { Apply(Rnorm_unknown(is)) }
| RINDEP { Apply(Rindep) }
| RSWAP i = NAT j =int { Apply(Rswap(i-1,j)) }
| RSWAP op = opos j =int { Apply(Rswap_oracle(op,j)) }
| ASSUMPTION_DECISIONAL d=dir s=ID xs=ID* { Apply (Rassm_decisional(d,s,xs))}
| ASSUMPTION_COMPUTATIONAL s=ID e = expr0 { Apply (Rassm_computational(s,e))}
| REQUIV LBRACKET gd = gdef0 RBRACKET e=event? { Apply(Requiv(gd,e)) }
| RLET_ABSTRACT i = NAT i1 = ID e1 = expr0 { Apply(Rlet_abstract(i-1,i1,e1)) }
| RLET_UNFOLD i = NAT { Apply(Rlet_unfold(i-1)) }
| RADD_TEST op = opos e = expr0 asym = AID fvs = ID* { Apply(Radd_test(op,e,asym,fvs)) }
| REXCEPT i = NAT es = expr0* { Apply(Rexcept(i-1,es)) }
| REXCEPT_ORACLE op = opos es = expr0* { Apply(Rexcept_oracle(op,es)) }
| RRANDOM i = NAT LPAREN i1 = ID TO e1 = expr0 RPAREN
                  LPAREN i2 = ID TO e2 = expr0 RPAREN
                  i3 = ID { Apply(Rrandom(i-1,Some(i1,e1),Some(i2,e2),i3)) }
| RRANDOM i = NAT UNDERSCORE
                  LPAREN i2 = ID TO e2 = expr0 RPAREN
                  i3 = ID { Apply(Rrandom(i-1,None,Some(i2,e2),i3)) }
| RRANDOM i = NAT UNDERSCORE
                  UNDERSCORE
                  i3 = ID { Apply(Rrandom(i-1,None,None,i3)) }
| RRANDOM_ORACLE op = opos
                 LPAREN i1 = ID TO e1 = expr0 RPAREN
                 LPAREN i2 = ID TO e2 = expr0 RPAREN
                 i3 = ID
                 { Apply(Rrandom_oracle(op,Some(i1,e1),i2,e2,i3)) }
| RRANDOM_ORACLE op = opos
                 UNDERSCORE
                 LPAREN i2 = ID TO e2 = expr0 RPAREN
                 i3 = ID
                 { Apply(Rrandom_oracle(op,None,i2,e2,i3)) }
| RBAD i=NAT s = ID { Apply(Rbad (i-1,s)) }
| RCTXT_EV LPAREN i1 = ID TO e1 = expr0 RPAREN j = NAT
   { Apply(Rctxt_ev(i1,e1,j - 1)) }
| RREMOVE_EV i = int
   { Apply(Rremove_ev([i - 1])) }
| RSPLIT_EV i = int
   { Apply(Rsplit_ev(i - 1)) }
| RCASE_EV e = expr0
   { Apply(Rcase_ev(e)) }
| RCTXT_EV LPAREN i1 = ID TO e1 = expr0 RPAREN
   { Apply(Rctxt_ev(i1,e1,0)) }
| RFALSE_EV {Apply(Rfalse_ev)}
| RREWRITE_ORACLE op = opos d = dir { Apply(Rrewrite_oracle(op,d)) }
| RREWRITE_EV i = int d = dir { Apply(Rrewrite_ev(i - 1,d)) }
| EXTRACT s=STRING { Extract s }

instruction:
| i = instr DOT EOF { i }

theory :
| i = instr DOT EOF { [i] }
| i = instr DOT t = theory { i::t }
