%{
  (** Parser for expressions, games, judgments, and tactic command. *)
  open ParserUtil
  open Util

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
%token EXCL
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
%token NEQ

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
%token <string> LIST
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
%token ASSUMPTION_DECISIONAL_EX
%token ASSUMPTION_COMPUTATIONAL_EX
%token RINDEP_EX
%token RANDOM
%token BILINEAR
%token MAP
%token PROVE
%token DOT
%token PRINTGOALS
%token PRINTGOAL
%token PRINTPROOF
%token PRINTPROOF_EX
%token PRINTDEBUG
%token RNORM
%token RNORM_UNKNOWN
%token RNORM_SOLVE
%token RNORM_NOUNFOLD
%token RRND
%token RRND_ORACLE
%token RSWAP
%token RCONV
%token RINDEP
%token RCRUSH
%token BYCRUSH
%token RSIMP  
%token RBAD
%token RCASE_EV
%token RFALSE_EV
%token RREWRITE_EV
%token RSPLIT_EV
%token RREMOVE_EV
%token RLET_ABSTRACT
%token RLET_UNFOLD
%token RSUBST
%token RCTXT_EV
%token REXCEPT
%token RADD_TEST
%token REXCEPT_ORACLE
%token RREWRITE_ORACLE
%token UNDERSCORE
%token ADMIT
%token LAST
%token BACK
%token UNDOBACK
%token UNDOBACK_EXCL
%token QED
%token EXTRACT
%token SETUNSAFE
%token UNSETUNSAFE
%token DEDUCE
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
| EXISTS bd=hbindings COLON e1 = expr1 EQUAL e2 = expr1
     { Exists(e1,e2,bd) }
| e1 = expr0 BACKSLASH i = NAT { Proj(i,e1) }
| e1 = expr1 EQUAL e2 = expr1 { Eq(e1,e2) }
| e1 = expr1 NEQ e2 = expr1 { Not(Eq(e1,e2)) }
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
| x=ID LEFTARROW h = LIST {x,h}
;
hbindings:
| hbs=separated_nonempty_list(COMMA,hbinding) { hbs }

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
| is = idlist LEFTARROW hsym = LIST { LBind(is,hsym) }
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

range:
| i = NAT MINUS j = NAT { (i - 1,j - 1) }
;

ranges:
| LPAREN rs = separated_nonempty_list(COMMA,range) RPAREN {rs} 
;

dir:
| LEFTARROW { Util.RightToLeft }
| TO        { Util.LeftToRight }
;

opos:
| LPAREN i = NAT COMMA j = NAT COMMA k = NAT RPAREN { (i-1,j-1,k-1) }

%public uoption(X):
| UNDERSCORE { None }
| x = X { Some x }

ctx :
| LPAREN i = ID TO e = expr0 RPAREN { (i,e) }

symmetric_class:
| LBRACKET vs = separated_nonempty_list(COMMA,ID) RBRACKET { vs }

symmetric_vars:
| LPAREN symclass=symmetric_class* RPAREN {symclass}

instr :
| ADMIT { Admit }
| LAST { Last }
| BACK { Back }
| UNDOBACK { UndoBack(false) }
| UNDOBACK_EXCL { UndoBack(true) }
| QED { Qed }
| ADVERSARY i = AID  COLON t1 = typ0 TO t2 = typ0 { ADecl(i,t1,t2) }
| ORACLE    i = AID  COLON t1 = typ0 TO t2 = typ0 { ODecl(i,t1,t2) }
| RANDOM ORACLE i = AID COLON t1 = typ0 TO t2 = typ0 { RODecl(i,true,t1,t2) }
| OPERATOR i = AID COLON t1 = typ0 TO t2 = typ0 { RODecl(i,false,t1,t2) }
| BILINEAR MAP i = ID COLON g1 = TG STAR g2 = TG TO g3 = TG { EMDecl(i,g1,g2,g3) }
| ASSUMPTION_DECISIONAL i = ID LBRACKET g0 = gdef0 RBRACKET LBRACKET g1 = gdef0 RBRACKET
    sym=option(symmetric_vars)
    { AssmDec(i,g0,g1,opt id [] sym) }
| ASSUMPTION_COMPUTATIONAL
    i1 = ID sym=option(symmetric_vars) LBRACKET g = gdef0 RBRACKET
    COLON e = expr0
    { AssmComp(i1,g,e,opt id [] sym) }
| PROVE LBRACKET g = gdef0 RBRACKET e=event { Judgment(g,e) }
| PRINTGOALS COLON i = ID { PrintGoals(i) }
| PRINTGOAL COLON i = ID { PrintGoal(i) }
| PRINTPROOF { PrintProof(false) }
| PRINTPROOF_EX { PrintProof(true) }
| PRINTGOALS { PrintGoals("") }
| PRINTDEBUG s=STRING { Debug s }
| SETUNSAFE { Unsafe(true) }
| UNSETUNSAFE { Unsafe(false) }
| RNORM { Apply(Rnorm) }
| RNORM_NOUNFOLD { Apply(Rnorm_nounfold) }
| RNORM_UNKNOWN is = ID* { Apply(Rnorm_unknown(is)) }
| RNORM_SOLVE e = expr0 { Apply(Rnorm_solve(e)) }
| RINDEP { Apply(Rindep(false)) }
| RINDEP_EX { Apply(Rindep(true)) }
| RSWAP i = NAT j =int { Apply(Rswap(i-1,j)) }
| RSWAP op = opos j =int { Apply(Rswap_oracle(op,j)) }
| ASSUMPTION_DECISIONAL    s=uoption(ID) d=uoption(dir)
    rngs=option(ranges)
    xs=option(ID+)
    { Apply (Rassm_dec(false,s,d,rngs,xs))}
| ASSUMPTION_DECISIONAL_EX s=uoption(ID) d=uoption(dir)
    rngs=option(ranges)
    xs=option(ID+)
    { Apply (Rassm_dec(true,s,d,rngs,xs))}
| ASSUMPTION_COMPUTATIONAL    s=uoption(ID) rngs=option(ranges)
  { Apply (Rassm_comp(false,s,rngs))}
| ASSUMPTION_COMPUTATIONAL_EX s=uoption(ID)
  rngs=option(ranges)
  { Apply (Rassm_comp(true,s,rngs))}
| RCONV LBRACKET gd = gdef0 RBRACKET e=event { Apply(Requiv(gd,e)) }
| RLET_ABSTRACT i = uoption(NAT) i1 = ID e1 = uoption(expr0) mupto = option(NAT)
  { Apply(Rlet_abstract(map_opt (fun x -> x -1) i
                       ,i1,e1,map_opt (fun x -> x - 1) mupto)) }
| RSUBST i = NAT e1 = expr0 e2 = expr0 mupto = option(NAT)
  { Apply(Rsubst(i - 1,e1,e2,mupto)) }
| RLET_UNFOLD i = option(NAT) { Apply(Rlet_unfold(map_opt (fun x -> x - 1) i)) }
| RADD_TEST op = opos e = expr0 asym = AID fvs = ID*
  { Apply(Radd_test(Some(op),Some(e),Some(asym),Some(fvs))) }
| RADD_TEST UNDERSCORE { Apply(Radd_test(None,None,None,None)) }
| REXCEPT i = uoption(NAT) es = uoption(expr0*)
  { Apply(Rexcept(map_opt (fun i -> i-1) i,es)) }
| REXCEPT_ORACLE op = opos es = expr0* { Apply(Rexcept_orcl(op,es)) }
| RRND exact=option(EXCL) mi = uoption(NAT) mc1 = uoption(ctx) mc2 = uoption(ctx)
  { Apply(Rrnd(exact<>None,map_opt (fun i -> i -1) mi,mc1,mc2)) }
| DEDUCE  LBRACKET es=separated_list(COMMA,expr0) RBRACKET e=expr0
  { Apply(Deduce(es,e)) }
| RSIMP { Apply(Rsimp) }
| RCRUSH  mi = uoption(NAT) { Apply(Rcrush(false,mi)) }
| RCRUSH  { Apply(Rcrush(false,Some(1))) }
| BYCRUSH { Apply(Rcrush(true,None)) }
| BYCRUSH mi = uoption(NAT) { Apply(Rcrush(true,mi)) }
| RRND_ORACLE op = uoption(opos) c1 = uoption(ctx) c2 = uoption(ctx) { Apply(Rrnd_orcl(op,c1,c2)) }
| RBAD i=NAT s = ID { Apply(Rbad (i-1,s)) }
| RCTXT_EV LPAREN i1 = ID TO e1 = expr0 RPAREN j = NAT
  { Apply(Rctxt_ev(i1,e1,j - 1)) }
| RREMOVE_EV is = int+
  { Apply(Rremove_ev(L.map (fun x -> x - 1) is)) }
| RSPLIT_EV i = int
  { Apply(Rsplit_ev(i - 1)) }
| RCASE_EV e = uoption(expr0)
  { Apply(Rcase_ev(e)) }
| RCTXT_EV LPAREN i1 = ID TO e1 = expr0 RPAREN
  { Apply(Rctxt_ev(i1,e1,0)) }
| RFALSE_EV {Apply(Rfalse_ev)}
| RREWRITE_ORACLE op = opos d = dir { Apply(Rrewrite_orcl(op,d)) }
| RREWRITE_EV i = int d = option(dir) { Apply(Rrewrite_ev(i - 1,opt id LeftToRight d)) }
| EXTRACT s=STRING { Extract s }

instruction:
| i = instr DOT EOF { i }

theory :
| i = instr DOT EOF { [i] }
| i = instr DOT t = theory { i::t }
