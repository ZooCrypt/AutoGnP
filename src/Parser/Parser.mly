%{
  (** Parser for expressions, games, judgments, and tactic command. *)
  open ParserTypes
  open Assumption
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
%token SLASH2
%token SLASHEQ
%token SLASH2EQ
%token INFTHEORETIC

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
%token QUERIES
%token IN
/************************************************************************/
/* Tokens for games */

%token LEFTARROW
%token LET
%token SAMP
%token SHARP
%token BACKSLASH
%token LBRACK
%token RBRACK
%token MID
%token SEMICOLON
%token <string> LIST
%token WITH
/* %token <string> AID */
%token <int> NAT

/************************************************************************/
/* Tokens for theories */

%token TO
%token ADVERSARY
%token ORACLE
%token OPERATOR
%token ASSUMPTION
%token ASSUMPTION_DECISIONAL
%token ASSUMPTION_COMPUTATIONAL
%token RANDOM
%token BILINEAR
%token MAP
%token SUCC
%token ADV
%token BOUNDDIST
%token BOUNDSUCC
%token BOUNDADV
%token DOT
%token PRINTGOALS
%token PRINTGOAL
%token PRINTPROOF
%token PRINTPROOF_EX
%token PRINTDEBUG
%token PRINTGAME
%token PRINTGAMES
%token RNORM
%token RNORM_UNKNOWN
%token RNORM_SOLVE
%token RNORM_NOUNFOLD
%token RRND
%token RRND_ORACLE
%token RSWAP_MAIN
%token RSWAP
%token RCONV
%token RTRANS
%token RDIST_SYM
%token RDIST_EQ
%token RINDEP
%token RCRUSH
%token BYCRUSH
%token RSIMP  
%token BYSIMP
%token RBAD
%token RCASE_EV
%token RFALSE_EV
%token RREWRITE_EV
%token RSPLIT_EV
%token RREMOVE_EV
%token RLET_ABSTRACT
%token RLET_UNFOLD
%token RSUBST
%token RRENAME
%token RCTXT_EV
%token REXCEPT
%token RHYBRID
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
%token DEDUCE
%token LISTFE
%token <string> STRING

/************************************************************************/
/* Production types */

%type <ParserTypes.parse_ty> typ

%type <ParserTypes.parse_expr> expr

%type <ParserTypes.lcmd> lcmd

%type <ParserTypes.odef> odef

%type <ParserTypes.gcmd> gcmd

%type <ParserTypes.gdef> gdef

%type <ParserTypes.theory> theory

%type <ParserTypes.instr> instruction

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
| i=TBS { BS(i) }
| TBOOL { Bool }
| i=TG { G(i) }
| TFQ { Fq }
| UNIT { Prod([]) }
| LPAREN l=separated_list(STAR,typ0) RPAREN
  { match l with [t] -> t | _ -> Prod(l) }
| t=typ0 CARET n=NAT
  { Prod(Util.replicate n t) }

/************************************************************************/
/* Expressions */

/* FIXME: check operator precedence */

expr :
| e=expr0 EOF { e }

expr0 :
| EXISTS bd=hbindings COLON e1=expr1 EQUAL e2=expr1
     { Exists(e1,e2,bd) }
| e1=expr0 SHARP i=NAT { Proj(i,e1) }
| e1=expr1 EQUAL e2=expr1 { Eq(e1,e2) }
| e1=expr1 NEQ e2=expr1 { Not(Eq(e1,e2)) }
| e1=expr1 QUESTION e2=expr1 COLON e3=expr1 { Ifte(e1, e2, e3) }
| e1=expr1 IN QUERIES LPAREN oname=ID RPAREN { InLog(e1,oname) } 
| e=expr1 { e }

expr1 :
| e1=expr1 PLUS e2=expr1 { Plus(e1, e2) }
| e1=expr1 XOR e2=expr1  { Xor (e1, e2) }
| e=expr2 { e }

expr2:
| e1=expr2 MINUS e2=expr2 { Minus(e1, e2) }
| e=expr3 { e }

expr3:
| e1=expr4 SLASH e2=expr4 { Div(e1, e2) }
| e=expr4 { e }

expr4 :
| e1=expr4 STAR e2=expr4 { Mult(e1,e2) }
| e1=expr4 LAND e2=expr4 { Land(e1,e2) }
| e=expr5 { e }

expr5:
| e1=expr6 CARET e2=expr6 { Exp(e1, e2) }
| e =expr6 { e }

exprlist1 :
| e=expr0 { [e] }
| e=expr0 COMMA l=exprlist1 { e::l }

exprlist0 :
| l=exprlist1? { from_opt [] l }

expr6 :
| s=ID  { V(s) }
| UNIT    { Tuple [] }
| i=NAT { CFNat i }
| i=GEN { CGen(i) }
| i=ZBS { CZ(i) }
| TRUE    { CB(true) }
| FALSE   { CB(false) }
| s=ID LPAREN l=exprlist1 RPAREN
  { SApp(s,l) }
| MINUS e1=expr6 { Opp(e1) }
| NOT e=expr6 { Not(e) }
| LOG LPAREN e1=expr0 RPAREN { Log(e1) }
| LPAREN e=expr0 RPAREN {e}
| LPAREN l=exprlist1 RPAREN { Tuple(l) }
;

hbinding:
| x=ID LEFTARROW h=LIST {x,h}
;
hbindings:
| hbs=separated_nonempty_list(COMMA,hbinding) { hbs }

;
/************************************************************************/
/* List comprehensions */
/* FIXME: handle shift-reduce conflict */

idlist :
| UNIT { [] }
| LPAREN is=idlist0 RPAREN { is }
| is=idlist0 { is }

idlist0 :
| i=ID { [i] }
| i=ID COMMA is=idlist0 { i :: is }

lcmd :
| LET i=ID EQUAL e=expr0 { LLet(i,e) }
| is=idlist LEFTARROW hsym=LIST { LBind(is,hsym) }
| i=ID SAMP t=typ0 BACKSLASH es=exprlist1 { LSamp(i,t,es) }
| i=ID SAMP t=typ0                          { LSamp(i,t,[]) }
| e=expr0 { LGuard(e) }

lcmdlist :
| c=lcmd { [c] }
| c=lcmd COMMA cs=lcmdlist { c::cs }

lcomp :
| LBRACK e=expr0 MID cmds=lcmdlist RBRACK { (cmds, e) }

odef :
| oname=ID UNIT EQUAL lc=lcomp { (oname,[],lc) }
| oname=ID LPAREN args=idlist RPAREN EQUAL lc=lcomp { (oname, args, lc) }

/************************************************************************/
/* games */

odeflist :
| od=odef { [od] }
| od=odef COMMA ods=odeflist { od::ods }

mexprlist0 :
| l=exprlist1 {  match l with [e] -> e | _   -> Tuple l }

gcmd :
| LET i=ID EQUAL e=expr0 { GLet(i,e) }
| is=idlist LEFTARROW asym=ID LPAREN e=mexprlist0 RPAREN WITH os=odeflist
  { GCall(is,asym,e,os) }
| is=idlist LEFTARROW asym=ID LPAREN e=mexprlist0 RPAREN
  { GCall(is,asym,e,[]) }
| is=idlist LEFTARROW asym=ID UNIT WITH os=odeflist
  { GCall(is,asym,Tuple [],os) }
| is=idlist LEFTARROW asym=ID UNIT
  { GCall(is,asym,Tuple [],[]) }
| i=ID SAMP t=typ0 BACKSLASH es=exprlist1
  { GSamp(i,t,es) }
| i=ID SAMP t=typ0
  { GSamp(i,t,[]) }

gcmdlist0 :
| c=gcmd SEMICOLON { [c] }
| c=gcmd SEMICOLON cs=gcmdlist0 { c::cs }

gdef0 :
| cs=gcmdlist0 { cs }

gdef :
| gdef0 EOF { [] }

/************************************************************************/
/* for defining instructions */

int:
| i=NAT {i}
| MINUS i=NAT {-i}
;

event:
| COLON e=expr0 { e }
;

dir:
| LEFTARROW { Util.RightToLeft }
| TO        { Util.LeftToRight }
;

opos:
| LPAREN i=NAT COMMA j=NAT COMMA k=NAT RPAREN { (i-1,j-1,k-1) }
;

%public uopt(X):
| UNDERSCORE { None }
| x=X { Some x }
;

ty_anno :
| COLON  t=typ0 { t }

ctx :
| LPAREN i=ID ot=option(ty_anno) TO e=expr0 RPAREN { (i,ot,e) }
;

sym_class:
| LBRACK vs=separated_nonempty_list(COMMA,ID) RBRACK { vs }
;

sym_vars:
| LPAREN symclass=sym_class* RPAREN {symclass}
;

/************************************************************************/
/* declarations */

atype:
| SUCC { A_Succ }
| ADV  { A_Adv }

decl :
| ADVERSARY i=ID  COLON t1=typ0 TO t2=typ0 { ADecl(i,t1,t2) } 
| ORACLE    i=ID  COLON t1=typ0 TO t2=typ0 { ODecl(i,t1,t2) }
| RANDOM ORACLE i=ID COLON t1=typ0 TO t2=typ0 { RODecl(i,true,t1,t2) }
| OPERATOR i=ID COLON t1=typ0 TO t2=typ0 { RODecl(i,false,t1,t2) }
| BILINEAR MAP i=ID COLON g1=TG STAR g2=TG TO g3=TG { EMDecl(i,g1,g2,g3) }
| ASSUMPTION it=delimited(LBRACK,INFTHEORETIC,RBRACK)?
    i=ID sym=option(sym_vars) LBRACK g0=gdef0 RBRACK LBRACK g1=gdef0 RBRACK
  { AssmDec(i,it<>None,g0,g1,opt id [] sym) }
| ASSUMPTION it=delimited(LBRACK,INFTHEORETIC,RBRACK)?
    i1=ID at=atype sym=option(sym_vars) LBRACK g=gdef0 RBRACK COLON e=expr0
  { AssmComp(i1,it<>None,at,g,e,opt id [] sym) }
| BOUNDSUCC LBRACK g=gdef0 RBRACK e=event { JudgSucc(g,e) }
| BOUNDADV LBRACK g=gdef0 RBRACK e=event { JudgAdv(g,e) }
| BOUNDDIST LBRACK g1=gdef0 RBRACK e1=event
     LBRACK g2=gdef0 RBRACK e2=event
   { JudgDist(g1,e1,g2,e2) }
;

/************************************************************************/
/* proof commands */

proof_command :
| ADMIT { Admit }
| LAST { Last }
| BACK { Back }
| UNDOBACK { UndoBack(false) }
| UNDOBACK_EXCL { UndoBack(true) }
| QED { Qed }
| EXTRACT s=STRING { Extract s }
| PRINTGOALS COLON i=ID { PrintGoals(i) }
| PRINTGOAL COLON i=ID { PrintGoal(i) }
| PRINTPROOF { PrintProof(false) }
| PRINTPROOF_EX { PrintProof(true) }
| PRINTGOALS { PrintGoals("") }
| PRINTDEBUG s=STRING { Debug s }
| PRINTGAME s=STRING { PrintGame s }
| PRINTGAMES s1=STRING s2=STRING { PrintGames(s1,s2) }
;

/************************************************************************/
/* tactics */
br_exprlist0:
| LBRACK es=exprlist0 RBRACK { es }
;

gpos:
| i=NAT { i - 1 }
| LBRACK i=NAT RBRACK { i - 1 }
| LBRACK MINUS i=NAT RBRACK { (-i) - 1}
;

assgn_pos:
| n=int            { Pos(n) }
| i=ID             { Var(i) } 
(*| i=ID PLUS  n=NAT { Var(i,Some n)   }
| i=ID MINUS n=NAT { Var(i,Some (-n))} *)
;

inter_pos:
| LBRACK i1=assgn_pos i2=assgn_pos? RBRACK { Some i1, i2 }
;

swap_pos:
| i=inter_pos  { i } 
| i1=assgn_pos { Some i1 , Some i1 }
; 

tactic :

/* norm variants */
| RNORM                { Rnorm }
| SLASH2               { Rnorm }
| RNORM_NOUNFOLD       { Rnorm_nounfold }
| SLASHEQ              { Rnorm_nounfold }
| RNORM_UNKNOWN is=ID* { Rnorm_unknown(is) }
| SLASH2EQ             { Rnorm_unknown([]) }
| RNORM_SOLVE e=expr0  { Rnorm_solve(e) }

/* conversion */
| RCONV LBRACK gd=gdef0 RBRACK e=event   { Rconv(gd,e) }
| RTRANS LBRACK gd=gdef0 RBRACK e=event  { Rtrans(gd,e) }
| RSUBST i=inter_pos? e1=expr0 e2=expr0 { 
    let i, mupto = from_opt (None,None) i in
    Rsubst(i,e1,e2,mupto) } 
| RRENAME v1=ID v2=ID { Rrename(v1,v2) }
| RLET_UNFOLD i=assgn_pos*            { Rlet_unfold(i) }
| RLET_ABSTRACT excl=EXCL? i=uopt(assgn_pos) 
          i1=ID e1=uopt(expr0) mupto=assgn_pos?
  { Rlet_abstract(i,i1,e1,mupto,excl=None) }

/* swapping */
| RSWAP i=swap_pos j=assgn_pos { Rswap(i,j) }
| RSWAP op=opos j=int { Rswap_oracle(op,j) }
| RSWAP_MAIN op=opos v=ID { Rswap_main(op,v) }

/* random samplings */
| RRND excl=EXCL?  mi=uopt(assgn_pos) mc1=uopt(ctx) mc2=uopt(ctx) mgen=expr0?
  { Rrnd(excl=None,mi,mc1,mc2,mgen) }
| REXCEPT i=uopt(assgn_pos) es=uopt(br_exprlist0) { Rexcept(i,es) }
| REXCEPT_ORACLE op=opos es=expr0*          { Rexcept_orcl(op,es) }

/* assumptions */
| ASSUMPTION_DECISIONAL excl=EXCL?
    s=uopt(ID) d=uopt(dir) rngs=inter_pos* xs=option(ID+)
  { Rassm_dec(excl=None,s,d,rngs,xs)}
| ASSUMPTION_COMPUTATIONAL excl=EXCL? s=uopt(ID) rngs=inter_pos*
  { Rassm_comp(excl=None,s,rngs)}

/* automated rules */
| BYSIMP               { Rsimp(true) }
| RSIMP                { Rsimp(false) }
| RCRUSH  mi=uopt(NAT) { Rcrush(false,mi) }
| RCRUSH               { Rcrush(false,Some(1)) }
| BYCRUSH              { Rcrush(true,None) }
| BYCRUSH mi=uopt(NAT) { Rcrush(true,mi) }

/* oracles */
| RRND_ORACLE op=uopt(opos) c1=uopt(ctx) c2=uopt(ctx) { Rrnd_orcl(op,c1,c2) }
| RREWRITE_ORACLE op=opos d=dir                       { Rrewrite_orcl(op,d) }
| RBAD i=NAT s=ID                                     { Rbad (i-1,s) }
| RADD_TEST op=opos e=expr0 asym=ID fvs=ID*
  { Radd_test(Some(op),Some(e),Some(asym),Some(fvs)) }
| RADD_TEST UNDERSCORE { Radd_test(None,None,None,None) }
| RHYBRID LPAREN i=NAT COMMA j=NAT RPAREN  lc=lcomp asym=ID
  { Rhybrid((i-1,j-1),lc,asym) }

/* events */
| RREMOVE_EV is=gpos+         { Rremove_ev(is) }
| RSPLIT_EV i=gpos            { Rsplit_ev(i - 1) }
| RCASE_EV e=uopt(expr0)      { Rcase_ev(e) }
| RREWRITE_EV i=gpos d=dir?   { Rrewrite_ev(i,opt id LeftToRight d) }
| RCTXT_EV oj=uopt(gpos) c=uopt(ctx) { Rctxt_ev(oj,c) }

/* probability bounding rules */
| RINDEP excl=EXCL? { Rindep(excl=None) }
| RFALSE_EV         { Rfalse_ev}

/* bounding distinguishing probability */
| RDIST_EQ  { Rdist_eq}
| RDIST_SYM { Rdist_sym}

/* debugging */
| DEDUCE  LBRACK es=separated_list(COMMA,expr0) RBRACK e=expr0 { Deduce(es,e) }
| LISTFE  es=expr0*                                            { FieldExprs(es) }


/************************************************************************/
/* instructions and theories */

instr :
| i=decl { i }
| i=proof_command { i }
| is=separated_nonempty_list(SEMICOLON,tactic)
  { match is with [i] -> Apply(i) | _ -> Apply(Rseq(is)) }

instruction:
| i=instr DOT EOF { i }

theory :
| i=instr DOT EOF { [i] }
| i=instr DOT t=theory { i::t }
