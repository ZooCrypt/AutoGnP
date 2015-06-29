%{
  (** Parser for expressions, games, judgments, and tactic command. *)
  open ParserTypes
  open Syms
  open Abbrevs
  open Assumption
  open Util

  module G = Game

%}

/*======================================================================*/
/* Tokens */

%token EOF

/*----------------------------------------------------------------------*/
/* Tokens for types */

(* %token EXISTS *)
%token <string> TBS
%token TBOOL
%token <string> TG
%token TFQ
%token STAR
%token EXCL
%left  STAR
%token LPAREN
%token RPAREN
%token RESTART

/*----------------------------------------------------------------------*/
/* Tokens for expressions */

%token <string> ID
%token <string> F_INV
%token <string> KEYPAIR
%token <string> PKEY
%token <string> SKEY
%token <string> GETPK
%token <string> GETSK						  
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
%token SLASH3EQ
%token PPT
%token INFTHEO
%token INRIGHT
%token INBOTH
%token TRUE
%token FALSE
%token NOT
%token COLON
%token QUESTION
%token LAND
%token FORALL
%token EXISTS
%token IN
%left  LAND

%token EQUAL
%token GREATER
%token LESS
%token ASSERT

%token COMMA
%token NEQ

%token <string> GEN
%token LOG
%token <string> ZBS
(* %token QUERIES *)
(* %token IN *)

/*----------------------------------------------------------------------*/
/* Tokens for games */

%token LEFTARROW
%token LET
%token RETURN
%token SAMP
%token SHARP
%token BACKTICK
%token BACKSLASH
%token LBRACK
%token RBRACK
%token LCBRACE
%token RCBRACE
%token SEMICOLON
%token <string> LIST
%token WITH
/* %token <string> AID */
%token <int> NAT

/*----------------------------------------------------------------------*/
/* Tokens for theories */

%token TO
%token ADVERSARY
%token ORACLE
%token OPERATOR
%token PERMUTATION
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
%token PRINTDEBUG
%token PRINTGAME
%token PRINTGAMES
%token RNORM
%token RNORM_UNKNOWN
%token RNORM_SOLVE
%token RNORM_NOUNFOLD
%token RRND
%token RRND_EXP
%token RRND_ORACLE
%token RSWAP_MAIN
%token RSWAP
%token RCONV
%token RTRANS
%token RTRANSSTAR
%token RINSERT
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
%token RSPLIT_INEQ
%token RREMOVE_EV
%token RLET_ABSTRACT
%token RLET_ABSTRACT_DEDUCE
%token RLET_UNFOLD
%token RSUBST
%token RRENAME
%token RCTXT_EV
%token REXCEPT
%token RHYBRID
%token RADD_TEST
%token RGUARD
%token RGUESS
%token RFIND
%token REXCEPT_ORACLE
%token RREWRITE_ORACLE
%token UNDERSCORE
%token ADMIT
%token LAST
%token BACK
%token UNDOBACK
%token QED
%token EXTRACT
%token DEDUCE
%token LISTFE
%token <string> STRING

/*======================================================================*/
/* Production types */

%type <ParserTypes.lcmd list> lcmd

%type <ParserTypes.odef> odef

%type <ParserTypes.gcmd list> gcmd

%type <ParserTypes.theory> theory

%type <ParserTypes.instr list> instruction

/*======================================================================*/
/* Start productions */

%start odef

%start instruction

%start theory

%%


/*======================================================================*/
/* Useful definitions and abbreviations */

%public uopt(X):
| UNDERSCORE { None }
| x=X { Some x }

%public seplist0(S,X):
| l=separated_list(S,X) {l}

%public seplist1(S,X):
| l=separated_nonempty_list(S,X) { l }

%public termlist0(S,X):
| l=list(terminated(X,S)) {l}

%public termlist1(S,X):
| l=nonempty_list(terminated(X,S)) { l }

%public paren_list0(S,X):
| l=delimited(LPAREN,separated_list(S,X),RPAREN) {l}

/*======================================================================*/
/* Types */

typ :
| i=TBS                              { BS(i) }
| s=KEYPAIR                          { KeyPair(s) }
| s=PKEY                          { PKey(s) }
| s=SKEY                          { SKey(s) }
| TBOOL                              { Bool }
| i=TG                               { G(i) }
| TFQ                                { Fq }
| LPAREN l=seplist0(STAR,typ) RPAREN { mk_Prod l }
| t=typ CARET n=NAT                  { Prod(Util.replicate n t) }

/*======================================================================*/
/* Expressions */

expr :
| e1=expr  SHARP i=NAT                       { Proj(i,e1) }
| e1=expr1 EQUAL e2=expr1                    { Eq(e1,e2) }
| e1=expr1 NEQ e2=expr1                      { Not(Eq(e1,e2)) }
| e1=expr1 QUESTION e2=expr1 COLON e3=expr1  { Ifte(e1, e2, e3) }
| FORALL l=seplist1(COMMA,binding1) COLON e1=expr1 { All(l,e1) }
(* | e1=expr1 IN QUERIES LPAREN oname=ID RPAREN { InLog(e1,oname) }  *)
| e=expr1                                    { e }

expr1 :
| e1=expr1 PLUS e2=expr1 { Plus(e1, e2) }
| e1=expr1 XOR e2=expr1  { Xor (e1, e2) }
| e=expr2                { e }

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
| e=expr6                 { e }

expr6 :
| s=ID                           { V(Unqual,s) }
| s1=ID BACKTICK s2=ID           { V(Qual s1, s2) }
| i=NAT                          { CFNat i }
| i=GEN                          { CGen(i) }
| i=ZBS                          { CZ(i) }
| TRUE                           { CB(true) }
| FALSE                          { CB(false) }
| s=ID l=paren_list0(COMMA,expr) { SApp(s,l) }
| MINUS e1=expr6                 { Opp(e1) } (* FIXME: check how unary/binary minus handled in Haskell/OCaml *)
| NOT e=expr6                    { Not(e) }
| LOG LPAREN e1=expr RPAREN      { Log(e1) }
| l=paren_list0(COMMA,expr)      { mk_Tuple l }
| s=F_INV LPAREN k1=expr COMMA e1=expr RPAREN { ParsePerm(s,true,k1,e1) }
| s=GETPK LPAREN e=expr RPAREN             { ParseGetPK(s,e) }
| s=GETSK LPAREN e=expr RPAREN             { ParseGetSK(s,e) }
       

/*======================================================================*/
/* Oracle definitions */

except_exprs :
| BACKSLASH LCBRACE es=separated_nonempty_list(COMMA,expr) RCBRACE { es }
| BACKSLASH         es=separated_nonempty_list(COMMA,expr)         { es }

lcmd :
| LET i=ID EQUAL e=expr                         { [ LLet(i, e) ] }
| is=seplist0(COMMA,ID) LEFTARROW hsym=LIST     { [ LBind(is, hsym) ] }
(*| i=KEYPAIR SAMP t=typ
    es=loption(except_exprs)                    { LSampKP(i, t, es) }*)
| is=seplist1(COMMA,ID) SAMP t=typ
    es=loption(except_exprs)                    { L.map (fun i -> LSamp(i, t, es)) is }
| e=expr                                        { [ LGuard(e) ] }

obody :
| LCBRACE cmds=termlist0(SEMICOLON,lcmd)
    RETURN e=expr SEMICOLON? RCBRACE     { (L.concat cmds, e) }

odecl :
| lc=obody { Odef lc}
| LBRACK lc1=obody lc2=obody lc3=obody RBRACK { Ohybrid(lc1,lc2,lc3) }

odef :
| oname=ID args=paren_list0(COMMA,ID) EQUAL od=odecl { (oname, args, od) }

/*======================================================================*/
/* Games */

arglist0 :
| l=paren_list0(COMMA,expr) { mk_Tuple l }

odefs :
| WITH os=seplist1(COMMA,odef) { os }

var_pat :
| i = ID                                    { [i] }
| LPAREN is=separated_list(COMMA,ID) RPAREN { is }

gcmd :
| LET i=ID EQUAL e=expr                                      { [ GLet(i,e) ] }
| is=var_pat LEFTARROW asym=ID e=arglist0 ods=loption(odefs) { [ GCall(is, asym, e, ods) ] }
| ASSERT LPAREN e=expr RPAREN                                { [ GAssert(e) ] }
| ids=seplist1(COMMA,ID) SAMP t=typ es=loption(except_exprs) { L.map (fun i -> GSamp(i, t, es)) ids }

gdef :
| cs=termlist0(SEMICOLON,gcmd) { L.concat cs }

/*======================================================================*/
/* Instructions */

/*----------------------------------------------------------------------*/
/* helper definitions */

int:
| i=NAT {i}
| MINUS i=NAT {-i}

binding1:
| x=ID IN o=ID {[x], o}
| LPAREN xs=seplist1(COMMA,ID) RPAREN IN o=ID {xs, o}

binding:
(* | FORALL l=seplist1(COMMA,binding1) COLON {Game.Forall, l} *)
| EXISTS l=seplist1(COMMA,binding1) COLON {Game.Exists, l}

bind_event:
| COLON b=binding? e=expr
  { match b with
    | None                 -> (Game.Forall, []), e
    | Some (Game.Forall,_) -> assert false
    | Some (Game.Exists,l) -> (Game.Exists,l),e }

dir:
| LEFTARROW { Util.RightToLeft }
| TO        { Util.LeftToRight }

otype:
| LESS    { G.OHless}
| EQUAL   { G.OHeq }
| GREATER { G.OHgreater }

opos:
| LPAREN i=NAT COMMA j=NAT COMMA k=NAT RPAREN                { (i-1, j-1, k-1, G.Onohyb) }
| LPAREN i=NAT COMMA j=NAT COMMA k=NAT COMMA ot=otype RPAREN { (i-1, j-1, k-1, G.Ohyb ot) }

opos_partial:
| LPAREN i=NAT COMMA j=NAT COMMA k=NAT RPAREN { (i-1, j-1, k-1) }

ty_anno :
| COLON  t=typ { t }

ctx :
| LPAREN i=ID ot=option(ty_anno) TO e=expr RPAREN { (i, ot, e) }

sym_class:
| LBRACK vs=separated_nonempty_list(COMMA,ID) RBRACK { vs }

sym_vars:
| LPAREN symclass=sym_class* RPAREN {symclass}

/*----------------------------------------------------------------------*/
/* declarations */

atype:
| SUCC { A_Succ }
| ADV  { A_Adv }

decl :
| ADVERSARY i=ID  COLON t1=typ TO t2=typ    { ADecl(i, t1, t2) } 
| ORACLE    i=ID  COLON t1=typ TO t2=typ    { ODecl(i, t1, t2) }
| RANDOM ORACLE i=ID COLON t1=typ TO t2=typ { RODecl(i, true, t1, t2) } (* Shouldn't it be RRND_ORACLE instead ? *)
| PERMUTATION i=ID COLON k=TBS { PermDecl(i, BS(k)) } (* { assert false } *) (* permutation f : BS_k *)
| OPERATOR i=ID COLON t1=typ TO t2=typ      { RODecl(i, false, t1, t2) }
| BILINEAR MAP i=ID COLON
    g1=TG STAR g2=TG TO g3=TG               { EMDecl(i, g1, g2, g3) }
| ASSUMPTION
    it=boption(delimited(LBRACK,INFTHEO,RBRACK))
    i=ID sym=loption(sym_vars)
    LBRACK g0=gdef RBRACK
    LBRACK g1=gdef RBRACK                   { AssmDec(i, it, g0, g1, sym) }
| ASSUMPTION
    it=boption(delimited(LBRACK,INFTHEO,RBRACK))
    i1=ID at=atype sym=loption(sym_vars)
    LBRACK g=gdef RBRACK e=bind_event       { AssmComp(i1, it, at, g, e, sym) }
| BOUNDSUCC LBRACK g=gdef RBRACK e=bind_event    { JudgSucc(g, e) }
| BOUNDADV LBRACK g=gdef RBRACK e=bind_event     { JudgAdv(g, e) }
| BOUNDDIST LBRACK g1=gdef RBRACK e1=bind_event
    LBRACK g2=gdef RBRACK e2=bind_event          { JudgDist(g1, e1, g2, e2) }

/*----------------------------------------------------------------------*/
/* proof commands */

proof_command :
| ADMIT                                { Admit }
| LAST                                 { Last }
| BACK                                 { Back }
| UNDOBACK b=boption(EXCL)             { UndoBack(b) }
| QED                                  { Qed }
| RESTART                              { Restart }
| EXTRACT s=STRING                     { Extract s }
| PRINTGOALS COLON i=ID                { PrintGoals(i) }
| PRINTGOAL COLON i=ID                 { PrintGoal(i) }
| PRINTPROOF b=boption(EXCL) s=STRING? { PrintProof(b,s) }
| PRINTGOALS                           { PrintGoals("") }
| PRINTDEBUG s=STRING                  { Debug s }
| PRINTGAME s=STRING                   { PrintGame s }
| PRINTGAMES s1=STRING s2=STRING       { PrintGames(s1,s2) }

/*----------------------------------------------------------------------*/
/* tactics */

br_exprlist0:
| LBRACK es=separated_list(COMMA,expr) RBRACK { es }

gpos:
| i=NAT { i - 1 }
| LBRACK i=NAT RBRACK { i - 1 }
| LBRACK MINUS i=NAT RBRACK { (-i) - 1}

assgn_pos:
| n=int            { Pos(n) }
| i=ID             { Var(i) } 
| LPAREN n=NAT RPAREN  { AbsPos(n-1) }

inter_pos:
| LBRACK i1=assgn_pos i2=assgn_pos? RBRACK { Some i1, i2 }

swap_pos:
| i=inter_pos  { i } 
| i1=assgn_pos { Some i1 , Some i1 }

diff_cmd:
| RRENAME i1=ID i2=ID mupto=assgn_pos?
  { Drename(i1,i2,mupto) }
| RINSERT p=assgn_pos LBRACK gd=gdef RBRACK
  { Dinsert(p,gd) }
| RSUBST p=assgn_pos LPAREN e1=expr TO e2=expr RPAREN
  { Dsubst(p,e1,e2) }

id_pair:
| id = ID { (id,None) }
| LPAREN id1=ID id2=ID RPAREN { (id1,Some id2) }

maybe_upto:
| COLON ap=assgn_pos { ap }

tactic :

/* norm variants */
| RNORM                { Rnorm }
| SLASH2               { Rnorm }
| RNORM_NOUNFOLD       { Rnorm_nounfold }
| SLASHEQ              { Rnorm_nounfold }
| RNORM_UNKNOWN is=ID* { Rnorm_unknown(is) }
| SLASH2EQ is=ID*      { Rnorm_unknown(is) }
| SLASH3EQ is=ID*      { Rseq [Rnorm; Rnorm_unknown(is)] }
| RNORM_SOLVE e=expr  { Rnorm_solve(e) }

/* conversion */
| RCONV gd=uopt(delimited(LBRACK,gdef,RBRACK)) e=bind_event { Rconv(gd,e) }
| RTRANS LBRACK gd=gdef RBRACK e=bind_event  { Rtrans(gd,e) }
| RTRANSSTAR LBRACK dcmds=separated_nonempty_list(COMMA,diff_cmd) RBRACK
  { Rtrans_diff(dcmds) }
| RSUBST i=inter_pos? LPAREN e1=expr TO e2=expr RPAREN
  { let i, mupto = from_opt (None,None) i in
    Rsubst(i,e1,e2,mupto) } 
| RRENAME v1=ID v2=ID { Rrename(v1,v2) }
| RLET_UNFOLD i=assgn_pos*            { Rlet_unfold(i) }
| RLET_ABSTRACT excl=EXCL? i=uopt(assgn_pos) 
          i1=ID e1=uopt(expr) mupto=maybe_upto?
  { Rlet_abstract(i,i1,e1,mupto,excl=None) }
| RLET_ABSTRACT_DEDUCE excl=EXCL? i=assgn_pos
          i1=ID e1=expr mupto=maybe_upto?
  { Rlet_abstract_deduce(excl<>None,i,i1,e1,mupto) }
| ASSERT i=assgn_pos e=expr?
  { Rassert(i,e) }

/* swapping */
| RSWAP i=swap_pos j=assgn_pos { Rswap(i,j) }
| RSWAP op=opos j=int { Rswap_oracle(op,j) }
| RSWAP_MAIN op=opos_partial v=ID { Rswap_to_main(op,v) }
| RSWAP_MAIN i=assgn_pos op=opos_partial v=ID { Rswap_to_orcl(i,op,v) }

/* random samplings */
| RRND excl=EXCL?  mi=uopt(assgn_pos) mc1=uopt(ctx) mc2=uopt(ctx) mgen=expr?
  { Rrnd(excl=None,mi,mc1,mc2,mgen) }
| RRND_EXP excl=EXCL? ids=id_pair+
  { Rrnd_exp(excl=None,ids) }

| REXCEPT i=uopt(assgn_pos) es=uopt(br_exprlist0) { Rexcept(i,es) }
| REXCEPT_ORACLE op=opos es=br_exprlist0          { Rexcept_orcl(op,es) }

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
| RADD_TEST op=opos e=expr asym=ID fvs=ID*
  { Radd_test(Some(op),Some(e),Some(asym),Some(fvs)) }
| RADD_TEST UNDERSCORE { Radd_test(None,None,None,None) }
| RGUARD op=opos e=expr? { Rguard(op,e) }
| RGUESS asym=ID fvs=ID* { Rguess(asym,fvs) }
| RFIND LPAREN bd=ID* TO body=expr RPAREN e=expr asym=ID fvs=ID*
                         { Rfind((bd,body),e,asym,fvs) }
| RHYBRID LPAREN i=NAT COMMA j=NAT RPAREN  lc=obody
  { Rhybrid((i-1,j-1),lc) }

/* events */
| RREMOVE_EV is=gpos+                { Rremove_ev(is) }
| RSPLIT_EV i=gpos                   { Rsplit_ev(i) }
| RSPLIT_INEQ i=gpos                 { Rsplit_ineq(i) }
| RCASE_EV e=uopt(expr)              { Rcase_ev(e) }
| RREWRITE_EV i=gpos d=dir?          { Rrewrite_ev(i,from_opt LeftToRight d) }
| RCTXT_EV oj=uopt(gpos) c=uopt(ctx) { Rctxt_ev(oj,c) }

/* probability bounding rules */
| RINDEP excl=EXCL? { Rindep(excl=None) }
| RFALSE_EV         { Rfalse_ev }

/* bounding distinguishing probability */
| RDIST_EQ  { Rdist_eq }
| RDIST_SYM { Rdist_sym }

/* debugging */
| DEDUCE  ppt=PPT?
    LBRACK es=seplist1(COMMA,expr) RBRACK e=expr { Deduce(ppt<>None,es,e) }
| LISTFE LBRACK es=seplist1(COMMA,expr) RBRACK   { FieldExprs(es) }

/*----------------------------------------------------------------------*/
/* instructions and theories */

selector:
| INRIGHT { InRight }
| INBOTH { InBoth }

instr :
| i=decl { [i] }
| i=proof_command { [i] }
| ir=selector? is=separated_nonempty_list(SEMICOLON,tactic) 
  { let tacs =
      match is with
      | [i] -> [Apply(i)]
      | _ -> [Apply(Rseq(is))]
    in
    match ir with
    | None -> tacs
    | Some InBoth -> tacs@[Apply(Rdist_sym)]@tacs@[Apply(Rdist_sym)]
    | Some InRight -> [Apply(Rdist_sym)]@tacs@[Apply(Rdist_sym)]
  }

instruction:
| i=instr DOT EOF { i }

theory :
| i=instr DOT EOF { i }
| i=instr DOT t=theory { i@t }
