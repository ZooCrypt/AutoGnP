%{
	open ParserUtil

%}

%token EOF

/************************************************************************/
/* Tokens for types */
%token TBS
%token TBOOL
%token TG
%token TGT
%token TFQ
%token STAR
%token LPAREN
%token RPAREN
%token UNDERSCORE
%token <string> LV_ID /* always l<int> */

/************************************************************************/
/* Tokens for expressions */
%token <string> ID
%token PLUS
%left PLUS

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

%token COMMA

%token ZERO
%token ONE
%token GEN
%token EMAP

/************************************************************************/
/* Production types */

%type <ParserUtil.parse_ty> typ

%type <ParserUtil.parse_expr> expr

/************************************************************************/
/* Start productions */
%start typ

%start expr

%%

/************************************************************************/
/* Types */

typ :
| t=typ0 EOF { t }

typ0 :
| TBS UNDERSCORE s=LV_ID { BS(s) }
| TBOOL { Bool }
| TG { G }
| TGT { GT }
| TFQ { Fq }
| LPAREN RPAREN { Prod([]) }
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
| e = expr1 { e }
| e1 = expr0 PLUS e2 = expr0 { Plus(e1, e2) }
| e1 = expr0 MINUS e2 = expr0 { Minus(e1, e2) }
| e1 = expr0 SLASH e2 = expr0 { Div(e1, e2) }
| e1 = expr0 QUESTION e2 = expr0 COLON e3 = expr0
  { Ifte(e1, e2, e3) }
| MINUS e1 = expr0 { Opp(e1) }  

exprlist0 :
| e = expr0 { [e] }
| e = expr0 COMMA l = exprlist0 { e::l }

expr1 :
| e1 = expr1 STAR e2 = expr1 { Mult(e1,e2) }
| e1 = expr1 LAND e2 = expr1 { Land(e1,e2) }
| e = expr2 { e }

expr2:
| e1 = expr2 CARET e2 = expr2 { Exp(e1, e2) }
| e = expr3 { e }

expr3 :
| s = ID { V(s) }
| ONE { Cnst(Expr.FOne) }
| ZERO { Cnst(Expr.FZ) }
| GEN { Cnst(Expr.GGen) }
| TRUE { Cnst(Expr.B true) }
| FALSE { Cnst(Expr.B false) }
| s = ID LPAREN l = exprlist0 RPAREN { SApp(s,l) }
| NOT e = expr0 { Not(e) }
| EMAP e1 = expr0 COMMA e2 = expr0 RPAREN { EMap(e1,e2) }
| LPAREN e = expr0 RPAREN {e}
| LPAREN RPAREN { Tuple []}
| LPAREN e = expr0 COMMA l = exprlist0 RPAREN { Tuple(e::l) }