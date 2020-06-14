%token <string> ID
%token <int>    LEVEL
%token EQ COLONEQ
%token BACKSLASH
%token FORALL SIGMA
%token NAT TYPE REFL SUCC ZERO
%token NATELIM EQELIM
%token DOT COLON COMMA
%token LPAREN RPAREN LANGLE RANGLE
%token DOUBLESEMI DOUBLECOLON
%token EOF

%start <Syntax.binding option> main

%%

main:
| x = ID DOUBLECOLON e = expr DOUBLESEMI           { Some (Syntax.Claim (x, e)) }
| x = ID COLONEQ e = expr DOUBLESEMI               { Some (Syntax.Def (x, e)) }
| EOF                                              { None }

atomic_expr:
| x = ID                                           { Syntax.Var x }
| ZERO                                             { Syntax.Zero }
| TYPE l = option(LEVEL)                           { Syntax.Type l }  
| NAT                                              { Syntax.Nat }
| LPAREN e = expr RPAREN                           { e }

app_expr:
| e1 = app_expr e2 = atomic_expr                   { Syntax.App (e1, e2) }
| e = atomic_expr                                  { e }

expr:
| BACKSLASH x = ID COLON t = expr DOT e = expr     { Syntax.Lambda (x, t, e) }
| SUCC e = atomic_expr                             { Syntax.Succ e }                                 
| REFL e1 = atomic_expr e2 = atomic_expr                         { Syntax.Refl (e1, e2) }
| NATELIM e1 = atomic_expr e2 = atomic_expr e3 = atomic_expr e4 = atomic_expr  { Syntax.NatElim (e1, e2, e3, e4) }
| EQELIM e1 = atomic_expr e2 = atomic_expr e3 = atomic_expr e4 = atomic_expr   { Syntax.EqElim (e1, e2, e3, e4) }
| FORALL LPAREN x = ID COLON t = expr RPAREN DOT e = expr         { Syntax.Pi ((x, t), e) }
| x = atomic_expr EQ y = atomic_expr                             { Syntax.PropEq (x, y) }
| SIGMA  LPAREN x = ID COLON t = atomic_expr RPAREN DOT e = atomic_expr         { Syntax.Sigma ((x, t), e) }
| LANGLE LPAREN x = ID COMMA e1 = atomic_expr RPAREN COMMA e2 = atomic_expr RANGLE { Syntax.Pair ((x, e1), e2) }
| e = app_expr                                     { e }