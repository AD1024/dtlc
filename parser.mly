%token <string> ID
%token <int>    LEVEL
%token EQ COLONEQ BAR STAR
%token BACKSLASH
%token FORALL SIGMA
%token NAT TYPE REFL SUCC ZERO FST SND
%token NATELIM EQELIM INL INR SUMELIM
%token DOT COLON COMMA
%token LPAREN RPAREN LANGLE RANGLE LCURLY RCURLY
%token ARROW
%token DOUBLESEMI DOUBLECOLON
%token CMDNORMAL
%token EOF

%left  DOT
%right ARROW
%right BAR
%right STAR
%left  EQ

%start <Syntax.binding option> main

%%

main:
| x = ID DOUBLECOLON e = expr DOUBLESEMI           { Some (Syntax.Claim (x, e)) }
| x = ID COLONEQ e = expr DOUBLESEMI               { Some (Syntax.Def (x, e)) }
| CMDNORMAL e = expr DOUBLESEMI                    { Some (Syntax.CmdNormalize e) }
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

%public optional_ty(X):
| { Syntax.Type None }
| COLON e = X                                            { e }

expr:
| BACKSLASH x = ID optional_ty(expr) DOT e = expr                               { Syntax.Lambda (x, Syntax.Explicit, e) }
| BACKSLASH LCURLY x = ID optional_ty(expr) RCURLY DOT e = expr                 { Syntax.Lambda (x, Syntax.Implicit, e) }
| SUCC e = atomic_expr                                                          { Syntax.Succ e }
| INL e = atomic_expr                                                           { Syntax.Inl e }
| INR e = atomic_expr                                                           { Syntax.Inr e }
| FST e = atomic_expr                                                           { Syntax.Fst e }
| SND e = atomic_expr                                                           { Syntax.Snd e }
| REFL e1 = atomic_expr e2 = atomic_expr                                        { Syntax.Refl (e1, e2) }
| NATELIM e1 = atomic_expr e2 = atomic_expr e3 = atomic_expr e4 = atomic_expr   { Syntax.NatElim (e1, e2, e3, e4) }
| EQELIM e1 = atomic_expr e2 = atomic_expr e3 = atomic_expr e4 = atomic_expr    { Syntax.EqElim (e1, e2, e3, e4) }
| SUMELIM e1 = atomic_expr e2 = atomic_expr e3 = atomic_expr e4 = atomic_expr   { Syntax.SumElim (e1, e2, e3, e4) }
| FORALL LPAREN x = ID COLON t = expr RPAREN DOT e = expr                       { Syntax.Pi ((x, t, Syntax.Explicit), e) }
| FORALL LCURLY x = ID COLON t = expr RCURLY DOT e = expr                       { Syntax.Pi ((x, t, Syntax.Implicit), e) }
| x = expr EQ y = expr                                                          { Syntax.PropEq (x, y) }
| x = expr BAR y = expr                                                         { Syntax.Sum(x, y) }
| e1 = expr ARROW e2 = expr                                                     { Syntax.Pi(("$", e1, Syntax.Explicit), e2) }
| e1 = expr STAR e2 = expr                                                      { Syntax.Sigma(("$", e1), e2) }
| SIGMA  LPAREN x = ID COLON t = expr RPAREN DOT e = expr                       { Syntax.Sigma ((x, t), e) }
| LANGLE e1 = expr COMMA e2 = expr RANGLE                                       { Syntax.Pair (e1, e2) }
| e = app_expr                                                                  { e }