{
  open Parser

  exception Error of Lexing.position * string
}

rule token = parse
| [' ' '\t']                                           { token lexbuf }
| '\n'                                                 { Lexing.new_line lexbuf; token lexbuf }
| '\\'                                                 { BACKSLASH }
| '.'                                                  { DOT }
| ':'                                                  { COLON }
| "->"                                                 { ARROW }
| "Nat"                                                { NAT }
| "Forall"                                             { FORALL }
| "Sigma"                                              { SIGMA }
| "Succ"                                               { SUCC }
| "Zero"                                               { ZERO }
| "Refl"                                               { REFL }
| "nat_elim"                                           { NATELIM }
| "eq_elim"                                            { EQELIM }
| "Type"                                               { TYPE }
| '<'                                                  { LANGLE }
| '>'                                                  { RANGLE }
| '('                                                  { LPAREN }
| ')'                                                  { RPAREN }
| ','                                                  { COMMA }
| "::"                                                 { DOUBLECOLON }
| ";;"                                                 { DOUBLESEMI }
| '='                                                  { EQ }
| ":="                                                 { COLONEQ }
| '#' [^'\n']* '\n'                                    { Lexing.new_line lexbuf; token lexbuf }
| '#' [^'\n']* eof                                     { EOF }
| eof                                                  { EOF }

(* expression variables are restricted to start with lowercase letter or underscore *)
| ['0'-'9']+ as x                                      { LEVEL (int_of_string x) }
| ['a'-'z''A'-'Z''0'-'9''\'''_']+ as x     { ID x }

| _                                         {
    let msg = Printf.sprintf "unexpected character %C" (Lexing.lexeme_char lexbuf 0)
    in raise (Error (Lexing.lexeme_start_p lexbuf, msg))
}
