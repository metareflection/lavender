{
open Parser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
let id = ['a'-'z' 'A'-'Z' '0'-'9' '_' '-' '?']+
let strlit =
    ['a'-'z' 'A'-'Z' '0'-'9' '_' '-' '.' '!' ',' '?' '/' ':']+

rule read = 
  parse
  | white { read lexbuf }
  | "true" { TRUE }
  | "false" { FALSE }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "+" { ID "+" }
  | "-" { ID "-" }
  | "*" { ID "*" }
  | "<" { ID "<" }
  | ">" { ID ">" }
  | '"' { DOUBLEQUOTE }
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | id { ID (Lexing.lexeme lexbuf) }
  | strlit { STRINGLIT (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { UNDEF (Lexing.lexeme lexbuf) }