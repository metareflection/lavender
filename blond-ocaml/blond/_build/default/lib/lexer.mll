{
open Parser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
let id = ['a'-'z' 'A'-'Z' '0'-'9' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '?']+
let strlit = '"' id '"'

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
  | id { ID (Lexing.lexeme lexbuf) }
  | strlit { STRINGLIT (Lexing.lexeme lexbuf) }
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }