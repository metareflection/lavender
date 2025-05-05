
(* The type of tokens. *)

type token = 
  | TRUE
  | STRINGLIT of (string)
  | RPAREN
  | LPAREN
  | INT of (int)
  | ID of (string)
  | FALSE
  | EOF

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Evaluator.exp)
