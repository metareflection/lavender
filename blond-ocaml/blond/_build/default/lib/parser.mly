%{
    open Evaluator
	 %}

%token <int> INT
%token <string> STRINGLIT
%token <string> ID
%token TRUE
%token FALSE
%token LPAREN
%token RPAREN
%token EOF

%start <Evaluator.exp> prog
%%

prog:
  | e = expr; EOF { e }
;

expr:
  | i = INT { ConstExp (NumConst i) }
  | x = ID { VarExp x }
  | s = STRINGLIT { ConstExp (StringConst s) }
  | TRUE { ConstExp (BoolConst true) }
  | FALSE { ConstExp (BoolConst false) }
  | LPAREN; RPAREN { ListExp [] } 
  | LPAREN; elst=expr_lst; RPAREN { ListExp elst } 
;

expr_lst:
  | e = expr { e :: [] }
  | e = expr; elst = expr_lst { e :: elst }
