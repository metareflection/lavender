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
%token <string> UNDEF

%start <Evaluator.exp> prog
%%

prog:
  | e = sexp; EOF { e }
;

sexp:
  | i = INT { ConstExp (NumConst i) }
  | TRUE { ConstExp (BoolConst true) }
  | FALSE { ConstExp (BoolConst false) }
  | s = STRINGLIT { ConstExp (StringConst s) }
  | x = ID { VarExp x }
  | u = UNDEF { ConstExp (StringConst ("Invalid Character" ^ u)) }
  | LPAREN; RPAREN { ListExp [] } 
  | LPAREN; elst = exp_lst; RPAREN { ListExp elst } 
;

exp_lst:
  | e = sexp { e :: [] }
  | e = sexp; elst = exp_lst { e :: elst }
