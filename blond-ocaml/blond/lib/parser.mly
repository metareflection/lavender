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
%token DOUBLEQUOTE
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
  | x = ID { VarExp x }
  | DOUBLEQUOTE; DOUBLEQUOTE { ConstExp (StringConst "") }
  | DOUBLEQUOTE; x = ID ; DOUBLEQUOTE { ConstExp (StringConst x) }
  | DOUBLEQUOTE; s = STRINGLIT ; DOUBLEQUOTE { ConstExp (StringConst s) }
  | u = UNDEF { ConstExp (StringConst ("Invalid Character" ^ u)) }
  | LPAREN; RPAREN { ListExp [] } 
  | LPAREN; elst = exp_lst; RPAREN { ListExp elst } 
;

exp_lst:
  | e = sexp { e :: [] }
  | e = sexp; elst = exp_lst { e :: elst }
