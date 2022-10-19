%{
open Interpreter
%}

%token <string> IDENT
%token <Uint63.t> INT
%token FUN
%token WITH
%token IF0
%token LBRACE "{"
%token RBRACE "}"
%token ADD "+"
%token SUB "-"
%token MUL "*"
%token DIV "/"
%token EOF

%start <cfwae> prog

%%

prog : expr EOF { $1 }

expr :
  | IDENT { Var $1 }
  | INT { Num $1 }
  | "{" primop expr expr "}" { Primop ($2, $3, $4) }
  | "{" WITH "{" list(binding) "}" expr "}" { With ($4, $6) }
  | "{" IF0 expr expr expr "}" { If0 ($3, $4, $5) }
  | "{" FUN "{" list(IDENT) "}" expr "}" { Fun ($4, $6) }
  | "{" expr list(expr) "}" { App ($2, $3) }

binding : "{" IDENT expr "}" { ($2, $3) }

primop :
  | "+" { P_Add }
  | "-" { P_Sub }
  | "*" { P_Mul }
  | "/" { P_Div }
