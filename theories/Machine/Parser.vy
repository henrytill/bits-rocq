(* -*- mode: prog; -*- *)

%{
Set Warnings "-deprecated-from-Coq".

From Bits.Machine Require Syntax.
%}

%token ADD SUB LPAREN RPAREN EOF
%token <nat> NUM

%start <Syntax.expr> parse_expr

%type <Syntax.expr> p_expr
%type <Syntax.expr> p_factor
%type <Syntax.expr> p_atom

%%

parse_expr : p_expr EOF  { $1 }

p_atom :
  | NUM                  { Syntax.Val $1 }
  | LPAREN p_expr RPAREN { $2 }

p_expr :
  | p_factor             { $1 }
  | p_expr ADD p_factor  { Syntax.Add $1 $3 }
  | p_expr SUB p_factor  { Syntax.Sub $1 $3 }

p_factor :
  | p_atom               { $1 }
