/* Parser */

%{
	open Ast
%}

/* Déclaration des tokens */

%token EOF
%token <int> CONST
%token <string> IDENT
%token <bool> BOOL
%token <string> STR

%token BOOLEAN CLASS ELSE
%token EXTENDS FALSE IF
%token IMPLEMENTS INT INTERFACE
%token NEW NULL PUBLIC
%token RETURN STATIC THUS
%token TRUE VOID WHILE

/* Priorités et associativités des tokens */

