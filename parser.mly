/* Parser */

%{
	open Ast
%}

/* Déclaration des tokens */

%token EOF
%token <string> IDENT
%token <int> CONST
%token <bool> BOOL
%token <string> STR

%token <Ast.binop> CMP
%token <Ast.binop> RING
%token <Ast.binop> EQU
%token EQUAL OR AND NOT
%token PLUS MINUS DOT

%token LPAR LCRO LAC
%token RPAR RCRO RAC
%token VIRG PVIRG ESP

%token BOOLEAN CLASS ELSE EXTENDS
%token IF IMPLEMENTS INT INTERFACE
%token NEW NULL PUBLIC RETURN
%token STATIC THUS VOID WHILE

/* Priorités et associativités des tokens */

%right EQUAL
%left OR
%left AND
%left EQU
%left CMP
%left PLUS MINUS
%left RING
%right UNMIN NOT
%left DOT

/* Point d'entrée de la grammaire */
%start file

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <Ast.program> file

%%
