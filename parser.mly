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
%token EQUAL LT GT
%token OR AND NOT
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
%start fichier

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <Ast.fichier> fichier

%%

fichier:
	| l=class_intf* ; cm=class_Main ; EOF { l, cm }

class_intf:
	| CLASS ; id=IDENT ; pt=paramstype? ; ext=extends1? ;	imp=implements?	; LAC ; d=decl* ; RAC
		{ id, pt, ext, imp, d }
	| INTERFACE ; id=IDENT ; pt=paramstype? ;	extextends2? ;	LAC ; pr=pro* ; RAC 
		{ id, pt, ext, pr }

extends1:
	| EXTENDS ; nt=ntype { nt }
implements:
	|IMPLEMENTS ; l=seperated_nonempty_list(VIRG,ntype) { l }
extends2:
	|EXTENDS ; l=seperated_nonempty_list(VIRG,ntype) { l }
pro: 
	| p=proto ; PVIRG { p }

paramstype:
	| LT ; l=seperated_nonempty_list(VIRG,paramtype) ; GT { l }

paramtype:
	| id=IDENT ; l=extends3 { l }
extends3:
	|EXTENDS ; l=seperated_nonempty_list(ESP,ntype) { l }

decl:
	| t=typ ;  id=ident ; PVIRG { t, id }
	| c=constructeur { c }
	| m=methode { m }

constructeur:
	| id=IDENT ; LPAR ; par=separated_list(VIRG,parametre) ; RPAR ; LAC ; ins=instruction* ; RAC
		{ id, par, ins }

methode:
	| pro=proto ; LAC ; ins=instruction* ; RAC { pro; ins }

proto:
	| PUBLIC? ; t=typ ; id=IDENT ; LPAR ; l=seperated_list(VIRG,parametre) ; RPAR
		{ t, id, l }
	| PUBLIC? ; VOID; id=IDENT ; LPAR ; l=seperated_list(VIRG,parametre) ; RPAR
		{ id, l }

parametre: t=typ ; id=IDENT { t, id }

typ: 
	| BOOLEAN { jtype Jboolean }
	| INT { jtype Jint }
	| nt=ntype { nt }

ntype:
	| id=IDENT ; nt=ntype_aux? { id, nt }
ntype_aux:
	| LT ; l=seperated_nonempty_list(ntype) ; GT { l }

class_main: /* nécessairement la dernière class */
	| CLASS ; m=IDENT ; LAC ; PUBLIC ; STATIC ; VOID ;
		n=IDENT ; LPARs ; tr=IDENT ; LCRO ; RCRO ;
		id=IDENT ; LAC ; l=instruction* ; RAC ; RAC
		{ if m = "Main" && n = "main" && str = "String"
		then id, l else failwith "error 404" }


