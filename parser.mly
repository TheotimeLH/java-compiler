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
	| l=class_intf* ; cm=class_Main ; EOF { { intfs=l ; main=cm } }

class_intf:
	| CLASS ; id=IDENT ; pt=paramstype? ; ext=extends1? ;	imp=implements?	; LAC ; d=decl* ; RAC
		{ Class { nom=id ; params=pt ; extd=ext ; implmts=imp ; body=d } }
	| INTERFACE ; id=IDENT ; pt=paramstype? ;	ext=extends2? ;	LAC ; p=pro* ; RAC 
		{ Interface { nom=id ; params=pt ; extds=ext ; body=p } }

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
	| id=IDENT ; l=extends3 { { nom=id ; extds=l } }
extends3:
	|EXTENDS ; l=seperated_nonempty_list(ESP,ntype) { l }

decl:
	| t=typ ;  id=ident ; PVIRG { Dvar(t,id) }
	| c=constructeur 						{ Dconstr c }
	| m=methode 								{ Dmeth m }

constructeur:
	| id=IDENT ; LPAR ; par=separated_list(VIRG,parametre) ; RPAR ; LAC ; ins=instruction* ; RAC
		{ { nom=id ; params=par ; body=ins } }

methode:
	| p=proto ; LAC ; l=instruction* ; RAC { { info=p ; body=l } }

proto:
	| b=public ; t=type_void ; id=IDENT ; LPAR ; l=seperated_list(VIRG,parametre) ; RPAR
		{ { public=b ; typ=t ; nom=id ; params=l } }
public:
	| 				{ false }
	| PUBLIC 	{ true }
type_void:
	| Void 	{ None }
	| t=typ { Some t }

parametre:
	| t=typ ; id=IDENT { { typ=t ; nom=id } }

typ: 
	| BOOLEAN 	{ Jboolean }
	| INT 			{ Jint }
	| nt=ntype 	{ Jntype nt }

ntype:
	| id=IDENT ; LT ; l=seperated_nonempty_list(ntype) ; GT
							{ Ntype(id,l) }
	| id=IDENT	{ Ntype(id,[]) }

class_main: /* nécessairement la dernière class */
	| CLASS ; m=IDENT ; LAC ; PUBLIC ; STATIC ; VOID ;
		n=IDENT ; LPARs ; tr=IDENT ; LCRO ; RCRO ;
		id=IDENT ; LAC ; l=instruction* ; RAC ; RAC
		{ if m = "Main" && n = "main" && str = "String"
		then { nom=id ; body=l } else failwith "error 404" }

expr:
	| NULL 															{ Enil }
	| es=expr_simple 										{ Esimple es }
	| a=acces ; EQUAL ; e=expr 					{ Eequal(a,e) }
	| NOT ; e=expr 											{ Eunop(Unot,e) }
	| MINUS ; e=expr %prec UNMIN 				{ Eunop(Uneg,e) }
	| e1=expr ; op=operateur ; e2=expr	{ Ebinop(e1,op,e2) }
	
acces:
	| id=IDENT 												{ Aident id }
	| es=expr_simple ; DOT ; id=IDENT { Achemin(es,id) }

expr_simple:
	| n=CONST 							{ ESint n }
	| s=STR 								{ ESstr s }
	| b=BOOL 								{ ESbool b }
	| THIS 									{ ESthis }
	| LPAR ; e=expr ; RPAR	{ ESexpr e }
	| NEW ; nt=ntype ; LPAR ; l=seperated_list(VIRG,expr) ; RPAR 
													{ ESnew(nt,l) }
	| a=acces ; LPAR ; l=seperated_list(VIRG,expr) ; RPAR
													{ ESacces(a,l) }
	| a=acces 							{ ESacces a }

%inline operateur:
	| x=EQU | x=CMP | x=RING 	{ binop x }
	| LT 											{ binop Blt }
	| GT 											{ binop Bgt }
	| PLUS 										{ Badd }
	| MINUS 									{ Bsub }
	| AND 										{ Band }
	| OR 											{ Bor }

instruction:
	| PVIRG																						{ Inil }
	| es=expr_simple ; PVIRG													{ Isimple es }
	| a=acces ; EQUAL ; e=expr ; PVIRG 								{ Idef(a,e) }
	| t=typ ; id=IDENT ; PVIRG 												{ Iinit(t,id) }
	| t=typ ; id=IDENT ; EQUAL ; e=expr ; PVIRG				{ Iinit_def(t,id,e) }
	| IF ; LPAR ; e=expr ; RPAR ; ins=instruction 		{ Iif(e,ins,Inil) }
	| IF ; LPAR ; e=expr ; RPAR ; i1=instruction ; ELSE ; i2=instruction
																										{ Iif(e,i1,i2) }
	| WHILE ; LPAR ; e=expr ; RPAR ; ins=instruction	{ Iwhile(e,ins) }
	| LAC ; l=instruction* ; RAC 											{ Ibloc l}
	| RETURN ; e=expr? ; PVIRG												{ Ireturn e }
