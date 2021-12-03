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
%token STATIC THIS VOID WHILE

/* Priorités et associativités des tokens */

%right EQUAL
%left OR
%left AND
%left EQU
%left CMP LT GT
%left PLUS MINUS
%left RING
%right UNMIN NOT
%nonassoc IF
%nonassoc ELSE

/* Point d'entrée de la grammaire */
%start fichier

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <Ast.fichier> fichier

%%

fichier: c=class_intf+ ; EOF
		{ let rec aux l = match l with
				|[{desc=Main _}] -> l
				|{desc=Main _}::_ -> raise (Parser_error "classe Main avant la fin")
				|_::q -> aux q
				|[] -> raise (Parser_error "aucune classe Main")
			in aux c }
        
class_intf:
	| CLASS ; id=IDENT ; pt=paramstype ; ext=extends ; imp=implements ; LAC ; d=decl* ; RAC
		{ { loc=$startpos,$endpos ; desc = Class { nom=id ; params=pt ; extd=ext ; implmts=imp ; body=d } } }
	| INTERFACE ; id=IDENT ; pt=paramstype ;
		ext=loption(preceded(EXTENDS,separated_nonempty_list(VIRG,ntype))) ;
		LAC ; p=terminated(proto,PVIRG)* ; RAC 
		{ { loc=$startpos,$endpos ; desc = Interface { nom=id ; params=pt ; extds=ext ; body=p } } }
	| CLASS ; m=IDENT ; LAC ; PUBLIC ; STATIC ; VOID ; n=IDENT ; LPAR ;
	 	str=IDENT ; LCRO ; RCRO ; IDENT ; RPAR ; LAC ; l=instruction* ; RAC ; RAC
		{ if m = "Main" && n = "main" && str = "String"
			then { loc=$startpos,$endpos ; desc = Main l }
			else raise (Parser_error "classe Main non reconnue") }

%inline extends:
	| 										{ None }
	| EXTENDS ; nt=ntype 	{ Some nt }

%inline implements:
	| IMPLEMENTS ; l=separated_nonempty_list(VIRG,ntype)
		{ l }
	| { [] }

%inline paramstype:
	| LT ; l=separated_nonempty_list(VIRG,paramtype) ; GT
		{ l }
	| { [] }

paramtype:
	| id=IDENT ; l=loption(preceded(EXTENDS,separated_nonempty_list(ESP,ntype)))
		{ { loc=$startpos,$endpos ; desc = { nom=id ; extds=l } } }

decl:
	| t=typ ;  id=IDENT ; PVIRG { { loc=$startpos,$endpos ; desc = Dvar(t,id) } }
	| c=constructeur 						{ { loc=$startpos,$endpos ; desc = Dconstr c } }
	| m=methode 								{ { loc=$startpos,$endpos ; desc = Dmeth m } }

constructeur:
	| id=IDENT ; LPAR ; par=separated_list(VIRG,parametre) ; RPAR ; LAC ; ins=instruction* ; RAC
		{ { loc=$startpos,$endpos ; desc = { nom=id ; params=par ; body=ins } } }

methode:
	| p=proto ; LAC ; l=instruction* ; RAC
		{ { loc=$startpos,$endpos ; desc = { info=p ; body=l } } }

proto:
        | VOID ; id=IDENT ; LPAR ; l=separated_list(VIRG,parametre) ; RPAR
		{ { loc=$startpos,$endpos ; desc = { typ=None ; nom=id ; params=l } } }
	| t=typ ; id=IDENT ; LPAR ; l=separated_list(VIRG,parametre) ; RPAR
		{ { loc=$startpos,$endpos ; desc = { typ=Some t ; nom=id ; params=l } } }
	| PUBLIC ; VOID ; id=IDENT ; LPAR ; l=separated_list(VIRG,parametre) ; RPAR
		{ { loc=$startpos,$endpos ; desc = { typ=None ; nom=id ; params=l } } }
	| PUBLIC ; t=typ ; id=IDENT ; LPAR ; l=separated_list(VIRG,parametre) ; RPAR
		{ { loc=$startpos,$endpos ; desc = { typ=Some t ; nom=id ; params=l } } }

parametre:
	| t=typ ; id=IDENT { { loc=$startpos,$endpos ; desc = { typ=t ; nom=id } } }

typ: 
	| BOOLEAN 	{ { loc=$startpos,$endpos ; desc = Jboolean } }
	| INT 			{ { loc=$startpos,$endpos ; desc = Jint } }
	| nt=ntype 	{ { loc=$startpos,$endpos ; desc = Jntype nt } }

ntype:
	| id=IDENT ; LT ; l=separated_nonempty_list(VIRG,ntype) ; GT
							{ { loc=$startpos,$endpos ; desc = Ntype (id,l) } }
	| id=IDENT	{ { loc=$startpos,$endpos ; desc = Ntype (id,[]) } }

expr:
	| NULL 															{ { loc=$startpos,$endpos ; desc = Enil } }
	| es=expr_simple 										{ { loc=$startpos,$endpos ; desc = Esimple es } }
	| a=acces ; EQUAL ; e=expr 					{ { loc=$startpos,$endpos ; desc = Eequal(a,e) } }
	| NOT ; e=expr 											{ { loc=$startpos,$endpos ; desc = Eunop(Unot,e) } }
	| MINUS ; e=expr %prec UNMIN 				{ { loc=$startpos,$endpos ; desc = Eunop(Uneg,e) } }
	| e1=expr ; op=operateur ; e2=expr	{ { loc=$startpos,$endpos ; desc = Ebinop(e1,op,e2) } }
	
acces:
	| id=IDENT 												{ { loc=$startpos,$endpos ; desc = Aident id } }
	| es=expr_simple ; DOT ; id=IDENT { { loc=$startpos,$endpos ; desc = Achemin(es,id) } }

expr_simple:
	| n=CONST 							{ { loc=$startpos,$endpos ; desc = ESint n } }
	| s=STR 								{ { loc=$startpos,$endpos ; desc = ESstr s } }
	| b=BOOL 								{ { loc=$startpos,$endpos ; desc = ESbool b } }
	| THIS 									{ { loc=$startpos,$endpos ; desc = ESthis } }
	| LPAR ; e=expr ; RPAR	{ { loc=$startpos,$endpos ; desc = ESexpr e } }
	| NEW ; nt=ntype ; LPAR ; l=separated_list(VIRG,expr) ; RPAR 
													{ { loc=$startpos,$endpos ; desc = ESnew(nt,l) } }
	| a=acces ; LPAR ; l=separated_list(VIRG,expr) ; RPAR
													{ { loc=$startpos,$endpos ; desc = ESacces(a,l) } }
	| a=acces 							{ { loc=$startpos,$endpos ; desc = ESacces(a,[]) } }

%inline operateur:
	| x=EQU | x=CMP | x=RING 	{ x }
	| LT 											{ Blt }
	| GT 											{ Bgt }
	| PLUS 										{ Badd }
	| MINUS 									{ Bsub }
	| AND 										{ Band }
	| OR 											{ Bor }

instruction:
	| PVIRG 																					{ { loc=$startpos,$endpos ; desc = Inil } }
	| es=expr_simple ; PVIRG													{ { loc=$startpos,$endpos ; desc = Isimple es } }
	| a=acces ; EQUAL ; e=expr ; PVIRG 								{ { loc=$startpos,$endpos ; desc = Idef(a,e) } }
	| t=typ ; id=IDENT ; PVIRG 												{ { loc=$startpos,$endpos ; desc = Iinit(t,id) } }
	| t=typ ; id=IDENT ; EQUAL ; e=expr ; PVIRG				{ { loc=$startpos,$endpos ; desc = Iinit_def(t,id,e) } }
	| IF ; LPAR ; e=expr ; RPAR ; i1=instruction ; ELSE ; i2=instruction
																										{ { loc=$startpos,$endpos ; desc = Iif(e,i1,i2) } }
	| IF ; LPAR ; e=expr ; RPAR ; ins=instruction	%prec IF
																										{ { loc=$startpos,$endpos ; desc = Iif(e,ins,{ loc=
																												Lexing.dummy_pos,Lexing.dummy_pos ; desc=Inil } ) } }
	| WHILE ; LPAR ; e=expr ; RPAR ; ins=instruction	{ { loc=$startpos,$endpos ; desc = Iwhile(e,ins) } }
	| LAC ; l=instruction* ; RAC											{ { loc=$startpos,$endpos ; desc = Ibloc l } }
	| RETURN ; e=expr? ; PVIRG												{ { loc=$startpos,$endpos ; desc = Ireturn e } }
