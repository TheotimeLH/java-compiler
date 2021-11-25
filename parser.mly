/* Parser */

%{
	open Ast
	exception Parser_error of String
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

fichier:
	| c = class_+ ; EOF
		{ let rec aux l = match l with
				|[{desc=Main _}] -> l
				|{desc=Main _}::_ -> raise (Parser_error "classe Main avant la fin")
				|_::q -> aux q
				|[] -> raise (Parser_error "pas de classe Main")
			in aux c }
        
class_:
	| CLASS ; id=IDENT ; pt=paramstype ; ext=extends ; imp=implements; LAC ; d=decl* ; RAC
		{ { loc=$starpos,$endpos ; desc = Class { nom=id ; params=pt ; extd=ext ; implmts=imp ; body=d } } }
	| INTERFACE ; id=IDENT ; pt=paramstype ;
		ext=loption(preceded(EXTENDS,separated_nonempty_list(VIRG,ntype))) ;
		LAC ; p=terminated(proto,PVIRG)* ; RAC 
		{ { loc=$starpos,$endpos ; desc = Interface { nom=id ; params=pt ; extds=ext ; body=p } } }
	| CLASS ; m=IDENT ; LAC ; PUBLIC ; STATIC ; VOID ; n=IDENT ; LPAR ;
	 	str=IDENT ; LCRO ; RCRO ; id=IDENT ; LAC ; l=instruction* ; RAC ; RAC
		{ if m = "Main" && n = "main" && str = "String"
			then { loc=$starpos,$endpos ; desc = Main { nom=id ; body=l } }
			else raise (Parser_error "classe Main non reconnue") }

%inline extends:
	| 											{ None }
	| ext= EXTENDS ; ntype 	{ Some ext }

%inline implements:
	| imp= IMPLEMENTS ; separated_nonempty_list(VIRG,ntype)
		{ Some imp }
	| { None }

%inline paramstype:
	| LT ; l=separated_nonempty_list(VIRG,paramtype) ; GT
		{ Some l }
	| { None }

paramtype:
	| id=IDENT ; l=loption(preceded(EXTENDS,separated_nonempty_list(ESP,ntype)))
		{ { loc=$starpos,$endpos ; desc = { nom=id ; extds=l } } }

decl:
	| t=typ ;  id=IDENT ; PVIRG { { loc=$starpos,$endpos ; desc = Dvar(t,id) } }
	| c=constructeur 						{ { loc=$starpos,$endpos ; desc = Dconstr c } }
	| m=methode 								{ { loc=$starpos,$endpos ; desc = Dmeth m } }

constructeur:
	| id=IDENT ; LPAR ; par=separated_list(VIRG,parametre) ; RPAR ; LAC ; ins=instruction* ; RAC
		{ { loc=$starpos,$endpos ; desc = { nom=id ; params=par ; body=ins } } }

methode:
	| p=proto ; LAC ; l=instruction* ; RAC
		{ { loc=$starpos,$endpos ; desc = { info=p ; body=l } } }

proto:
	| b=pblc ; VOID ; id=IDENT ; LPAR ; l=separated_list(VIRG,parametre) ; RPAR
		{ { loc=$starpos,$endpos ; desc = { public=b ; typ=None ; nom=id ; params=l } } }
	| b=pblc ; t=typ ; id=IDENT ; LPAR ; l=separated_list(VIRG,parametre) ; RPAR
		{ { loc=$starpos,$endpos ; desc = { public=b ; typ=Some t ; nom=id ; params=l } } }

%inline pblc:
        |       	{ false }
        | PUBLIC	{ true }

parametre:
	| t=typ ; id=IDENT { { loc=$starpos,$endpos ; desc = { typ=t ; nom=id } } }

typ: 
	| BOOLEAN 	{ { loc=$starpos,$endpos ; desc = Jboolean } }
	| INT 			{ { loc=$starpos,$endpos ; desc = Jint } }
	| nt=ntype 	{ { loc=$starpos,$endpos ; desc = Jntype nt } }

ntype:
	| id=IDENT ; LT ; l=separated_nonempty_list(VIRG,ntype) ; GT
							{ { loc=$starpos,$endpos ; desc = Ntype(id,l) } }
	| id=IDENT	{ { loc=$starpos,$endpos ; desc = Ntype(id,[]) } }

expr:
	| NULL 															{ { loc=$starpos,$endpos ; desc = Enil } }
	| es=expr_simple 										{ { loc=$starpos,$endpos ; desc = Esimple es } }
	| a=acces ; EQUAL ; e=expr 					{ { loc=$starpos,$endpos ; desc = Eequal(a,e) } }
	| NOT ; e=expr 											{ { loc=$starpos,$endpos ; desc = Eunop(Unot,e) } }
	| MINUS ; e=expr %prec UNMIN 				{ { loc=$starpos,$endpos ; desc = Eunop(Uneg,e) } }
	| e1=expr ; op=operateur ; e2=expr	{ { loc=$starpos,$endpos ; desc = Ebinop(e1,op,e2) } }
	
acces:
	| id=IDENT 												{ { loc=$starpos,$endpos ; desc = Aident id } }
	| es=expr_simple ; DOT ; id=IDENT { { loc=$starpos,$endpos ; desc = Achemin(es,id) } }

expr_simple:
	| n=CONST 							{ { loc=$starpos,$endpos ; desc = ESint n } }
	| s=STR 								{ { loc=$starpos,$endpos ; desc = ESstr s } }
	| b=BOOL 								{ { loc=$starpos,$endpos ; desc = ESbool b } }
	| THIS 									{ { loc=$starpos,$endpos ; desc = ESthis } }
	| LPAR ; e=expr ; RPAR	{ { loc=$starpos,$endpos ; desc = ESexpr e } }
	| NEW ; nt=ntype ; LPAR ; l=separated_list(VIRG,expr) ; RPAR 
													{ { loc=$starpos,$endpos ; desc = ESnew(nt,l) } }
	| a=acces ; LPAR ; l=separated_list(VIRG,expr) ; RPAR
													{ { loc=$starpos,$endpos ; desc = ESacces(a,l) } }
	| a=acces 							{ { loc=$starpos,$endpos ; desc = ESacces a } }

%inline operateur:
	| x=EQU | x=CMP | x=RING 	{ binop x }
	| LT 											{ binop Blt }
	| GT 											{ binop Bgt }
	| PLUS 										{ Badd }
	| MINUS 									{ Bsub }
	| AND 										{ Band }
	| OR 											{ Bor }

instruction:
	| PVIRG																						{ { loc=$starpos,$endpos ; desc = Inil } }
	| es=expr_simple ; PVIRG													{ { loc=$starpos,$endpos ; desc = Isimple es } }
	| a=acces ; EQUAL ; e=expr ; PVIRG 								{ { loc=$starpos,$endpos ; desc = Idef(a,e) } }
	| t=typ ; id=IDENT ; PVIRG 												{ { loc=$starpos,$endpos ; desc = Iinit(t,id) } }
	| t=typ ; id=IDENT ; EQUAL ; e=expr ; PVIRG				{ { loc=$starpos,$endpos ; desc = Iinit_def(t,id,e) } }
	| IF ; LPAR ; e=expr ; RPAR ; i1=instruction ; ELSE ; i2=instruction %prec IF
																										{ { loc=$starpos,$endpos ; desc = Iif(e,i1,i2) } }
	| IF ; LPAR ; e=expr ; RPAR ; ins=instruction	%prec IF
																										{ { loc=$starpos,$endpos ; desc = Iif(e,ins,{ loc=
																												Lexing.dummy_pos,Lexing.dummy_pos ; desc=Inil } ) } }
	| WHILE ; LPAR ; e=expr ; RPAR ; ins=instruction	{ { loc=$starpos,$endpos ; desc = Iwhile(e,ins) } }
	| LAC ; l=instruction* ; RAC											{ { loc=$starpos,$endpos ; desc = Ibloc l } }
	| RETURN ; e=expr? ; PVIRG												{ { loc=$starpos,$endpos ; desc = Ireturn e } }
