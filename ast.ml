(* Syntaxe abstraite pour petit Java *)
type 'a desc = 
	{loc : Location.position * Location.position ; desc : 'a}

type ident = string

type ntype = Ntype of ident * ntype list

type jtype = 
	|	Jboolean | Jint 
	| Jntype of ntype

type unop =
  | Uneg (* -e *)
  | Unot (* not e *)

type binop =
  | Badd | Bsub | Bmul | Bdiv | Bmod    (* + - * / % *)
  | Beq | Bneq | Blt | Ble | Bgt | Bge  (* == != < <= > >= *)
  | Band | Bor                          (* && || *)

type expr =
	|	Enil
	|	Esimple of expr_simple
	|	Eequal of acces * expr
	|	Eunop of unop * expr
	|	Ebinop of expr * binop * expr

and acces = 
	|	Aident of ident
	|	Achemin of expr_simple * ident

and expr_simple =
	|	ESint of int	| ESstr of string	| ESbool of bool
	|	ESthis
	|	ESexpr of expr
	|	ESnew of ntype * expr list
	|	ESacces of acces * expr list

type instr = 
	| Inil
	|	Isimple of expr_simple
	|	Idef of acces * expr
	|	Iinit of jtype * ident
	|	Iinit_def of jtype * ident * expr
	|	Iif of expr * instr * instr
	|	Iwhile of expr * instr
	|	Ibloc of instr list
	| Ireturn of expr option

type param = {typ : jtype ; nom : ident}

type proto = 
	{public : bool ; typ : jtype option ;
	nom : ident ; params : param list}

type methode = {info : proto ; body : instr list}

type constructeur = 
	{nom : ident ; params : param list ; body : instr list}

type decl = 
	|	Dvar of jtype * ident
	|	Dconstr of constructeur 
	|	Dmeth of methode

type paramtype = {nom : ident ; extds : ntype list}

type classe_intf = 
	| Class of {nom : ident ; params : paramtype list ;
				extd : ntype option ; implmts : ntype list ; body : decl list}
	|	Interface of {nom : ident ; params : paramtype list;
				extds : ntype list ; body : proto list}

type classe_main = {nom : ident ; body : instr list} 

type fichier = { intfs : classe_intf list ; main : classe_main}


