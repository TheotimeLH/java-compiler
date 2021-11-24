(* Syntaxe abstraite pour petit Java *)
type 'a desc = 
	{loc : Lexing.position * Lexing.position ; desc : 'a}

type ident = string

type ntype = Ntype of ident * ntype desc list

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
	|	Eequal of acces desc * expr
	|	Eunop of unop * expr desc 
	|	Ebinop of expr desc * binop * expr desc 

and acces = 
	|	Aident of ident
	|	Achemin of expr_simple desc * ident desc

and expr_simple =
	|	ESint of int	| ESstr of string	| ESbool of bool
	|	ESthis
	|	ESexpr of expr desc
	|	ESnew of ntype desc * expr desc list
	|	ESacces of acces desc * expr desc list

type instr = 
	| Inil
	|	Isimple of expr_simple desc
	|	Idef of acces desc * expr desc
	|	Iinit of jtype desc * ident
	|	Iinit_def of jtype desc * ident * expr desc
	|	Iif of expr desc * instr desc * instr desc
	|	Iwhile of expr desc * instr desc
	|	Ibloc of instr desc list
	| Ireturn of expr desc option

type param = {typ : jtype desc ; nom : ident}

type proto = 
	{public : bool ; typ : jtype desc option ;
	nom : ident ; params : param desc list}

type methode = {info : proto desc ; body : instr desc list}

type constructeur = 
	{nom : ident ; params : param desc list ; body : instr desc list}

type decl = 
	|	Dvar of jtype desc * ident desc	
	|	Dconstr of constructeur desc
	|	Dmeth of methode desc

type paramtype = {nom : ident ; extds : ntype desc list}

type classe = 
	| Class of {nom : ident ; params : paramtype desc list ;
				extd : ntype desc option ; implmts : ntype desc list ; body : decl desc list}
	|	Interface of {nom : ident ; params : paramtype desc list;
				extds : ntype desc list ; body : proto desc list}
	| Main of {nom : ident ; body : instr list} 

type fichier = classe desc list
