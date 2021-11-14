(* Syntaxe abstraite pour petit Java *)
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

type instruction = 
	| Inil
	|	Isimple of expr_simple
	|	Idef of acces * expr
	|	Iinit of jtype * ident
	|	Iinit_def of jtype * ident * expr
	|	Iif of expr * instruction * instruction
	|	Iwhile of expr * instruction
	|	Ibloc of instruction list
	| Ireturn of expression option

type param = jtype * ident

type secu = Public | NonPublic
type proto = secu * (jtype option) * ident * param list

type methode = proto * instruction list

type constructeur = ident * param list * instruction list

type decl = 
	|	Dvar of jtype * ident
	|	Dconstr of constructeur 
	|	Dmeth of methode

type paramtype = ident * ntype list

type paramstype

type classe_main = ident * instruction list 

type fichier = class_intf list * classe_main


