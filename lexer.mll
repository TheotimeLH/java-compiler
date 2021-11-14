(* Lexer *)

{
	open Lexing
	open Parser
	open Location	

	exception Error of loc * string
	exception Non_fini

	let id_or_keyword = 
		let keywords = Hashtbl.create 18 in
		List.iter (fun (s,t) -> Hashtbl.add keywords s t)
			["boolean",BOOLEAN ;	"class",CLASS ;	"else",ELSE ;
			"extends",EXTENDS ;	"false",FALSE ;	"if",IF	;
			"implements",IMPLEMENTS ;	"int",INT ;	"interface"INTERFACE ;
			"new",NEW ;	"null",NULL ;	"public",PUBLIC ;	"return",RETURN;
			"static",STATIC ;	"this",THIS ;	"true",TRUE ;
			"void",VOID ;	"while",WHILE]	;
		fun s -> try Hashtbl.find s keywords with Not_Found -> IDENT s
	
	let string_buffer = Buffer.create 1024 
	
}

let chiffre = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = (alpha | _) (alpha | chiffre | _)*
let entier = 0 | '1'-'9' chiffre*
let comment_line = "//" [^'\n']*

rule token = parse
	|	[' ' '\t']+ | comment_line  {token lexbuf}
	| '\n' {new_line lexbuf ; token lexbuf}
	| "/*" {let pos_debut = Location.curr lexbuf in
			try comment lexbuf 
			with Non_fini -> 
				raise (Error(pos_debut,"commentaire non fini"))}
	| '"'	{let pos_debut = Location.curr lexbuf in
			try STR (chaine lexbuf)
			with Non_fini -> 
				raise (Error(pos_debut,"chaine de caractères non finie"))}
	| entier as s -> {}

and chaine = parse
	| '"' {let s = Buffer.contents string_buffer in
				Buffer.reset string_buffer; s}
	|	"\\n" {Buffer.add_char string_buffer '\n';
				chaine lexbuf}
	| "\\\"" {Buffer.add_char string_buffer '"';
        chaine lexbuf}
	| "\\\\" {Buffer.add_char string_buffer '\\';
        chaine lexbuf}
	| '\\' {raise Error(Location.curr lexbuf,
			"LEXICAL : pas de \\ autre que \\n etc")}
	|	'\n' {raise Error(Location.curr lexbuf,
			"LEXICAL : pas de retour à la ligne dans une chaine de caractère !") }
	| _ as c {Buffer.add_char string_buffer c;
        chaine lexbuf}
	| eof {raise Non_fini}


and comment = parse
  | "*/" {token lexbuf}
	| '\n' {new_line lexbuf ; comment_lexbuf}
  | _  {comment lexbuf}
  | eof {raise Non_fini}




