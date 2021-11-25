(* Lexer *)

{
	open Lexing
	open Parser

	type error = { loc = Lexing.position ; msg=String }
	exception Lexer_error of String
	exception Non_fini of error
	exception Interruption

	let id_or_keyword = 
		let keywords = Hashtbl.create 18 in
		List.iter (fun (s,t) -> Hashtbl.add keywords s t)
			[ "boolean",BOOLEAN ; "class",CLASS ;
				"else",ELSE ; "extends",EXTENDS ;
				"false",BOOL false ; "if",IF	;
				"implements",IMPLEMENTS ; "int",INT ;
				"interface"INTERFACE ; "new",NEW ;
				"null",NULL ; "public",PUBLIC ;
				"return",RETURN; "static",STATIC ;
				"this",THIS ; "true",BOOL true ;
				"void",VOID ; "while",WHILE ]	;
		fun s -> try Hashtbl.find s keywords with Not_Found -> IDENT s
	
	let string_buffer = Buffer.create 1024 	
}

let chiffre = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = (alpha | _) (alpha | chiffre | _)*
let entier = 0 | '1'-'9' chiffre*

rule token = parse
	|	[' ' '\t']+ | "//" [^'\n']*	{token lexbuf}
	| '\n' 	{ new_line lexbuf ; token lexbuf }
	| "/*"	{ let pos = lexbuf.lex_curr_p in
						try comment lexbuf with Interruption ->
						raise (Non_fini { loc=pos ; msg="commentaire non fermé" } ) }
	| '"'		{ let pos = lexbuf.lex_curr_p in
						try STR (chaine lexbuf) with Interruption -> 
						raise (Non_fini { loc=pos ; msg="chaîne de caractères non fermée" } ) }
	| entier as s -> 	{ try Const (int_of_string s) with _ ->
											raise (Lexer_error "entier trop grand") }
	|	ident as s -> 	{id_or_keyword s}
	| '=' 	{EQUAL}
	|	"||" 	{OR}
	|	"&&" 	{AND}
	| "==" 	{EQU Beq}
	| "!=" 	{EQU Bneq}	
	|	"<=" 	{CMP Ble}
	| ">=" 	{CMP Bge}
	|	'+' 	{PLUS}
	|	'-' 	{MINUS}
	|	'*' 	{RING Bmul}
	|	'/' 	{RING Bdiv}
	|	'%' 	{RING Bmod}
	|	'!' 	{NOT}
	| '.' 	{DOT}
	| '<' 	{LT}
	| '>' 	{GT}
	|	'(' 	{LPAR}
	|	')' 	{RPAR}
	|	'[' 	{LCRO}
	|	']' 	{RCRO}
	|	'{' 	{LAC}
	|	'}' 	{RAC}
	| ',' 	{VIRG}
	|	';' 	{PVIRG}
	|	'&' 	{ESP}


and chaine = parse
	| '"' 		{ let s = Buffer.contents string_buffer in
							Buffer.reset string_buffer ; s }
	|	"\\n" 	{ Buffer.add_char string_buffer '\n' ; chaine lexbuf }
	| "\\\"" 	{ Buffer.add_char string_buffer '"' ; chaine lexbuf }
	| "\\\\" 	{ Buffer.add_char string_buffer '\\' ; chaine lexbuf }
	| '\\' 		{ raise (Lexer_error "backslash illégal dans chaîne") }
	| '\n' 		{ raise (Lexer_error "retour chariot dans chaîne") }
	| _ as c 	{ Buffer.add_char string_buffer c ; chaine lexbuf }
	| eof 		{raise Interruption}


and comment = parse
  | "*/" 	{token lexbuf}
	| '\n' 	{ new_line lexbuf ; comment_lexbuf }
  | _  		{comment lexbuf}
  | eof 	{raise Interruption}
