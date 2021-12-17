
(* Programme principal *)

open Lexing
open Format

let usage = "usage: pjava [options] file.java"

let parse_only = ref false
let type_only = ref false
let spec =
    [ "--parse-only" , Arg.Set parse_only , " stop after pasrsing" ;
      "--type-only", Arg.Set type_only , " stop after typing" ]

let file = ref ""
let () =
    Arg.parse spec (fun s -> file:=s) usage ;
    if !file = "" then (eprintf "erreur entrée: aucun fichier renseigné " ; exit 1) ;
    if not (Filename.check_suffix !file ".java")
    then (eprintf "erreur entrée: pas d'extension .java " ; exit 1)

let report (s,e) =
    let l = s.pos_lnum in
    let fc = s.pos_cnum - s.pos_bol + 1 in
    let lc = e.pos_cnum - s.pos_bol + 1 in
    eprintf "File \"%s\", line %d, characters %d-%d:\n" !file l fc lc

let () =
    let ch = open_in !file in
    let lb = Lexing.from_channel ch in
    let p = try Parser.fichier Lexer.token lb with
        | Lexer.Non_fini { loc=pos ; msg=s } ->
          report pos ;
          eprintf "erreur lexicale: %s@." s ;
          exit 1
        | Lexer.Lexer_error s ->
          report (lexeme_start_p lb,lexeme_end_p lb) ;
          eprintf "erreur lexicale: %s@." s ;
          exit 1
        | Ast.Parser_error s ->
          report (lexeme_start_p lb,lexeme_end_p lb) ;
          eprintf "erreur syntaxique: %s@." s ;
          exit 1
        | _ ->
          report (lexeme_start_p lb,lexeme_end_p lb) ;
          eprintf "erreur syntaxique: grammaire non reconnue@." ;
          exit 1
    in close_in ch ;
    if !parse_only then exit 0 ;
    
    let t = try Typing.type_fichier p with
        | Typing.Typing_error { loc=pos ; msg=s } ->
          report pos ;
          eprintf "erreur typage: %s@." s ;*
          exit 1 
    in
    if !type_only then exit 0 ;
    
    exit 0
