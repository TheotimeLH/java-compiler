
(* Programme principal *)

open Lexing
open Parser
open Format

let usage = "usage: mini-java [options] file.java"

let parse_only = ref false
let type_only = ref false
let spec =
    [ "--parse-only" , Arg.set parse_only , " stop after pasrsing" ;
      "--type-only", Arg.set type_only , " stop after typing" ]

let file = ref ""
let () =
    Arg.parse spec (fun s -> file:=s) usage ;
    if !file = "" then raise (Arg.bad "aucun fichier renseigné")
    if not (Filename.check_suffix !file ".java")
    then raise (Arg.bad "pas d'extension .java")

let report (s,e) =
    let l = s.pos_lnum in
    let fc = s.pos_cnum - s.pos_bol + 1 in
    let lc = e.pos_cnum - s.pos_bol + 1 in
    eprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc

let () =
    let ch = open_in file in
    let lb = Lexing.from_channel ch in
    try
        let p = Parser.fichier Lexer.token lb in
        close_in ch ;
        if !parse_only then exit 0 ;
        let t = Typing.fichier p in
        if !type_only then exit 0 ;
        exit 0
    with
        | Lexer.Non_fini { loc=pos ; msg=s } ->
          report pos ;
          eprintf "erreur lexicale: %s@." s ;
          exit 1
        | Parser.Parser_error s ->
          report (lexeme_start_p lb,lexeme_end_p lb) ;
          eprintf "erreur syntaxique: %s@." s ;
          exit 1
        | Lexing.Lexer_error s ->
          report (lexeme_start_p lb,lexeme_end_p lb) ;
          eprintf "erreur lexicale: %s@." s ;
          exit 1
        | Typing.Type_error _ -> exit 1