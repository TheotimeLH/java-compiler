open Ast

(* On garde jtype et ntype *)
(* On garde les positions avec desc pour pouvoir la donner *)

module IdSet = Set.Make(String)

type ty_methode = 
  {nom : ident ;
  typ : jtype desc option ;
  types_params : jtype desc list}

module Methode = struct
  type t = ty_methode
  let compare m1 m2 = Stdlib.compare m1.nom m2.nom
  let equal m1 m2 = m1.nom = m2.nom
end

module MethSet = Set.Make(Methode)

module Ntype = struct
  type t = ntype 
end

module NtypeSet = Set.Make(Ntype)
