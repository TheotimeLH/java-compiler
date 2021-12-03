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
  let rec equal (Ntype (id1,l1)) (Ntype (id2,l2)) =
    try
      (id1=id2) &&
      (List.for_all2 
        (fun {desc = n1'} {desc = n2'} -> equal n1' n2')
        l1 l2 )
    with
      | Invalid_argument -> false
      
end

module NtypeSet = Set.Make(Ntype)
