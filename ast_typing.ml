open Ast

(* On garde jtype et ntype *)
(* On garde les positions avec desc pour pouvoir la donner *)

module IdSet = Set.Make(String)

type ty_methode = 
  {nom : ident ;
  typ : jtype desc option ; (* car potentiellement void *)
  types_params : jtype desc list}

module Methode = struct
  type t = ty_methode
  let compare m1 m2 = Stdlib.compare m1.nom m2.nom
  let equal m1 m2 = m1.nom = m2.nom (* pas de surcharge ! *)
end

module MethSet = Set.Make(Methode)

module Ntype = struct
  type t = ntype
  let rec equal (Ntype (id1,l1)) (Ntype (id2,l2)) =
    try
      (id1=id2) &&
      (List.for_all2 
        (fun dn1' dn2' -> equal (dn1').desc (dn2').desc)
        l1 l2 )
    with
      | Invalid_argument _-> false
  let compare = Stdlib.compare
end

module NtypeSet = Set.Make(Ntype)

type env_typage = {
  mutable paramstype : IdSet.t ;
  mutable ci : IdSet.t ;
  mutable c : IdSet.t ;
  mutable i : IdSet.t ;
  mutable extends : (ident , ntype desc list) Hashtbl.t ;
  mutable implements : (ident , ntype desc list) Hashtbl.t ;
  mutable contraintes : (ident , ntype desc list) Hashtbl.t }

