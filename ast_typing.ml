open Ast

(* === Pour les tris topologiques === *)
type mark = NotVisited | InProgress | Visited
type node = { id : ident ; mutable mark : mark ;
  mutable prec : node list ; mutable succ : node list}


(* === Ensemble d'identifiants === *)
module IdSet = Set.Make(String)

(* === Pour les constructeurs === *)
type ty_const = param desc list
(* Pendant la phase de vérification du typage, on n'a pas besoin des corps,
   c'est seulement au moment de la vérification de ceux-ci qu'on produit un 
   nouvel arbre de syntaxe, destiné au producteur de code *)
(* === Pour les méthodes === *)
type ty_methode = 
  {nom : ident ;
  typ : jtype desc option ; (* car potentiellement void *)
  types_params : jtype desc list}

module Methode = struct
  type t = ty_methode
  let compare (m1:t) (m2:t) = Stdlib.compare m1.nom m2.nom
  let equal (m1:t) (m2:t) = m1.nom = m2.nom (* pas de surcharge ! *)
end
module MethSet = Set.Make(Methode)
(* ======================= *)

(* === Pour les champs === *)
type ty_champ = {nom : ident ; typ : jtype desc}
module Champ = struct
  type t = ty_champ
  let compare (ch1:t) (ch2:t) = Stdlib.compare ch1.nom ch2.nom
  let equal (ch1:t) (ch2:t) = ch1.nom = ch2.nom
end
module ChSet = Set.Make(Champ)
(* ======================= *)

(* === Pour les ntype / jtype === *)
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
  let rec to_str (ntd : ntype desc) = match ntd.desc with
    |Ntype(id,[]) -> id
    |Ntype(id,l) -> id^"<"^(String.concat "," (List.map to_str l) )^">"
end

module NtypeSet = Set.Make(Ntype)

let jtype_equal jty1 jty2 = match jty1,jty2 with
  | Jtypenull,Jtypenull | Jint,Jint | Jboolean,Jboolean -> true
  | Jntype dn1,Jntype dn2 -> Ntype.equal dn1.desc dn2.desc 

let str_of_jtp jtp = match jtp with
  |Jtypenull -> "typenull"
  |Jint -> "int"
  |Jboolean -> "boolean"
  |Jntype ntd -> Ntype.to_str ntd

let str_of_jtp_opt (typ : jtype desc option) = match typ with
  |None -> "Void"
  |Some jtp -> str_of_jtp jtp.desc
(* ======================= *)

(* === Les environnements de typage === *) 
type env_typage = {
  mutable paramstype : IdSet.t ;
  mutable ci : IdSet.t ;
  mutable c : IdSet.t ;
  mutable i : IdSet.t ;
  extends : (ident , ntype desc list) Hashtbl.t ;
  implements : (ident , ntype desc list) Hashtbl.t ;
  methodes : (ident, MethSet.t) Hashtbl.t ;
  (* Pour une classe : les méthodes possédées,
     Pour une interface : les méthodes demandées,
     Pour un paramtype : les méthodes nécessairement possédées
     i.e. héritées via les contraintes, si T extends C & I1 & I2 etc
     alors T possède toutes les méthodes de C, mais aussi toutes celles
     demandées par les I. *) 
  champs : (ident, ChSet.t) Hashtbl.t ; (* idem *)
  tab_loc : (ident, localisation) Hashtbl.t
}

(* === Informations temporaires pour trier les paramstype === *)
type info_paramtype_tmp = {
  mutable tk_mark : mark ;
  tk_loc : localisation ;
  tk_contraintes : ntype desc list
}
