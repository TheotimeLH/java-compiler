open Ast

(* === Pour les tris topologiques === *)
type mark = NotVisited | InProgress | Visited
type node = { id : ident ; mutable mark : mark ;
  mutable prec : node list ; mutable succ : node list}


(* === Ensemble d'identifiants === *)
module IdSet = Set.Make(String)

(* === Pour les accès === *)
type info_constr = param desc list

type info_methode = 
  { nom : ident ;
  typ : jtype desc option ; (* car potentiellement void *)
  types_params : jtype desc list ;
  id_ci : ident }
type methtab = (ident , info_methode) Hashtbl.t

type info_champ = {nom : ident ; typ : jtype desc ; id_c : ident}
type chtab = (ident, info_champ) Hashtbl.t
(* Pendant la phase de vérification du typage, on n'a pas besoin des corps,
   c'est seulement au moment de la vérification de ceux-ci qu'on produit un 
   nouvel arbre de syntaxe, destiné au producteur de code *)
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
  let rec to_str (ntd : ntype desc) = match ntd.desc with
    |Ntype(id,[]) -> id
    |Ntype(id,l) -> id^"<"^(String.concat "," (List.map to_str l) )^">"
end

let jtype_equal jty1 jty2 = match jty1,jty2 with
  | Jtypenull,Jtypenull | Jint,Jint | Jboolean,Jboolean -> true
  | Jntype dn1,Jntype dn2 -> Ntype.equal dn1.desc dn2.desc 
  | _,_ -> false

let str_of_jtp jtp = match jtp with
  |Jtypenull -> "typenull"
  |Jint -> "int"
  |Jboolean -> "boolean"
  |Jntype ntd -> Ntype.to_str ntd

let str_of_jo = function
  |None -> "Void"
  |Some jt -> str_of_jtp jt

let str_of_djo (typ : jtype desc option) = match typ with
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
  mutable methodes : (ident, methtab) Hashtbl.t ;
  (* Pour une classe : les méthodes possédées,
     Pour une interface : les méthodes demandées,
     Pour un paramtype : les méthodes nécessairement possédées
     i.e. héritées via les contraintes, si T extends C & I1 & I2 etc
     alors T possède toutes les méthodes de C, mais aussi toutes celles
     demandées par les I. *) 
  mutable champs : (ident, chtab) Hashtbl.t ; (* idem *)
  tab_loc : (ident, localisation) Hashtbl.t
}

(* === Informations temporaires pour trier les paramstype === *)
type info_paramtype_tmp = {
  mutable tk_mark : mark ;
  tk_loc : localisation ;
  tk_contraintes : ntype desc list
}

(* === Pour les env_var === *)
module IdMap = Map.Make(String)
type info_var = {jt : jtype ; init : bool } 
type env_vars = info_var IdMap.t

type nom_var =
  | Muet
  | New
  | Nom of ident
