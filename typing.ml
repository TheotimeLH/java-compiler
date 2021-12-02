(* J'ai besoin d'un graphe pour décrire les relations d'héritage entre les classes 
   et les interfaces. On fait un tri topologique (error si cycle) puis ensuite on va 
   vérifier les types en suivant ce tri topologique (qui a pour racine la classe
   Object, qui a au moins un fils String, ayant pour seule méthode equal).
   -> on en profite pour vérifier que chaque C/I n'est définie qu'une fois
   -> qu'on est sous-classe d'une classe existence (qui n'est pas String)
   -> idem pour I

   2) On reparcourt les C et les I dans l'ordre topo (d'abord les I ?):
       i) On commence par vérifier les paramtype (à partir des C_I déjà faits).
       On a surtout besoin de vérifier ce qui existe (si on a les bons champs, 
       les bonnes méthodes etc, si les redéfinitions sont correctes) et que tout
       est défini proprememnt (pas deux champs/meth même nom, exactement un 
       constructeur, au plus une méthode au nom de I etc).
       
       ii) Une fois qu'on a l'état des lieux (on est obligé de le faire en deux temps
       car l'ordre des déclarations n'importe pas) on vérifier que les corps des
       methodes et du constructeurs fait sens)
    
    Doit-on faire i) pour toutes les C/I avant de passer au ii) ? OUI
    car on peut utiliser les constructeurs des uns dans tous les autres, idem
    les méthodes).

   Pour l'env de typage globale :
       on a une Hashtbl : ident -> Set des méthodes * leurs types
       (celles demandées dans les interfaces, et celles faites dans les classes)
       de même Hashtbl : ident ->
   
   Comment marche les constructeurs de sous classes, on appelle le sur constructeur
   pour s'occuper de tous les champs de la sur-classe, puis après on s'occupe des
   nouveaux. Doit-on que le constructeur s'occupe de tous les champs ?
   Les méthodes sont tjr en public mais les déclarations de champ en privées
   par défaut ? (Donc on doit vérifier que si on demande qlqch il est en public.
   Sachant que ça permet de modifier un champ. Du genre dico.machin= 2).
   Dans le main, si au final tjr arg, on s'en fout ?
   Peut-on récupérer les déclarations au premier tour ? *)

open Ast
open Ast_typing

type error = { loc = Lexing.position * Lexing.position; msg = string }
exception Typing_error of error

type mark = NotVisited | InProgress | Visited
type node = { id : ident ; mutable mark : mark ;
  mutable prec : node list ; mutable succ : node list}

let type_fichier l_ci =
  (* ===== GRAPHES DES RELATIONS ENTRE LES C / LES I ===== *)
  (* On commence par récupérer toutes les relations, pour pouvoir traiter les I puis 
     les C dans un ordre topologique, on ne vérifie pas les paramstype par exemple.
     Attention ! Les ntype, peuvent cacher d'autres dépendances dans les types données
     pour les paramstype. *)
  let tab_pos_ci = Hashtbl.create 10 in
  let graph_c = Hashtbl.create 5 in
  let graph_i = Hashtbl.create 5 in
  
  (* === Ajout des noeuds === *)
  let node_obj = {id="Object" ; mark = NotVisited ; prec=[] ; succ=[]} in

  let graph_add_node ci = match ci.desc with
    | Class {nom} -> 
      Hashtbl.add tab_pos_ci nom ci.loc ;
      if Hashtbl.mem graph_c nom || Hashtbl.mem graph_i nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Deux classes/interfaces ont le même nom"})
      else if nom = "Main" 
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Une autre classe que la Main porte le nom Main"})
      else Hashtbl.add graph_c nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
    | Interface {nom} ->
      Hashtbl.add tab_pos_ci nom ci.loc ;
      if Hashtbl.mem graph_c nom || Hashtbl.mem graph_i nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Deux classes/interfaces ont le même nom"})
      else if nom = "Main" 
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Une interface porte le nom Main"})
      else Hashtbl.add graph_i nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
    | Main _ -> 
      Hashtbl.add tab_pos_ci "Main" ci.loc ; 
      (* tjr traitée dernière *)
  in
  List.iter graph_add_node l_ci ;
  
  (* === Ajout des relations === *)
  (* On ne regarde pas les relations C implements I, on va traiter les I avant *)
  let rec graph_add_rel g node_id1 nty =
    let (id2,params) = nty.desc in
    let node_id2 = Hashtbl.find g id2 in
    node_id1.prec <- node_id2 :: node_id1.prec ; 
    node_id2.succ <- node_id1 :: node_id2.succ ;
    List.iter (graph_add_rel g node_id1) params
  in
  let graph_add_vg ci = match ci.desc with
    | Class {nom ; extd=None} -> 
        let node_c = Hashtbl.find graph_c nom in
        node_c.prec <- [node_obj] ; (* Utile ? *)
        node_obj.succ <- node_c :: node_obj.succ
    | Class {nom ; extd=Some cp} -> 
        let node_id1 = Hashtbl.find graph_c nom in
        graph_add_rel g node_id1 cp
    | Interface {nom ; extds} ->
        let node_i = Hashtbl.find graph_i nom in
        List.iter (graph_add_rel g node_i) extds 
    | Main _ -> ()
  in
  List.iter graph_add_vg l_ci ;

  (* === Tri topologique === *)
  let l_tri = ref [] in
  let rec parcours n =
    if n.mark = NotVisited
    then (n.mark <- InProgress ;
      List.iter parcours n.prec ;
      n.mark <- Visited ;
      l_tri := n.nom :: !l_tri)
    else if n.mark = InProgress
    then raise (Typing_error {loc = Hashtbl.find tab_pos_ci n.nom ;
          msg = "Il y a un cycle dans les héritages !"})
  in
  parcours node_obj ;
  

  (* ===== VERIFICATIONS DE TOUTES LES DÉCLARATIONS ===== *)
  
  

        




