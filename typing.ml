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
       on a une Hashtbl : ident -> MethSet
       (celles demandées dans les interfaces, et celles faites dans les classes)
       de même Hashtbl : ident -> ChampSet 
       (utilisée uniquement pour les classes)
       
   
   Comment marche les constructeurs de sous classes, on appelle le sur constructeur
   pour s'occuper de tous les champs de la sur-classe, puis après on s'occupe des
   nouveaux. Doit-on que le constructeur s'occupe de tous les champs ?
   Les méthodes sont tjr en public mais les déclarations de champ en privées
   par défaut ? (Donc on doit vérifier que si on demande qlqch il est en public.
   Sachant que ça permet de modifier un champ. Du genre dico.machin= 2).
   Dans le main, si au final tjr arg, on s'en fout ?
   Peut-on récupérer les déclarations au premier tour ? 
   Que doit-on garder du typage ? *)

open Ast
open Ast_typing

type error = { loc : Lexing.position * Lexing.position; msg : string }
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
      else if nom = "Main" || nom = "Object" || nom = "String" 
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Deux classes Main ou Object ou String"})
      else Hashtbl.add graph_c nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
    | Interface {nom} ->
      Hashtbl.add tab_pos_ci nom ci.loc ;
      if Hashtbl.mem graph_c nom || Hashtbl.mem graph_i nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Deux classes/interfaces ont le même nom"})
      else if nom = "Main" || nom = "Object" || nom = "String"
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Une interface porte le nom Main, Object ou String"})
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
        node_c.prec <- [node_obj] ; 
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
  let rec parcours n l =
    if n.mark = NotVisited
    then (n.mark <- InProgress ;
      List.iter parcours n.prec l ;
      n.mark <- Visited ;
      l := n.nom :: !l)
    else if n.mark = InProgress
    then raise (Typing_error {loc = Hashtbl.find tab_pos_ci n.nom ;
          msg = "Il y a un cycle dans les héritages !"})
  in

  let list_cl = ref [] in
  parcours node_obj list_cl ;
  
  let list_intf = ref [] in
  Hashtbl.iter (fun i n -> parcours n list_intf) graph_i ;
  
  
  (* ===== Sous-type / Extends / Implements Généralisées  ===== *)
  (* ATTENTION, là on utilise les relations, on ne les vérifie pas *)
  
  (* === Pour les substitutions des paramstype avec sigma === *)
  let fait_sigma ci l_ntypes =
    let sigma = Hashtbl.create (List.length l_ntypes) in
    let l_params = Hashtbl.find ci_params ci in
    List.iter2 
      (fun param ntype -> Hashtbl.add sigma param.nom ntype) 
      l_params l_ntypes ;
    sigma
  in

  let rec substi_list sigma l_ntypes =
    List.map (fun {loc ; desc} -> {loc=loc  ; desc=substi sigma desc}) l_ntypes
  and substi sigma (Ntype (id,l)) =
    if Hashtbl.mem sigma id
      then Ntype( (Hashtbl.find sigma id), substi_list sigma l)
    else Ntype(id, substi_list sigma l)
  in 
 
  (* === Extends généralisée === *)
  let rec extends dci1 dci2 env_typage =
    (* Attention, on passe par un env, car on peut avoir id1 = T paramtype *)
    (dci1.desc = dci2.desc) || begin
    let Ntype (id1,l_ntypes1) = dci1.desc in
    let Ntype (id2,l_ntypes2) = dci2.desc in
    if not (IdSet.mem env_typage.ci id1)
      then raise (Typing_error {loc = dci1.loc ;
        msg = "Classe ou interface inconnue dans le contexte"}) ;
    if not (IdSet.mem env_typage.ci id2)
      then raise (Typing_error {loc = dci2.loc ;
        msg = "Classe ou interface inconnue dans le contexte"}) ;

    let l_precs1 = Hashtbl.find env_typage.extends id1 in
    let sigma = 
      if IdSet.mem env_typage.paramstype id1
      then Hashtbl.create 0 (* table de subsitution vide *)
      else fait_sigma id1 l_ntypes1
    in
    List.exists
      (fun dci -> extends dci dci2 env_typage)  
      (substi_list sigma l_precs1)
    end
  in

  (* === Implements généralisée === *)
  let rec implements dc di env_typage = 
    let Ntype (id_c,l_ntypes_c) = dc.desc in
    let Ntype (id_i,l_ntypes_i) = di.desc in
    if not (IdSet.mem env_typage.c id_c)
      then raise (Typing_error {loc = dc.loc ;
        msg = "Classe inconnue dans le contexte"}) ;
    if not (IdSet.mem env_typage.i id_i)
      then raise (Typing_error {loc = di.loc ;
        msg = "Interface inconnue dans le contexte"}) ;

    let l_implems = Hashtbl.find env_typage.implements id_c in
    let sigma = 
      if IdSet.mem env_typage.paramstype id_c
      then Hashtbl.create 0 (* table de subsitution vide *)
      else fait_sigma id_c l_ntypes_c
    in
    try
      let di' = List.find 
        (fun {desc = Ntype(id_i',_)} -> (id_i'=id_i))
        l_implems in
      let Ntype(id_i',l_ntypes_i') = di'.desc in
      (l_ntypes_i = substi_list sigma l_ntypes_i')
    with
      | Not_found ->
          let l_precs = Hashtbl.find env_typage.extends id_c in
          List.exists
            (fun dc' -> implements dc' di env_typage)
            (substi_list sigma l_precs)
            (* En soit il y a au plus une sur-classe *)
  in
      






 let sous_type jtyp1 jtyp2 = match jtyp1,jtyp2 with
    | Jtypenull,_ 
    | Jboolean,Jboolean | Jint,Jint -> true
    | Jntype {desc1},Jntype {desc2} when desc1 = desc2 -> true
    | Jntype { 


        
    
  let rec bf env_typage = function
    | Jboolean | Jint -> true
    | Jntype {loc ; desc = Ntype (id,ntl)} ->
        try 
          let paramstypes = Hashtbl.find ci_params id in
          let verifie theta {nom ; extds} =
            
            
          List.iter2 verifie ntl paramstypes ;
        with 
          | Not_found -> raise (Typing_error {loc=loc ;
              msg = "Classe ou Interface inconnue"})
          | Invalid_argument -> raise (Typing_error {loc=loc;
              msg = "Le nombre de ntypes donnés ne correspond pas au \
                  au nombre de paramtype de cette classe / interface"})


  (* ===== VERIFICATIONS DE TOUTES LES DÉCLARATIONS ===== *)
  

        




