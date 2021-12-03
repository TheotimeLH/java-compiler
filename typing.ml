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
  
  
  (* ===== TOUT POUR LES INTERFACES ===== *)
  (* On doit vérifier les héritages : si on demande une méthode, déjà présente dans 
     une sur-interface, on doit demander le même type.
     On doit vérifier que les types demandées sont bien fondés.  
     
     MAIS POUR VERIFIER BIEN FONDÉ, IL FAUT VÉRIFIER LES RELATIONS
     ON NOUS ANNONCE A extends/implements B, on le croit *)
  let intf_meth = Hashtbl.create 5 in

  let fait_intf {nom ; params ; extds ; body} =
    in
  (* Attention, là on utilise les relations, on ne les vérifie pas *)
  

  let sous_type jtyp1 jtyp2 = match jtyp1,jtyp2 with
    | Jtypenull,_ 
    | Jboolean,Jboolean | Jint,Jint -> true
    | Jntype {desc1},Jntype {desc2} when desc1 = desc2 -> true
    | Jntype { 
    

  let rec sous_ci ntyp1 ntyp2 env_typage = (* ~ extends généralisé *)
    (* Attention, on passe par un env, car on peut avoir id1 = T paramtype *)
    let Ntype (id1,l_ntyp1) = ntyp1.desc in
    let Ntype (id2,l_ntyp2) = ntyp2.desc in
    if not Hashtbl.mem env_typage.heritage id1 
      then raise (Typing_error {loc = ntyp1.loc ;
        msg = "Classe ou interface inconnue dans le contexte"}) ;
    let precs1 = Hashtbl.find env_typage.heritage id1 in 
    if node_ci = node_obj then id2 = "Object"
    else 
      List.exists (fun nty ->) node_ci.prec 
        



  let rec implem_bien c i =
    c <> "Object" &&
    ((NtypeSet.mem i (Hashtbl.find c_implems c))
    || (let node_c = Hashtbl.find graph_c c in
      implem_bien (List.hd node_c.prec).id i

        
    
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
  

        




