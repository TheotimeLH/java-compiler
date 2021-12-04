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
       car l'ordre des déclarations n'importe pas) on vérifie que les corps des
       methodes et du constructeurs font sens)
    
    Doit-on faire i) pour toutes les C/I avant de passer au ii) ? OUI
    car on peut utiliser les constructeurs des uns dans tous les autres, idem
    les méthodes).
   
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
  let ci_params = Hashtbl.create 5 in
  (* liste des paramstype, seules les "vraies" ci en ont (ie pas les paramtype) *)
  let env_typage_global = {
    paramstype = IdSet.empty ; 
    ci = IdSet.empty ;
    c = IdSet.empty ; 
    i = IdSet.empty ;
    extends = Hashtbl.create 5 ;
    implements = Hashtbl.create 5 ;
    contraintes = Hashtbl.create 5 } in
  let new_ci nom =
    env_typage_global.ci <- IdSet.add nom env_typage_global.ci in
  let new_c nom =
    new_ci nom ;
    env_typage_global.c <- IdSet.add nom env_typage_global.c in
  let new_i nom =
    new_ci nom ;
    env_typage_global.i <- IdSet.add nom env_typage_global.i in

  env_typage_global.c <- IdSet.of_list ["Main";"Object";"String"] ;
  env_typage_global.ci <- env_typage_global.c ;
  

  (* === Ajout des noeuds === *)
  let node_obj = {id="Object" ; mark = NotVisited ; prec=[] ; succ=[]} in

  let graph_add_node ci = match ci.desc with
    | Class {nom ; params} ->
      Hashtbl.add ci_params nom params ;
      Hashtbl.add tab_pos_ci nom ci.loc ;

      if IdSet.mem env_typage_global.ci nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Nom de classe ou interface déjà utilisé."})
      else (
        Hashtbl.add graph_c nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
        new_c nom ;
    | Interface {nom ; params} ->
      Hashtbl.add ci_params nom params ;
      Hashtbl.add tab_pos_ci nom ci.loc ;

      if IdSet.mem env_typage_global.ci nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Nom de classe ou interface déjà utilisé."})
      else (
        Hashtbl.add graph_i nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
        new_i nom ;
    | Main _ -> 
      Hashtbl.add tab_pos_ci "Main" ci.loc ; 
      (* tjr traitée dernière *)
  in
  List.iter graph_add_node l_ci ;
  
  (* === Ajout des relations === *)
  (* Remarque : dans les graphes on ne regarde pas les relations C implements I, 
     car on va traiter les I avant. *)
  let dum = (Lexing.dummy_pos,Lexing.dummy_pos) in
  let dobj = {loc = dum; desc = Ntype ("Object",[])} in
  let init_extends id l =
    Hashtbl.add env_typage_global.extends id l in
  let init_implements id l =
    Hashtbl.add env_typage_global.implements id l in
  
  init_extends "String" [dobj] ;
  
  let rec graph_add_rel g node_id1 dn =
    let Ntype (id2,l_ntypes2) = dn.desc in
    let node_id2 = Hashtbl.find g id2 in
    node_id1.prec <- node_id2 :: node_id1.prec ; 
    node_id2.succ <- node_id1 :: node_id2.succ ;
    List.iter (graph_add_rel g node_id1) l_ntypes2
  in
  let graph_add_vg ci = match ci.desc with
    | Class {nom ; extd=None ; implmts = l} ->
        init_extends nom [dobj] ;
        init_implements nom l ;
        let node_c = Hashtbl.find graph_c nom in
        node_c.prec <- [node_obj] ; 
        node_obj.succ <- node_c :: node_obj.succ
    | Class {nom ; extd=Some cp} ->
        init_extends nom [cp] ; 
        init_implements nom l ;
        let node_id1 = Hashtbl.find graph_c nom in
        graph_add_rel graph_c node_id1 cp
    | Interface {nom ; extds = l} ->
        init_extends nom l ;
        let node_i = Hashtbl.find graph_i nom in
        List.iter (graph_add_rel graph_i node_i) extds 
    | Main _ -> ()
  in
  List.iter graph_add_vg l_ci ;

  (* === Tri topologique === *)
  let rec parcours l n =
    if n.mark = NotVisited
    then (n.mark <- InProgress ;
      List.iter (parcours l) n.prec ;
      n.mark <- Visited ;
      l := n.id :: !l)
    else if n.mark = InProgress
    then raise (Typing_error {loc = Hashtbl.find tab_pos_ci n.id ;
          msg = "Il y a un cycle dans les héritages !"})
  in

  let list_cl = ref [] in
  parcours list_cl node_obj ;
  
  let list_intf = ref [] in
  Hashtbl.iter (fun i n -> parcours list_intf n) graph_i ;
  
  
  (* ===== Sous-type / Extends / Implements Généralisées / Bien fondé ===== *)
  (* ATTENTION, là on utilise les relations, on ne les vérifie pas *)
  (* Les fonctions sont des tests, par exemple verifie_bf vérifie si un type est bien
     fondé, si c'est le cas le retour est unit, en revanche sinon on raise l'erreur
     et on peut ainsi localiser très proprement le problème.   *)

  (* === Pour les substitutions des paramstype avec sigma === *)
  let fait_sigma ci l_ntypes =
    let sigma = Hashtbl.create (List.length l_ntypes) in
    let l_params = Hashtbl.find ci_params ci in
    List.iter2 
      (fun (param : paramtype desc) (dn : ntype desc) -> 
        Hashtbl.add sigma (param.desc).nom dn.desc) 
      l_params l_ntypes ;
    sigma
  in

  let rec substi_list sigma l_ntypes =
    List.map (fun (dn : ntype desc) -> 
      {loc=dn.loc  ; desc=substi sigma dn.desc}) l_ntypes
  and substi sigma (Ntype (id,l)) =
    (* Soit on est un paramtype, on le change (d'ailleurs l=[])
       Soit on est un type construit, qui a des paramstypes
       necessairement on ne peut être un paramtype  *)
    if Hashtbl.mem sigma id
      then (Hashtbl.find sigma id)
    else Ntype(id, substi_list sigma l)
  in 
  (* ======================= *)
 
  (* === Extends généralisée === *)
  let rec extends dci1 dci2 env_typage =
    (* Attention, on passe par un env, car on peut avoir id1 = T paramtype *)
    (Ntype.equal dci1.desc dci2.desc)
    || 
    begin
    let Ntype (id1,l_ntypes1) = dci1.desc in
    let Ntype (id2,l_ntypes2) = dci2.desc in
    if not (IdSet.mem id1 env_typage.ci)
      then raise (Typing_error {loc = dci1.loc ;
        msg = "Classe ou interface inconnue dans le contexte"}) ;
    if not (IdSet.mem id2 env_typage.ci)
      then raise (Typing_error {loc = dci2.loc ;
        msg = "Classe ou interface inconnue dans le contexte"}) ;

    let l_precs1 = Hashtbl.find env_typage.extends id1 in
    let sigma = 
      if IdSet.mem id1 env_typage.paramstype
      then Hashtbl.create 0 (* table de subsitution vide *)
      else fait_sigma id1 l_ntypes1
    in
    List.exists
      (fun dci -> extends dci dci2 env_typage)  
      (substi_list sigma l_precs1)
    end
  in
  let verifie_extends dci1 dci2 env_typage = 
    if not (extends dci1 dci2 env_typage)
    then (let Ntype (id1,_) = dci1.desc in
      let Ntype (id2,_) = dci2.desc in
      raise (Typing_error {loc = dci1.loc ;
      msg = (Ntype.to_str dci1) ^ " n'est pas connu comme étendant " ^ (Ntype.to_str dci2) }))
  in
  (* ======================= *)

  (* === Implements généralisée === *)
  let rec implements dc di env_typage = 
    let Ntype (id_c,l_ntypes_c) = dc.desc in
    let Ntype (id_i,l_ntypes_i) = di.desc in
    if not (IdSet.mem id_c env_typage.c)
      then raise (Typing_error {loc = dc.loc ;
        msg = "Classe inconnue dans le contexte"}) ;
    if not (IdSet.mem id_i env_typage.i)
      then raise (Typing_error {loc = di.loc ;
        msg = "Interface inconnue dans le contexte"}) ;

    let l_implems = Hashtbl.find env_typage.implements id_c in
    let sigma = 
      if IdSet.mem id_c env_typage.paramstype
      then Hashtbl.create 0 (* table de subsitution vide *)
      else fait_sigma id_c l_ntypes_c
    in
    try
      let di' = List.find 
        (fun ({desc = Ntype(id_i',_)} : ntype desc) -> (id_i'=id_i))
        l_implems in
      let Ntype(id_i',l_ntypes_i') = di'.desc in
      Ntype.equal di.desc (Ntype(id_i',substi_list sigma l_ntypes_i'))
    with
      | Not_found ->
          let l_precs = Hashtbl.find env_typage.extends id_c in
          List.exists
            (fun dc' -> implements dc' di env_typage)
            (substi_list sigma l_precs)
            (* En soit il y a au plus une sur-classe *)
  in
  let verifie_implements dc di env_typage = 
    if not (implements dc di env_typage)
    then (let Ntype (id_c,_) = dc.desc in
      let Ntype (id_i,_) = di.desc in
      raise (Typing_error {loc = dc.loc ;
      msg = (Ntype.to_str dc) ^ " n'est pas connu comme implémentant " ^ (Ntype.to_str di) }))
  in
  (* ======================= *)

  (* === Sous-Type === *)
  let rec sous_type jtyp1 jtyp2 env_typage = match jtyp1,jtyp2 with
    | Jtypenull,_ 
    | Jboolean,Jboolean | Jint,Jint -> true
    | Jntype {desc = d1},Jntype {desc = d2} when Ntype.equal d1 d2 -> true
    | Jntype dci, _ ->
        let Ntype (id_ci,l_ntypes_ci) = dci.desc in
        if not (IdSet.mem id_ci env_typage.ci)
          then raise (Typing_error {loc = dci.loc ;
            msg = "Classe ou interface inconnue dans le contexte"}) ;
        
        let sigma = 
          if IdSet.mem id_ci env_typage.paramstype
          then Hashtbl.create 0 (* table de subsitution vide *)
          else fait_sigma id_ci l_ntypes_ci
        in    
        let l_precs = Hashtbl.find env_typage.extends id_ci in
        
        (List.exists (* Règle 4 des sous-types *)
          (fun dci' -> sous_type (Jntype dci') jtyp2 env_typage)
          (substi_list sigma l_precs)  )
        || begin match jtyp2 with (* Potentiellement la règle 5 *)
            | Jntype di ->
                let Ntype (id_i,l_ntypes_i) = di.desc in
                if not (IdSet.mem id_i env_typage.ci)
                  then raise (Typing_error {loc = di.loc ;
                    msg = "Classe ou interface inconnue dans le contexte"}) ;
                (* La règle 5 porte sur une classe avec une interface *)
                (IdSet.mem id_i env_typage.i)
                && (IdSet.mem id_ci env_typage.c)
                && begin 
                  (* Il faut C implems I et en plus pile la bonne substitution
                     donc encore une fois, on va remonter l'arbre d'héritage,
                     jusqu'à trouver C implems I<theta>, puis on regarde si en 
                     appliquant sigma à I<theta> on retombe sur notre I.
                     Si j'ai le temps, vu le nombre de fois qu'on refait la même
                     chose, ça serait sûrement mieux de stocker l'extends généralisée
                     et pareil implems généralisée. :/ *)
                  
                  let rec retrouve_i c = (* on n'utilise que les id *)
                    let l_implems = Hashtbl.find env_typage.implements c in
                    try
                      Some (List.find
                        (fun ({desc = Ntype (id_i',_)} : ntype desc) ->
                          id_i' = id_i)
                        l_implems)
                    with
                      | Not_found ->
                          let rec recup_fst_ok = function
                            | [] -> None
                            | (Some i)::_ -> Some i
                            | None :: q -> recup_fst_ok q
                          in
                          recup_fst_ok (List.map
                            (fun ({desc = Ntype (c',_)} : ntype desc) ->
                              retrouve_i c' )
                            (Hashtbl.find env_typage.extends c))
                  in
                  match (retrouve_i id_ci) with
                    | None -> false
                    | Some di' -> 
                        let ntype' = substi sigma (di').desc in   
                        Ntype.equal di.desc ntype' 
                end
            | _ -> false
          end
    | _,_ -> false
  in
  let verifie_sous_type jtyp1 loc1 jtyp2 env_typage = 
    if not (sous_type jtyp1 jtyp2 env_typage)
    then (raise (Typing_error {loc = loc1 ;
      msg = (str_of_jtp jtyp1) ^ " n'est pas un sous-type de " ^ (str_of_jtp jtyp2) }))
      (* On pourrait rajouter la loc2... *)
  in
  (* ======================= *)

  (* === Bien Fondé === *)
  let rec verifie_bf jtyp env_typage = match jtyp with
    | Jboolean | Jint | Jtypenull -> () (* c'est la fonction vérifie *)
    | Jntype {loc ; desc = Ntype (id,l_ntypes)} ->
        if not (IdSet.mem id env_typage.ci)
          then raise (Typing_error {loc=loc ;
            msg = "Classe ou interface inconnue"}) ;
        if l_ntypes = [] then ()
        else begin
        (* id a des paramtypes, en particulier id n'est pas un paramtype *)
        let params_id = (* T1 , ... , Tn, juste les idents *)
          List.map 
            (fun (p : paramtype desc) -> (p.desc).nom)
            (Hashtbl.find ci_params id) in 
        try
          List.iter2
            (fun param dn ->
              verifie_bf (Jntype dn) env_typage ;
              (* param est un paramtype ! *)
              let l_contr = Hashtbl.find env_typage.contraintes param in
              match l_contr with
                | [] -> ()
                | h::q -> 
                    verifie_sous_type (Jntype dn) dn.loc (Jntype h) env_typage;
                    (List.iter (fun di' -> verifie_implements dn di' env_typage) q)
            )
            params_id l_ntypes
        with
          | Invalid_argument _-> raise (Typing_error {loc=loc ;
              msg = "Trop ou pas assez de paramstype"})
        end
  in
  (* ======================= *)
  

  (* ===== DECLARATIONS ET VERIFICATION DES HÉRITAGES ===== *)

  (* === Pour créer des env_typages locaux === *)
  let env_copy e =
    {paramstype = e.paramstype ;
    ci = e.ci ; c = e.c ; i = e.i ;
    extends = Hashtbl.copy e.extends ;
    implements = Hashtbl.copy e.implements ;
    contraintes = Hashtbl.copy e.contraintes}
  in
  (* Remarque : on aurait mieux fait d'utiliser des Map et non des Hashtbl :/ *) 
  
  (* === Les interfaces === *)
  (* Contrairement aux classes, elles ne servent qu'à vérifier le typage
     dans la production de code, on n'en a plus besoin.
     Donc on se contente de vérifier le typage, on ne renvoie rien.
     ET on les vérifie dans un ordre topologique. *)
  let verifie_interface i =
    let params = Hashtbl.find ci_params i in
    let env_typage = env_copy env_typage_global in
    env_typage.paramstype <- IdSet.of_list params ;




