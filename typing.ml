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

type error = { loc : localisation ; msg : string }
exception Typing_error of error
 
let loc_dum = (Lexing.dummy_pos,Lexing.dummy_pos)

(* Dans la suite, ci veut dire classe ou interface, et bien souvent les paramstype
   sont aussi concernés, les vraies ci sont les classe et les interfaces.
   c veut dire classe, i interface, et parfois t paramtype *)

let type_fichier l_ci =
  (* ===== LES VARIABLES GLOBALES ===== *)
  (* J'utilise 3 lieux différents pour stocker des informations :
    1) Les variables globales : 
      Pour les informations uniquement sur les vraies ci
    2) Un env_typage_global :
      Qui contient toutes les informations communes, utiles et disponibles partout.
      Principalement initilisé au début, lors de la déclarations des vraies ci,
      mais pas que ! Lors de la déclarations, je récupère les méthodes, les champs
      et le constructeur. Le constructeur ne vaut que pour les vraies classes,
      on peut donc utiliser une variable globale. En revanche, on souhaite aussi
      connaitre les champs et les méthodes que possèdent les paramstypes, garantis 
      de par leurs contraintes. Ainsi pour grandement se simplifier, on stocke
      toutes les méthodes et les champs dans l'env_typage_global.
    3) Les env_typage spécifiques :
      Tout n'est pas commun, tout ce qui concernent les paramstype est gardé localement
      à une vraie ci. Pour reprendre le paragraphe précédent, les méthodes et les
      champs des paramstype, sont propres à chaque env_typage locaux. 
      On accède aux environnements locaux via la table : env_locaux, créée lors 
      de l'étape de vérification des vraies ci. *)  

  let graph_c = Hashtbl.create 5 in (* Hashtbl : id -> node *)
  let graph_i = Hashtbl.create 5 in (* Hashtbl : id -> node *)
  let ci_params = Hashtbl.create 5 in (* Hashtbl : id (ci) -> paramtype desc list *)
  let ci_params_tri = Hashtbl.create 5 in (* Hashtbl : id (ci) -> ident list *)
  let i_body = Hashtbl.create 5 in (* Hashtbl : id -> proto desc list *)
  let c_body = Hashtbl.create 5 in (* Hashtbl : id -> decl desc list *)
  let c_constr = Hashtbl.create 5 in (* Hashtbl : id -> ty_constr *)
  let body_main = ref [] in (* instr desc list *)
  
  let params_to_ids params = (* T1 , ... , Tn, juste les idents *)
    List.map (fun (p : paramtype desc) -> (p.desc).nom) params 
  in 
  
  let env_typage_global = {
    paramstype = IdSet.empty ; 
    ci = IdSet.empty ;
    c = IdSet.empty ; 
    i = IdSet.empty ;
    extends = Hashtbl.create 5 ;
    implements = Hashtbl.create 5 ;
    methodes = Hashtbl.create 5 ;
    champs = Hashtbl.create 5 ;
    tab_loc = Hashtbl.create 5} in

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
  
  Hashtbl.add env_typage_global.methodes "String" 
    (MethSet.singleton 
      {nom = "equals" ; 
       typ = Some ({loc = loc_dum ; desc = Jboolean} : jtype desc) ;
       types_params = []} ) ;
  Hashtbl.add env_typage_global.champs "String" ChSet.empty ;
  Hashtbl.add env_typage_global.methodes "Object" MethSet.empty ;
  Hashtbl.add env_typage_global.champs "Object" ChSet.empty ;


  (* ===== GRAPHES DES RELATIONS ENTRE LES C / LES I ===== *)
  (* On commence par récupérer toutes les relations, pour pouvoir traiter les I PUIS 
     les C dans un ordre topologique.
     ATTENTION, contrairement à ce qu'on pourrait penser, si on a :
     " class A <T extends B> " n'impose par une dépendance de A envers B.
     
     On en profite pour décortiquer l'arbre de syntaxe, et mettre des
     informations dans nos variables globales et notre env_typage_global. *)

  (* === Ajout des noeuds === *)
  let node_obj = {id="Object" ; mark = NotVisited ; prec=[] ; succ=[]} in

  let graph_add_node ci = match ci.desc with
    | Class {nom ; params ; body} ->
      Hashtbl.add ci_params nom params ;
      Hashtbl.add c_body nom body ;
      Hashtbl.add env_typage_global.tab_loc nom ci.loc ;

      if IdSet.mem env_typage_global.ci nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Nom de classe ou interface déjà utilisé."})
      else (
        Hashtbl.add graph_c nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
        new_c nom ;
    | Interface {nom ; params ; body} ->
      Hashtbl.add ci_params nom params ;
      Hashtbl.add i_body nom body ;
      Hashtbl.add env_typage_global.tab_loc nom ci.loc ;

      if IdSet.mem env_typage_global.ci nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Nom de classe ou interface déjà utilisé."})
      else (
        Hashtbl.add graph_i nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
        new_i nom ;
    | Main l -> 
      Hashtbl.add env_typage_global.tab_loc "Main" ci.loc ;
      body_main := l
      (* tjr traitée dernière *)
  in
  List.iter graph_add_node l_ci ;
  
  (* === Ajout des relations === *)
  (* Remarque : dans les graphes on ne regarde pas les relations C implements I, 
     car on va traiter les I avant. *)
  let dobj = {loc = loc_dum; desc = Ntype ("Object",[])} in
  let init_extends id l =
    Hashtbl.add env_typage_global.extends id l in
  let init_implements id l =
    Hashtbl.add env_typage_global.implements id l in
  
  init_extends "String" [dobj] ;
  init_implements "String" [] ;
  init_extends "Object" [] ;
  init_implements "Object" [] ;

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
        init_implements nom [] ;
        let node_i = Hashtbl.find graph_i nom in
        List.iter (graph_add_rel graph_i node_i) extds 
    | Main _ -> ()
  in
  List.iter graph_add_vg l_ci ;

  (* === Tri topologique === *)
  let rec parcours l n =
    if n.mark = NotVisited
    then (n.mark <- InProgress ;
      List.iter (parcours l) n.succ ;
      n.mark <- Visited ;
      l := n.id :: !l)
    else if n.mark = InProgress
    then raise (Typing_error {loc = Hashtbl.find env_typage_global.tab_loc n.id ;
          msg = "Il y a un cycle dans les héritages !"})
  in

  let list_cl = ref [] in (* ident list *)
  parcours list_cl node_obj ; (* Object est en tête *)
  
  let list_intf = ref [] in (* ident list *)
  Hashtbl.iter (fun i n -> parcours list_intf n) graph_i ;
  
  
  (* ===== Sous-type / Extends / Implements Généralisées / Bien fondé ===== *)
  (* ATTENTION, là on utilise les relations, on ne les vérifie pas *)
  (* Les fonctions sont des tests, par exemple verifie_bf vérifie si un type est bien
     fondé, le type de retour est unit, mais on peut raise l'erreur lors de la vérification,
     cela permet de localiser les problèmes précisément, mais le mieux serait souvent
     de rattraper l'erreur, pour préciser le contexte (pourquoi on voulait sous-type 
     par exemple). *)

  (* === Pour les substitutions des paramstype avec sigma === *)
  let fait_sigma ci loc l_ntypes =
    let sigma = Hashtbl.create (List.length l_ntypes) in
    let dparams = Hashtbl.find ci_params ci_params ci in
    let params_id = params_to_ids dparams in
    try List.iter2 
          (fun id (dn : ntype desc) -> 
            Hashtbl.add sigma id dn.desc) 
          params_id l_ntypes ;
        sigma
    with | Invalid_argument _ -> 
      raise (Typing_error {loc = loc ;
        msg = "Trop ou pas assez de paramstype" })
  in

  let rec substi_list sigma l_ntypes =
    List.map (fun (dn : ntype desc) -> 
      {loc=dn.loc  ; desc=substi sigma dn.desc}) l_ntypes
  and substi sigma (Ntype (id,l)) =
    if Hashtbl.mem sigma id
      then (Hashtbl.find sigma id)
    else Ntype(id, substi_list sigma l)
    (* Soit id est un paramtype, on le change (d'ailleurs l=[]).
       Soit id est un type construit, qui a potentiellement des paramstypes. *)
  in
  let substi_dj sigma (dj : jtype desc) = match dj.desc with
    | Jboolean | Jint -> dj
    | Jtypenull -> failwith "Normalement, le parser fait que ça n'arrive pas"
    | Jntype dnt -> {loc = dj.loc ; 
        desc = Jntype ({loc = dnt.loc ; desc = substi sigma dnt.desc})} 
  in
  let substi_djo sigma (djo : jtype desc option) = match djo with
    | None -> None
    | Some dj -> Some (substi_dj sigma dj) 
  in
  let substi_list_dj sigma (l_dj : jtype desc list) =
    List.map (substi_dj sigma) l_dj 
  in
  (* ======================= *)
 
  (* === Extends généralisée === *) 
  (* Pratiquement toujours contenu dans le test de sous_type.
     SAUF dans le cadre d'héritage de méthode, voir plus loin. *)
  let rec extends (dci1 : ntype desc) (dci2 : ntype desc) env_typage =
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
      else fait_sigma id1 dci1.loc l_ntypes1
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
  let extends_jtype_opt (djo1 : jtype desc option) (djo2 : jtype desc option) env_typage = 
    match djo1 , djo2 with
    | None,None -> true (* void et void *)
    | Some dj1,Some dj2 ->
      begin match dj1.desc , dj2.desc with
        | Jboolean , Jboolean | Jint , Jint -> true
        | Jntype dnt1 , Jntype dnt2 -> extends dnt1 dnt2 env_typage 
        | _ , _ -> false
      end
    | _,_ -> false
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
      else fait_sigma id_c dc.loc l_ntypes_c
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
      msg = (Ntype.to_str dc) ^ " n'est pas connue comme implémentant " ^ (Ntype.to_str di) }))
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
          else fait_sigma id_ci dci.loc l_ntypes_ci
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
                     et pareil implems généralisée. Mais attention, il faudrait faire
                     les substitutions au fûr et à mesure. *)
                  
                  let rec retrouve_i id_c = (* on n'utilise que les id *)
                    let implems_id = Hashtbl.find env_typage.implements id_c in
                    try
                      Some (List.find
                        (fun ({desc = Ntype (id_i',_)} : ntype desc) ->
                          id_i' = id_i)
                        implems_id)
                    with
                      | Not_found ->
                          let rec recup_fst_ok = function
                            | [] -> None
                            | (Some i)::_ -> Some i
                            | None :: q -> recup_fst_ok q
                          in
                          recup_fst_ok (List.map
                            (fun ({desc = Ntype (id_c',_)} : ntype desc) ->
                              retrouve_i id_c' )
                            (Hashtbl.find env_typage.extends id_c))
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
  let verifie_sous_type_opt (djo1 : jtype desc option) (djo2 : jtype desc option) env_typage =
    match djo1 , djo2 with
      | None , None -> () (* void et void *)
      | Some dj1 , Some dj2 ->
          verifie_sous_type dj1.desc dj1.loc dj1.desc env_typage
      | _ , _ -> raise (Typing_error {loc = loc1 ;
      msg = (str_of_jtp_opt djo1) ^ " n'est pas un sous-type de " ^ (str_of_jtp_opt djo2) })
  in
  (* ======================= *)

  (* === Bien Fondé === *)
  let rec verifie_bf jtyp env_typage = match jtyp with
    | Jboolean | Jint | Jtypenull -> () (* une fonction vérifie est à valeur dans unit *)
    | Jntype {loc ; desc = Ntype (id,l_ntypes)} ->
        if not (IdSet.mem id env_typage.ci)
          then raise (Typing_error {loc=loc ;
            msg = "Classe ou interface inconnue"}) ;
        if l_ntypes = [] then ()
        else begin
        (* id a des paramtypes, en particulier id n'est pas un paramtype *)
        let dparams = Hashtbl.find ci_params ci_params ci in
        let params_id = params_to_ids dparams in (* T1 , ... , Tn, juste les idents *)
        try
          List.iter2
            (fun id_p dn ->
              verifie_bf (Jntype dn) env_typage ;
              (* un paramtype hérite au plus d'une classe ou d'un autre paramtype,
                 peut-être de Object 
                 ATTENTION à ça si on veut passer à un amélioration où on 
                 conserve extends généralisée *)
              let d_mere = List.hd (Hashtbl.find env_typage.extends id_p) in
              let l_implements = Hashtbl.find env_typage.implements id_p in
              verifie_extends dn d_mere env_typage ; (* verifie_sous_type fait l'affaire ? *)
              List.iter (fun di' -> verifie_implements dn di' env_typage) l_implements ;
            )
            params_id l_ntypes
        with
          | Invalid_argument _-> raise (Typing_error {loc=loc ;
              msg = "Trop ou pas assez de paramstype"})
        end
  in
  (* ======================= *)
  

  (* ===== DECLARATIONS ET VERIFICATION DES HÉRITAGES ===== *)

  (* === Pour les env_typages locaux === *)
  let env_locaux = Hashtbl.create 5 in

  let env_copy e =
    {paramstype = e.paramstype ;
    ci = e.ci ; c = e.c ; i = e.i ;
    extends = Hashtbl.copy e.extends ;
    implements = Hashtbl.copy e.implements ;
    methodes = Hashtbl.copy e.methodes ;
    champs = Hashtbl.copy e.champs ;
    tab_loc = Hashtbl.copy e.tab_loc }
  in
  (* Remarque : Oui j'ai préféré les Hashtbl aux Map, car plus pratiques :/ *) 
  
  (* === Vérification des paramstype === *)
  (* Pour une ci X<T1,...,Tn> il faut vérfier que les contraintes (/les extends)
     des Ti ne forment pas de cycle, puis on les traite dans un ordre topologique.
     On vérifie que les theta_i sont connus, et que ce sont des interfaces pour i>1.
     Si les conditions sont vérifiés, on rajoute les interfaces dans l'env_typage.
     On rajoute les contraintes via env_typage.extends et implements, mais aussi
     les méthodes nécessairement possédées par T, et évidemment on ajoute T 
     dans env_typage.paramstype.
     
     REMARQUE sur le comportement de java, on peut avoir Tk extends Tk' 
     MAIS dans ce cas Tk' doit être l'unique contrainte ! 

     Remarque sur mes choix, les paramstypes sont propres à une classe/interface,
     c'est une information qui nous sert localement pour vérifier les ci. Ainsi
     se trouve dans env_typage.paramstype uniquement les paramstype de la ci
     actuellement traitée. On génère un nouvel env_typage à chaque fois.
     Ainsi on ne risque pas de mélanger les paramstype entre ci. Si A et C utilisent
     des paramstype nommés "T", ils ne seront jamais mélangés. Les informations 
     utiles pour le traitement du corps des classes sont gardées dans chaque env_typage,
     qu'on peut récuperer via la table env_locaux. *)
     
  let verifie_et_fait_paramstype (ci : ident) env_typage =
    let dparams = Hashtbl.find ci_params ci in
    let params_id = params_to_ids dparams in (* T1 , ... , Tn, juste les idents *)
    env_typage.paramstype <- IdSet.of_list params_id ;
    let info_tmp = Hashtbl.create (List.length params) in
    (* (ident , info_paramtype_tmp) Hashtbl.t *)
    List.iter 
      (fun (p : paramtype desc) -> 
        Hashtbl.add env_typage.tab_loc (p.desc).nom p.loc ;
        Hashtbl.add info_tmp (p.desc).nom 
        {tk_mark = NotVisited ; tk_loc = p.loc ; 
         tk_contraintes = (p.desc).extds})
      params ;
    
    let recup_tk' tk = function (* cf la remarque précédente sur le comportement de java *)
      | [({desc = Ntype (tk',[])} : ntype desc)] 
          when IdSet.mem tk' env_typage.paramstype -> Some tk' 
      | _ -> None
    in

    let params_id_tri = ref [] in
    let rec parcours (tk : ident) =
      let info_tk = Hashtbl.find info_tmp tk in
      if info_tk.tk_mark = NotVisited 
      then begin info_tk.tk_mark <- InProgress ; 
         (match (recup_tk' tk info_tk.tk_contraintes) with
          | None -> ()
          | Some tk' -> parcours tk' )
         info_tk.tk_mark <- Visited ;
         params_id_tri := tk :: !params_id_tri ; end
      else if info_tk.tk_mark = InProgress
      then raise (Typing_error {loc = info_tk.tk_loc ;
            msg = "Il y a un cycle dans les paramstype"})
    in
    
    List.iter parcours params_id ;

    (* FINALEMENT peu importe dans quels sens on vérifie les paramstype,
       puisque soit cas 1 on a Tk extends Tk', auquel cas c'est ok.
       Soit cas 2 Tk ne dépend pas de d'autres paramstype.

       D'ailleurs dans le cas 2 quand on fait les vérications, si on tombe sur
       un Tk' il faut planter. Malheureusement ici je le fais planter sur un 
       "Tk' est inconnu", ce serait beaucoup mieux de dire "Tk' est un paramtype 
       donc doit être l'unique contrainte, ce qui n'est pas le cas ici".
       Actuellement ma solution est de ne pas mettre les T dans l'env 
       et les rajouter seulement après les vérifications.

       ATTENTION, on peut appeler un paramtype par le nom d'une ci, 
       même interface I<I> est autorisé. Dans ce cas on écrase la ci, avec 
       ma méthode consiste à supprimer les ci portant le nom de paramtype. 
       FINALEMENT je ne vais pas le faire, parce que je manque du temps et
       c'est compliqué, car si on a I<A extends C> et d'autre part une classe A
       et une classe C extends A, il faut garder l'ancien. Mais du coup il y
       a un gros mélange, on peut imaginer des cas tordus. Je cherchais 
       peut-être un jour une meilleure façon de faire. 
       
       ATTENTION, retournement de situation ! 
       Ici, dans la vérification des paramstype, on peut effectivement traiter les
       paramtype dans un ordre quelconque. EN REVANCHE, pour les classes, 
       on va récupérer les méthodes et les champs des paramtypes, et là on doit
       absoluement les traiter dans un ordre topologique. 
       Exemple : avec <X entends Y, Y extends A & I>
       On doit commencer par Y, qui possède les champs de A, les méthodes de A et
       les méthodes demandées par I. Ensuite on héritera tout pour X. 
       -> C'est là toute l'importance de ci_params_tri 
       rem : On ne peut pas réarranger ci_params, sinon les substitutions vont 
       mal se passer !    *)
    
    (* = Sauvegarde d'un ordre topologique = *)
    ####
    let tb_id_to_dp = Hashtbl.create (List.lenght params_id) in
    List.iter2 
      (fun (id : ident) (dp : paramtype desc) -> 
        Hashtbl.add tb_id_to_dp id dp)
      params_id dparams ;
    let dparams_tri = List.map (Hashtbl.find tb_id_to_dp) !params_id_tri in
    Hashtbl.add ci_params_tri ci !params_id_tri ;
    (* ===================================== *)

    let verifie_paramtype (tk : ident) = 
      let {tk_contraintes} = Hashtbl.find info_tmp tk in
      match recup_tk' tk tk_contraintes with (* Pour faire les relations *)
        | Some tk' ->
            Hashtbl.add env_typage.extends tk 
              [{loc = tk'_loc ; desc = Ntype (tk',[])}] ;
            Hashtbl.add env_typage.implements tk []
        | None -> begin
            match tk_contraintes with 
            | [] ->  init_extends tk [dobj] ; init_implements tk []
            | (dci : ntype desc) :: q ->
                verifie_bf (Jntype dci) env_typage ;
                let Ntype (id_ci,l_ntypes_ci) = dci.desc in
                if IdSet.mem id_ci env_typage.c
                then (Hashtbl.add env_typage.extends tk [dci] ;
                      Hashtbl.add env_typage.implements tk q)
                else (
                  Hashtbl.add env_typage.extends tk [dobj] ;
                  Hashtbl.add env_typage.implements tk tk_contraintes) ;

                List.iter (* On vérifie que les contraintes suivantes st des interfaces *)
                  (fun (dn : ntype desc) -> 
                    verifie_bf (Jntype dn) env_typage ;
                    let Ntype (id',l_ntypes') = dn.desc in
                    if not (IdSet.mem id' env_typage.i)
                    then raise (Typing_error {loc = dn.loc ;
                        msg = "On attend des interfaces en contraintes supplémentaires"})
                  ) q ;
                let h = Hashtbl.find env_typage.implements tk in
                Hashtbl.replace env_typage.implements tk (h @ q)
        end
    in
    List.iter verifie_paramtype params_id ; 
    (* params_id juste pour montrer qu'on n'a pas d'utiliser params_id_tri ici *)

    List.iter (fun tk ->
      env_typage.ci <- IdSet.add tk env_typage.ci ;
      env_typage.c <- IdSet.add tk env_typage.c ) params_id 
  in
  (* ======================= *)


  (* === LES METHODES : Héritage et vérification redéfinition === *)

  (* Je dis que deux méthodes sont en relations, si l'une appartient à une sur-ci
     de l'autre, ou si une ci hérite des deux. 
     Les paramètres doivent alors être de même types.*)
  let verifie_meme_parametres (meth : ty_methode) (meth' : ty_methode) =
    try List.iter2
      (fun (d_jtype : jtype desc) (d_jtype' : jtype desc) ->
        if not (jtype_equal d_jtype.desc djtype'.desc)
        then raise (Typing_error {loc = d_jtype.loc ;
          msg = "Deux méthodes en relation doivent avoir des paramètres de même types."}))
      meth.types_params meth'.types_params
    with | Invalid_argument _ -> 
        raise (Typing_error {loc = loc ;
          msg = "Deux méthodes en relation doivent avoir autant de paramètres."})
  in

  let recup_methodes (dci' : ntype desc) env_typage =
    let Ntype (id_ci',l_ntypes_ci') = dci'.desc in
    (* Il faut substituer les paramstype dans les types de retour des méthodes héritées *)
    (* MAIS aussi dans les paramètres, voir l'exemple correcte test9.java.
       << interface I<U> { U m();}
          interface J<U> { U m();}
          interface K extends I<String>,J<String> {String m();} >> *)
    let sigma = fait_sigma id_ci' dci'.loc l_ntypes_ci' in
    
    MethSet.map 
      (fun meth -> {nom = meth.nom ; 
          typ = substi_djo sigma meth.typ ; 
          types_params = substi_list_dj sigma meth.types_params } )
      (Hashtbl.find env_typage.methodes id_ci')
  in
  
  (* BUT : Renvoyer un MethSet contenant toutes les méthodes héritées.
       
       ATTENTION : si une méthode est présente dans deux ci mères (comme ce
       peut être le cas avec des interfaces), alors :
       il faut les mêmes arguments et il faut une relation entre les types de
       retour, typiquement si dans une des classes/interfaces mères on a T1 m() et dans
       une autre T2 m(), alors il faut T1 extends(généralisée) T2 ou T2 extends T1
       (en particulier T1 et T2 doivent être deux classes ou deux interfaces).
       Je dis bien, extends et non sous-type !! Auquel cas le type de retour hérité 
       sera le plus petit des différents types de retours.
       Ensuite si on redéfinit il faudra un sous-type de ce type hérité. 

       Remarque : on n'a pas besoin de remonter l'arbre des extensions,
       les ci_meres contiennent déjà celles des ancêtres. 

     Dans les faits on utilise plutôt une table qu'un MethSet :
       methodes_heritees : (ident , (ty_methode,ident)) Hashtbl.t 
       Ici beaucoup plus pratique qu'un MethSet, car on veut retrouver 
       les méthodes déjà héritées, à partir de leur nom. 
       On sauvegarde aussi le nom de la ci par laquelle on hérite, pour 
       envoyer des messages d'erreurs précis.     *)

  let heritage_d'une_surci id_ic loc_ci methode_heritees env_typage (dci' : ntype desc) =
    let Ntype (id_ci',l_ntypes_ci') = dci'.desc in
    let sigma = fait_sigma id_ci' dci'.loc l_ntypes_ci' in
    let sur_methodes = recup_methodes dci' env_typage in
    let traite_methode (meth' : ty_methode) =
      let {nom} = meth' in
      match (Hashtbl.find_opt methodes_heritees nom) with
        | None -> Hashtbl.add methodes_heritees nom (meth',id_ci')
        | Some (meth'',id_ci'') -> 
            verifie_meme_parametres meth' meth'' ;
            if not (extends_jtype_opt meth''.typ meth'.typ env_typage)
            then if (extends_jtype_opt meth'.typ meth''.typ env_typage)
            then Hashtbl.replace methodes_heritees nom (meth',id_ci')
            else raise (Typing_error {loc = loc_ci ;
              msg = id_ci ^ " hérite de la méthode " ^ nom ^ " via "
                  ^ id_ci' " avec le type de retour " ^ (str_of_jtp_opt meth'.typ)
                  ^ " mais aussi via " ^ id_ci'' ^ " avec le type de retour "
                  ^ (str_of_jtp_opt meth''.typ) 
                  ^ " or ces types ne sont pas en relation, l'un doit extends l'autre."})
            (* else on n'a pas à changer *)
            (* ATTENTION, je ne garantie rien dans les tests d'extends, 
               l'env de typage peut être très bizarre, dans le cas où des
               paramstype reprennent le nom de vraies ci. 
               Cf ma remarque à ce propos dans verifie_et_fait_paramstype. *) 
    in
    MethSet.iter traite_methode sur_methodes
  in
  let herite_methodes id_ci loc_ci env_typage =
    let methodes_heritees = Hashtbl.create 5 in 
    let extends = Hashtbl.find env_typage.extends id_ci in
    List.iter (heritage_d'une_surci id_ci loc_ci env_typage methodes_heritees) extends ;
    methodes_heritees 
  in


  let verifie_et_fait_methode (type_retour : jtype desc option)  nom params 
          loc env_typage methodes_heritees =
    (* Pour rappel, methodes_heritees : (ident , (ty_methode,ident)) Hashtbl.t
       qui prend un nom de méthode en entrée, et donne (si elle existe) la
       méthode héritée, et le nom de la ci mère dont on hérite *) 
    (* vérifie type de retour *)
    begin match type_retour with
      | None -> ()
      | Some tr -> verifie_bf tr.desc env_typage
    end ;
    (* vérifie type des paramètres *)
    List.iter 
      (fun (dp : param desc) -> verifie_bf dp.desc.ty.desc env_typage)
      params ;
    (* vérifie rédéfinition propre *)
    let types_params = 
      List.map (fun (dp : param desc) -> (dp.desc).typ) params in
    let meth = {nom = nom ; typ = type_retour ; types_params = types_params} in
    begin match (Hashtbl.find_opt methodes_heritees nom) with
      | None -> () 
      | Some (meth',id_ci') ->
          verifie_meme_parametres meth meth' ;
          verifie_sous_type_opt meth.typ meth'.typ env_typage end 
     Hashtbl.replace methodes_heritees nom (meth,id_ci)
     (* Pour les avoir toutes au même endroit...  
        d'ailleurs c'est forcément la nouvelle def qui l'emporte et là
        la contrainte est plus souple, avec un sous_type et non extends *)
     (* Là clairement on peut bien mieux faire en terme de message d'erreur :/ *)
  in
  let tab_meth_to_MethSet methodes_heritees =
    let l_methodes = ref [] in
    Hashtbl.iter
      (fun nom (meth,id_ci') -> l_methodes := meth :: !l_methodes)
      methodes_heritees ;
    MethSet.of_list !l_methodes
  in
  (* ======================= *)


  (* === Construction des infos sur les paramstypes, pour les classes === *)
  let recup_champs_methodes_paramstype id_c env_typage =
    (* ici on a déjà verifié et ajouté les paramstype *)
    let params_id_tri = Hashtbl.find ci_params_tri id_c in
    (* C'est précisément maintenant qu'on a besoin d'un ordre topologique,
       cf mon Attention dans verifie_et_fait_paramstype *) 
    let fait_un_paramtype id_t =
      let loc_t = Hashtbl.find env_typage.tab_loc id_t in
      (* = Les méthodes = *)
      let methodes_heritees = Hashtbl.create 5 in 
      let dc_mere = List.hd (Hashtbl.find env_typage.extends id_t) in
      heritage_d'une_surci id_t loc_t methodes_heritees dc_mere ;
      let implements = Hashtbl.find env_typage.implements id_t in
      List.iter (heritage_d'une_surci id_t loc_t methodes_heritees env_typage) implements ;
      Hashtbl.add env_typage.methodes id_t (tab_meth_to_MethSet methodes_heritees) ; 
      (* ATTENTION, je n'ai pas vérifié le comportement de java quand on
         hérite d'une méthode m() renvoyant un T1 et qu'on implémente une interface
         qui demande m() renvoyant un T2. Actuellement je prends le plus petit des deux.
         Peut-être qu'il faudrait toujours garder T1. *)

      (* = Les champs = *)
      let Ntype(id_m,l_ntypes_m) = dc_mere.desc in
      let sigma = fait_sigma id_m dc_mere.loc l_ntypes_m in
      let champs = ChSet.map 
        (fun champ -> {nom = champ.nom ; 
            typ = substi_dj sigma champ.typ } )
        (Hashtbl.find env_typage.champs id_m) in 
      Hashtbl.add env_typage.champs id_t champs ;
    in
    List.iter fait_un_paramtype params_id_tri
  in
  (* ======================= *)


  (* === LES INTERFACES  === *)
  (* Contrairement aux classes, elles ne servent qu'à vérifier le typage
     dans la production de code, on n'en a plus besoin.
     Donc on se contente de vérifier le typage, on ne renvoie rien.
     ET on les vérifie dans un ordre topologique. *)
  let verifie_bf_et_i (di' : ntype desc) =
      verifie_bf (Jntype di') env_typage ;
      let Ntype (id_i',l_ntypes_i') = di'.desc in
      if not (IdSet.mem id_i' env_typage.i)
      then raise (Typing_error {loc = di'.loc ;
        msg = "On attendait une interface et non une classe/paramtype"})
  in
  let verifie_interface id_i =
    let env_typage = env_copy env_typage_global in

    (* Première étape : les paramstype *)
    verifie_et_fait_paramstype id_i env_typage ;

    (* Deuxième étape : les extends *)
    let extends = Hashtbl.find env_typage.extends id_i in
    List.iter verifie_bf_et_i extends ;
    
    (* Troisième étape : les méthodes *)
    (* Les méthodes demandées par i comprennent toutes les méthodes demandées
       par une sur-interface de i. 
       Si on redéfinit une méthode, on doit vérifier que les paramètres sont 
       de même type, et que le type de retour est un sous-type. 
       Cf les très nombreuses remarques à ce propos dans les fonctions dédiées. *)

    let (body : proto desc list) = Hashtbl.find i_body id_i in
    let loc_i = Hashtbl.find env_typage.tab_loc id_i in
    let methodes_heritees = herite_methodes id_i loc_i env_typage in 
    let ajoute_meth (d_proto : proto desc) =
      let pro = d_proto.desc in
      verifie_et_fait_methode pro.typ pro.nom pro.params 
        d_proto.loc env_typage methodes_heritees 
    in
    List.iter ajoute_meth body ;
    Hashtbl.add env_typage_global.methodes id_i (tab_meth_to_MethSet methodes_heritees)
    (* Attention : les méthodes de l'interface partent dans l'env global !!
       Et c'est tout ce qu'on garde, on ne sauvegarde pas l'env local,
       pour les interfaces on s'arrête là. *)
  in
  
  List.iter verifie_interface !list_intf ;
  (* ======================= *)


  (* === LES CLASSES === *)
  (* La vérification des classes se fait en 2 temps. 
     1) Déclaration - pour *toutes* les classes : 
       -On déclare les paramstype 
       -On controle l'existence de la surclasse
       -On déclare les méthodes, les champs et le constructeur, en vérifiant
        les types des paramètres et le type de retour, et surtout on gère
        l'héritage des méthodes.
       -On controle les implements, en vérifiant chaque méthode !
     2) PUIS à nouveau pour *toutes* les classes :
       -On récupère les champs et les méthodes des paramstype,
        en suivant un ordre topologique au sein des paramstype.
     
     On est obligé de commencer par déclarer toutes les méthodes et les champs, 
     et ce dans toutes les classes (plus exactement dans toutes les vraies ci,
     sachant que les interfaces ont déjà été faites), avant de passer aux paramstypes. 
     Car on peut avoir A<I extends B> et B<I extends A>. 
     Utiliser un ordre topologique sur les classes est crucial dans la première partie,
     exactement pour comme pour les interfaces précédemment. *)

  let verifie_classe id_c =
    let env_typage = env_copy env_typage_global in

    (* Déclaration des paramstype *)
    verifie_et_fait_paramstype id_c env_typage ;  

    (* La sur-classe *)
    let d_mere = List.hd (Hashtbl.find env_typage.extends id_c) in
    (* Une classe hérite toujours d'une seule autre classe, possiblement d'Object,
       exceptée pour Object, mais qu'on n'a pas besoin de traiter. *)
    let Ntype(id_m,l_ntypes_m) = d_mere.desc in
    if id_m = "String"
    then raise (Typing_error {loc=d_mere.loc ;
      msg = "On ne doit pas hériter de la classe String" }) ;
    if not (IdSet.mem id_m env_typage.c)
    then raise (Typing_error {loc = d_mere.loc ;
      msg = "On attendait une classe et non une interface"}) ;
    if (IdSet.mem id_m env_typage.paramstype)
    then raise (Typing_error {loc = d_mere.loc ;
      msg = "Une classe ne peut étendre un de ses paramstype, beurk"}) ;
    verifie_bf (Jntype d_mere) env_typage ; 
       
    (* Déclaration du corps : des champs, des méthodes et du constructeur  *)
    let (body : decl desc list) = Hashtbl.find c_body id_c in
    let methodes_heritees = Hashtbl.create 5 in
    heritage_d'une_surci id_c loc_c methodes_heritees dc_mere ;
    let champs = ref (ChSet.map 
      (fun champ -> {nom = champ.nom ; 
        typ = substi_dj sigma champ.typ } )
      (Hashtbl.find env_typage.champs id_m)) in  
    let verifie_decl = function
      | Dchamp (dj,nom) ->
          let champ = {nom = nom ; typ = dj} in
          if ChSet.mem champ !champs (* Le equal du module Champ compare juste les noms *)
          then raise (Typing_error {loc = dj.desc ;
            msg = id_c ^ " hérite déjà d'un champ " ^ nom 
              ^ " il est interdit de rédéfinir un champ."})
            (* l'erreur vaut aussi si on définit 2 fois un champ au sein d'une classe *)
          else (verifie_bf djtype.desc ;
            champs := ChSet.add champ !champs)

      | Dmeth dmeth ->
          let d_proto = dmeth.desc.info in 
          let pro = d_proto.desc in (* les deux desc sont redondants ! *)
          verifie_et_fait_methode pro.typ pro.nom pro.params 
            d_proto.loc env_typage methodes_heritees ;
      
      | Dconstr dconstr -> 
          let {nom ; params} = dconstr.desc in
          if nom <> id_c then raise (Typing_error {loc = dconstr.loc ;
            msg = "Le constructeur doit avoir le même nom que la classe"}) ;
          List.iter 
            (fun (dp : param desc) -> verifie_bf dp.desc.typ.desc env_typage)
            params ;
          Hashtbl.add c_constr params 
    in
    List.iter verifie_decl body ; 
    Hashtbl.add env_typage_global.champs id_c !champs ;
    Hashtbl.add env_typage_global.methodes id_c (tab_meth_to_MethSet methodes_heritees) ;
    (* Informations qui partent dans le GLOBAL *)

    (* Vérification des implements, on vérifie vraiment si c présente les méthodes demandées *)
    let implements = Hashtbl.find env_typage.implements id_c in
    List.iter verifie_bf_et_i implements ;
    let verification_implements (di : ntype desc) =
      let Ntype (id_i,l_ntypes_i) = di.desc in
      let sigma = fait_sigma id_i di.loc l_ntypes_i in
      let meth_demandees = recup_methodes di env_typage in
      let verifie_meth (meth_i : ty_methode) = 
        match Hashtbl.find_opt methodes_heritees meth_i.nom with
        | None -> raise (Typing_error {loc = di.loc ;
            msg = id_c ^ " n'implémente pas " ^ id_i 
              ^ " parce qu'elle n'a pas de méthode " ^ nom})
        | Some meth_c -> 
            verifie_meme_parametres meth_i meth_c ;
            verifie_sous_type_opt meth_c.typ meth_i.typ env_typage
      in
      MethSet.iter verifie_meth meth_demandees 
    in
    List.iter verification_implements implements ;

    Hashtbl.add env_locaux id_c env_typage 
  in
  
  (* En premier *)
  List.iter verifie_classe (List.tl !list_cl) ; (* on ne vérifie pas Object *) 

  (* PUIS *)
  List.iter
    (fun id_c -> 
      let env_typage = Hashtbl.find env_locaux id_c in
      recup_champs_methodes_paramstype id_c env_typage )
    (List.tl !list_cl) ;



     
    ATTENTION À RAJOUTER STRING.EQUALS ET TRAITER SYSTEM.OUT.PRINT ET PRINTLN
