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

  let graph_c : (ident,node) Hashtbl.t = Hashtbl.create 5 in
  let graph_i : (ident,node) Hashtbl.t = Hashtbl.create 5 in 
  let ci_params : (ident,paramtype desc list) Hashtbl.t = Hashtbl.create 5 in
  let ci_params_tri : (ident,ident list) Hashtbl.t = Hashtbl.create 5 in
  let i_body : (ident,proto desc list) Hashtbl.t = Hashtbl.create 5 in 
  let c_body : (ident,desc desc list) Hashtbl.t = Hashtbl.create 5 in 
  let c_constr : (ident,info_constr) Hashtbl.t = Hashtbl.create 5 in
  let body_main : instr desc list = ref [] in
  
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
    env_typage_global.i <- IdSet.addp nom env_typage_global.i in

  env_typage_global.c <- IdSet.of_list ["Main";"Object";"String"] ;
  env_typage_global.ci <- env_typage_global.c ;
  
  let tabmeth_String = Hashtbl.create 1 in
  Hashtbl.add tabmeth_String "equals"
    {nom="equals" ; id_ci = "String" ;
     typ=Some {loc = loc_dum ; desc = Jboolean} ; types_params=[]} ;
  Hashtbl.add env_typage_global.methodes "String" tabmeth_String ;
  Hashtbl.add env_typage_global.methodes "Object" (Hashtbl.create 0) ;
  let tabch_empty = Hashtbl.create 0 in
  Hashtbl.add env_typage_global.champs "String" tabch_empty ;
  Hashtbl.add env_typage_global.champs "Object" tabch_empty ;


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
      msg = (Ntype.to_str dci1) ^ " n'est pas connu comme étendant " 
          ^ (Ntype.to_str dci2) }))
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
      msg = (Ntype.to_str dc) ^ " n'est pas connue comme implémentant " 
          ^ (Ntype.to_str di) }))
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
    Hashtbl.add ci_params_tri ci !params_id_tri ;

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
  let verifie_meme_parametres (meth : info_methode) (meth' : info_methode) loc=
    try List.iter2
      (fun (d_jtype : jtype desc) (d_jtype' : jtype desc) ->
        if not (jtype_equal d_jtype.desc djtype'.desc)
        then raise (Typing_error {loc = d_jtype.loc ;
          msg = "Problème avec les méthodes nommées" ^ meth.nom
             ^ ", deux méthodes en relation doivent avoir des paramètres de même types."}))
      meth.types_params meth'.types_params
    with | Invalid_argument _ -> 
        raise (Typing_error {loc = loc ;
          msg = "Problème avec les méthodes nommées" ^ meth.nom
             ^ ", deux méthodes en relation doivent avoir autant de paramètres."})
  in

  let recup_methodes (dci' : ntype desc) env_typage =
    let Ntype (id_ci',l_ntypes_ci') = dci'.desc in
    (* Il faut substituer les paramstype dans les types de retour des méthodes héritées *)
    (* MAIS aussi dans les paramètres, voir l'exemple correcte test9.java.
       << interface I<U> { U m();}
          interface J<U> { U m();}
          interface K extends I<String>,J<String> {String m();} >> *)
    let sigma = fait_sigma id_ci' dci'.loc l_ntypes_ci' in
    
    let sur_methodes : methtab = Hashtbl.create 0 in
    Hashtbl.iter
      (fun nom (meth : info_methode) -> 
        Hashtbl.add sur_methodes nom 
         {nom = meth.nom ; id_ci = meth.id_ci ; 
          typ = substi_djo sigma meth.typ ; 
          types_params = substi_list_dj sigma meth.types_params } )
      (Hashtbl.find env_typage.methodes id_ci') ;
    sur_methodes
  in
  
  (* BUT : Renvoyer une methtab contenant toutes les méthodes héritées.
       
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

       Remarque : Dans le info_methode, on retient aussi le nom de la ci 
       d'où provient cette méthode, pratique pour envoyer des messages d'erreurs précis.*)

  let heritage_d'une_surci id_ic loc_ci methode_heritees env_typage (dci' : ntype desc) =
    let Ntype (id_ci',l_ntypes_ci') = dci'.desc in
    let sigma = fait_sigma id_ci' dci'.loc l_ntypes_ci' in
    let sur_methodes = recup_methodes dci' env_typage in
    let traite_methode nom (meth' : info_methode) =
      match (Hashtbl.find_opt methodes_heritees nom) with
        | None -> Hashtbl.add methodes_heritees nom meth'
        | Some meth'' -> 
            verifie_meme_parametres meth' meth'' loc_ci;
            if not (extends_jtype_opt meth''.typ meth'.typ env_typage)
            then if (extends_jtype_opt meth'.typ meth''.typ env_typage)
            then Hashtbl.replace methodes_heritees nom meth'
            else raise (Typing_error {loc = loc_ci ;
              msg = id_ci ^ " hérite de la méthode " ^ nom ^ " via "
                  ^ id_ci' " avec le type de retour " ^ (str_of_jtp_opt meth'.typ)
                  ^ " mais aussi via " ^ meth''.id_ci ^ " avec le type de retour "
                  ^ (str_of_jtp_opt meth''.typ) 
                  ^ " or ces types ne sont pas en relation, l'un doit extends l'autre."})
            (* Au lieu de fournir juste loc_ci, ça serait cool de remonter l'arbre
               de extends en montrant d'où viennent les méthodes en conflits *)
            (* else on n'a pas à changer *)
            (* ATTENTION, je ne garantie rien dans les tests d'extends, 
               l'env de typage peut être très bizarre, dans le cas où des
               paramstype reprennent le nom de vraies ci. 
               Cf ma remarque à ce propos dans verifie_et_fait_paramstype. *) 
    in
    Hashtbl.iter traite_methode sur_methodes
  in
  let herite_methodes id_ci loc_ci env_typage =
    let methodes_heritees : methtab = Hashtbl.create 5 in 
    let extends = Hashtbl.find env_typage.extends id_ci in
    List.iter (heritage_d'une_surci id_ci loc_ci env_typage methodes_heritees) extends ;
    methodes_heritees 
  in


  let verifie_et_fait_methode (type_retour : jtype desc option) nom params id_ci 
          loc env_typage methodes =
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
    let meth = {nom = nom ; id_ci = id_ci ; 
      typ = type_retour ; types_params = types_params} in
    begin match (Hashtbl.find_opt methodes nom) with
      | None -> () 
      | Some meth' ->
          verifie_meme_parametres meth meth' loc;
          verifie_sous_type_opt meth.typ meth'.typ env_typage end 
     Hashtbl.replace methodes nom meth
     (* Pour les avoir toutes au même endroit...  
        d'ailleurs c'est forcément la nouvelle def qui l'emporte et là
        la contrainte est plus souple, avec un sous_type et non extends *)
     (* Là clairement on peut bien mieux faire en terme de message d'erreur :/ *)
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
      let methodes_heritees : methtab = Hashtbl.create 5 in 
      let dc_mere = List.hd (Hashtbl.find env_typage.extends id_t) in
      heritage_d'une_surci id_t loc_t methodes_heritees dc_mere ;
      let implements = Hashtbl.find env_typage.implements id_t in
      List.iter (heritage_d'une_surci id_t loc_t methodes_heritees env_typage) implements ;
      Hashtbl.add env_typage.methodes id_t methodes_heritees ; 
      (* ATTENTION, je n'ai pas vérifié le comportement de java quand on
         hérite d'une méthode m() renvoyant un T1 et qu'on implémente une interface
         qui demande m() renvoyant un T2. Actuellement je prends le plus petit des deux.
         Peut-être qu'il faudrait toujours garder T1. *)

      (* = Les champs = *)
      let Ntype(id_m,l_ntypes_m) = dc_mere.desc in
      let sigma = fait_sigma id_m dc_mere.loc l_ntypes_m in
      let champs : chtab = Hashtbl.create 5 in
      Hashtbl.iter
        (fun nom (champ : info_champ) ->
          Hashtbl.add champs nom
            {nom = champ.nom ; id_c = champ.id_c ; 
            typ = substi_dj sigma champ.typ } )
        (Hashtbl.find env_typage.champs id_m) in 
      Hashtbl.add env_typage.champs id_t champs
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
    let methodes = herite_methodes id_i loc_i env_typage in 
    let ajoute_meth (d_proto : proto desc) =
      let pro = d_proto.desc in
      verifie_et_fait_methode pro.typ pro.nom pro.params id_i 
        d_proto.loc env_typage methodes 
    in
    List.iter ajoute_meth body ;
    Hashtbl.add env_typage_global.methodes id_i methodes
    (* Attention : les méthodes de l'interface partent dans l'env global !!
       Et c'est tout ce qu'on garde, on ne sauvegarde pas l'env local,
       pour les interfaces on s'arrête là. 
       On pourrait bidouiller pour rajouter les méthodes et les champs des vraies
       ci directement dans tous les env_locaux. En initialisant au tout début 
       des Hashtbl vides pour chaque vraies ci dans l'env_typage_global, puis en
       rajoutant les méthodes et les champs à ces tables. Qui serait commune à 
       tout les env_typage, malgré le env_copy. 
       Mais c'est inutilement compliqué. *)
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
    let body = Hashtbl.find c_body id_c in
    let methodes : methtab = Hashtbl.create 5 in
    let champs : chtab = Hashtbl.create 5 in
    (* J'ai fait le choix après de nombreux essais, d'utiliser des methtab et des
       chtab pour pouvoir 1) retrouver les methodes/champs rapidement pendant
       la vérification des corps (les accès) (d'où l'abandon des MethSet),
       et 2) pour pouvoir en rajouter facilement (d'où des Hashtbl et non des Map) *)
    (* Héritage *)
    heritage_d'une_surci id_c loc_c methodes dc_mere ;
    Hashtbl.iter
      (fun nom (champ : info_champ) -> 
        Hashtbl.add champs nom 
         {nom = champ.nom ; id_c = champ.id_c ;
          typ = substi_dj sigma champ.typ } )
      (Hashtbl.find env_typage.champs id_m) ;

    (* Nouveaux *)
    let verifie_decl (decl : decl desc) = match decl.desc with
      | Dchamp (dj,nom) ->
          let champ = {nom = nom ; id_c = id_c ; typ = dj} in
          if Hashtbl.mem !champs nom
          then raise (Typing_error {loc = decl.loc ;
            msg = id_c ^ " hérite déjà d'un champ " ^ nom 
              ^ " il est interdit de rédéfinir un champ."})
            (* l'erreur vaut aussi si on définit 2 fois un champ au sein d'une classe *)
          else (verifie_bf djtype.desc ;
            Hashtbl.add champs nom champ )

      | Dmeth dmeth ->
          let d_proto = dmeth.desc.info in 
          let pro = d_proto.desc in (* les deux desc sont redondants ! *)
          verifie_et_fait_methode pro.typ pro.nom pro.params id_c
            d_proto.loc env_typage methodes ;
      
      | Dconstr dconstr ->
          if Hashtbl.mem c_constr id_c 
          then raise (Typing_error {loc = decl.loc ;
            msg = "Une classe ne peut avoir plus d'un constructeur"}) ;
          let {nom ; params} = dconstr.desc in
          if nom <> id_c then raise (Typing_error {loc = decl.loc ;
            msg = "Le constructeur doit avoir le même nom que la classe"}) ;
          List.iter 
            (fun (dp : param desc) -> verifie_bf dp.desc.typ.desc env_typage)
            params ;
          Hashtbl.add c_constr id_c params 
    in
    List.iter verifie_decl body ; 
    if not (Hashtbl.mem c_constr id_c)
    then Hashtbl.add c_constr id_c [] ;
    Hashtbl.add env_typage_global.champs id_c champs ;
    Hashtbl.add env_typage_global.methodes id_c methodes ;
    (* Informations qui partent dans le GLOBAL *)

    (* Vérification des implements :
       Enfin, on vérifie vraiment si c présente les méthodes demandées *)
    let implements = Hashtbl.find env_typage.implements id_c in
    List.iter verifie_bf_et_i implements ;
    let verification_implements (di : ntype desc) =
      let Ntype (id_i,l_ntypes_i) = di.desc in
      let sigma = fait_sigma id_i di.loc l_ntypes_i in
      let meth_demandees = recup_methodes di env_typage in
      let verifie_meth nom (meth_i : info_methode) = 
        match Hashtbl.find_opt methodes nom with
        | None -> raise (Typing_error {loc = di.loc ;
            msg = id_c ^ " n'implémente pas " ^ id_i 
              ^ " parce qu'elle n'a pas de méthode " ^ nom})
        | Some meth_c -> 
            verifie_meme_parametres meth_i meth_c di.loc ;
            verifie_sous_type_opt meth_c.typ meth_i.typ env_typage
      in
      Hashtbl.iter verifie_meth meth_demandees 
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
      env_typage.methodes <- Hashtbl.copy env_typage_global.methodes ; 
      env_typage.champs <- Hashtbl.copy env_typage_global.champs ;
      (* Des Hashtbl de methtbl. On doit copy les Hashtbl, mais les methtbl peuvent
         être les mêmes !
         On actualise, en prennant toutes les méthodes des vraies ci,
         sachant qu'on ne risque pas d'écraser quoique ce soit, dans les env_locaux
         ces champs étaient restés vides jusqu'ici. *)
      recup_champs_methodes_paramstype id_c env_typage )
    (List.tl !list_cl) ;

  (* ================================= *)
  (* ================================= *)




  (* ===== VERIFICATION DES CORPS ===== *)
  (* Il nous reste à vérifier les corps, composés d'inscrutions. Pour cela on 
     va utiliser, en plus des env_typage (locaux), des env_vars, qui sont en faites
     de simple (ident, jtype) Hashtbl.t   *)

  (* ATTENTION C'EST ICI QUE NOUS PRODUIRONS LE NOUVEL ARBRE DE SYNTAXE
     MAIS VU MON RETARD, JE TIENS D'ABORD À TESTER LE TYPEUR    *)

  (* Les accès gèrent les valeurs gauches *)
  let rec jtype_of_acces =

  and jtype_of_expr loc_expr env_typage env_vars = function
    | Enull -> Jtypenull
    | Esimple dexpr_s -> jtype_of_expr dexpr_s.loc env_typage env_vars dexpr_s.desc
    | Eequal (dacces,dexpr) -> (* permet a = b = c qui change b en c puis a en b *)
        let jt_expr = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
        let jt_acces = jtype_of_acces dacces.loc env_typage env_vars dacces.desc in
        if not (sous_type jt_expr jt_acces env_typage)
        then raise (Typing_error {loc=loc_expr ;
          msg = "Pour changer une valeur, il faut un sous-type de ce qui est demandé "
              ^ (str_of_jtp jt_expr) ^ " n'est pas un sous-type de "
              ^ (str_of_jtp jt_acces)}) ;
        jt_acces
    | Eunop (unop,dexpr) -> 
        let jt_expr = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
        begin match unop with
          | Unot -> 
              if jt_expr <> Jboolean 
              then raise (Typing_error {loc=dexpr.loc ;
                msg = "Le not s'applique sur un boolean"}) ;
              Jboolean
          | Uneg ->
              if jt_expr <> Jint 
              then raise (Typing_error {loc=dexpr.loc ;
                msg = "Le moins unaire s'applique sur un entier"}) ;
              Jint
        end
    | Ebinop (dexpr1,binop,dexpr2) ->
        let jt_expr1 = jtype_of_expr dexpr1.loc env_typage env_vars dexpr1.desc in
        let jt_expr2 = jtype_of_expr dexpr2.loc env_typage env_vars dexpr2.desc in
        begin match jt_expr1,binop,jt_expr2 with
          | Jint,Badd,Jint | Jint,Bsub,Jint | Jint,Bmul,Jint
          | Jint,Bdiv,Jint | Jint,Bmod,Jint -> Jint
          | Jint,Blt,Jint | Jint,Ble,Jint
          | Jint,Bgt,Jint | Jint,Bge,Jint -> Jboolean
          | Jboolean,Band,Jboolean | Jboolean,Bor,Jboolean -> Jboolean
          | Jntype {desc=Ntype("String",[])} as s,Badd,Jntype {desc=Ntype("String",[])}  
          | Jntype {desc=Ntype("String",[])} as s,Badd,Jint
          | Jint,Badd,Jntype {desc=Ntype("String",[])} as s -> s
            (* ATTENTION il faudra transmettre l'info du int_to_str *)
          | _,Beq,_ | _,Bneq,_ ->
              verifie_sous_type jt_expr1 dexpr1.loc jt_expr2 env_typage ;
              verifie_sous_type jt_expr2 dexpr2.loc jt_expr1 env_typage ;
              Jboolean
          | _,_,_ -> raise (Typing_error {loc = dexpr1.loc ;
              msg = "Cette opérateur binaire ne s'applique pas avec ces types "
                   ^ (str_of_jtp jt_expr1) ^ " et " ^ (str_of_jtp jt_expr2)})
            (* Ce message d'erreur est terrible...
               On pourrait demander un binop desc pour commencer.
               Dans tous les cas il faudra être plus fin pour produire l'arbre de sortie *)
        end         

  and jtype_of_expr_s loc_expr_s env_typage env_vars = function
    | ESint n -> Jint
    | ESstr s -> Jntype {loc = loc_dum ; desc=Ntype("String",[])}
        (* Il faut absoluement que je fasse un Jstring, ça sera tellement plus simple *)
    | ESbool b -> Jboolean
    | ESthis ->
        if not Hashtbl.mem env_vars "this"
        then raise (Typing_error {loc = loc_expr_s ;
          msg = "Aucun this actuellement, probablement parce que dans Main"})
        else Hashtbl.find env_vars "this"
    | ESexpr dexpr -> jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc 
    | ESnew (dn,params_dexpr) ->
        let Ntype(id_c,l_ntypes) = dn.desc in
        if id_c = "Object"
        then begin if l_ntypes = [] then Jntype dn
            else raise (Typing_error {loc = dn.loc ;
              msg = "Le constructeur Object() n'attend pas de paramètre"}) end
        else begin match Hashtbl.find_opt c_constr id_c with
          | None -> raise (Typing_error {loc = dn.loc ;
              msg = id_c ^ " ne possède pas de constructeur." })
          | Some params_dn ->
              try List.iter2 
                (fun (dn : param desc) (dexpr : expr desc) ->
                  let jt_expr = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
                  verifie_sous_type jt_expr dexpr.loc dn.desc.typ.desc )
                params_dn params_dexpr ;
                Jntype dn
              with | Invalid_argument -> raise (Typing_error {loc = loc_expr_s ;
                msg = "Le constructeur de " ^ id_c 
                    ^ " est appelé sur trop ou pas assez de paramètres"})
        end
    
    | ESacces_meth dacces l_dexpr -> 
    | ESacces_var daccces ->
  

  let verifie_blocs_instrs (type_r : jtype desc option) loc_bloc 
        env_typage env_vars (instrs : instr desc list) = match instrs with
    | [] -> 
        begin match type_r with
        | None -> ()
        | Some dj -> raise (Typing_error {loc = loc_bloc ;
            msg = "Il manque un return à ces instructions, on attend "
                    ^ (str_to_jtp_opt type_r) })
        end
    | dinstr :: q -> begin match dinstr.desc with
        | Ireturn dexpr_opt ->
            let djo = match dexpr_opt with 
              | None -> None
              | Some dexpr ->
                  let jtype = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
                  Some {loc = dexpr.loc ; desc = jtype}
            in
            (* à cause de jtype desc option, qui est naze, il faudrait jtype option desc *)
            verifie_sous_type_opt djo type_retour env_typage
            (* Il faudrait VRAIMENT rattraper l'erreur, et préciser que c'est 
               pour faire office de type de retour *)
        | _ -> begin match dinstr.desc with
          | Ireturn _ -> failwith "déjà traité, ce cas n'arrive jamais"
          | Inil -> ()
          | Isimple dexpr_s -> 
              ignore (jtype_of_expr_s dexpr_s.loc env_typage env_vars dexpr_s.desc)
              (* Attention, ici on autorise ce genre de chose pour simplifier la
                 grammaire, mais en java c'est interdit, donc on ignore le retour *)
          | Idef (dacc,dexpr)
          end
          verifie_blocs_instrs type_r loc_bloc env_typage env_vars q 
      end
  in
  
  (* === Fonctions principales === *)
  let verifie_corps_c id_c = 
    let loc_c = Hashtbl.find env_typage.tab_loc id_c in 
    let env_typage = Hashtbl.find env_locaux id_c in
    let body = Hashtbl.find c_body id_c in
    let params_dn = List.map
      (fun (dpt : paramtype desc) ->
        {loc = dpt.loc ; desc = Ntype (dpt.desc.nom,dpt.desc.extds) })
      (Hashtbl.find ci_params id_c) in
    let type_this = Jntype {loc = loc_c ; desc = Ntype (id_c , params_dn)} in
    (* this est une variable spéciale, de type C<T1,...,Tk> *)
    let verifie_decl (decl : decl desc) = match decl.desc with
      | Dchamp _ -> () (* tout est déjà fait *)
      | Dmeth dmeth ->
          let env_vars = Hashtbl.create 10 in
          Hashtbl.add env_vars "this" type_this ;
          let meth = dmeth.desc in
          let pro = meth.info.desc in
          let type_retour = pro.typ in
          List.iter 
            (fun (dp : param desc) -> Hashtbl.add env_vars dp.desc.nom dp.desc.typ.desc)
            pro.params ;
          verifie_bloc_instrs type_retour decl.loc env_typage env_vars meth.body 
      
      | Dconstr dconstr -> 
          (* On pourrait faire une fonction auxiliaire, puisqu'on copie le cas précédent *)
          let env_vars = Hashtbl.create 10 in
          Hashtbl.add env_vars "this" type_this ;
          let constr = dconstr.desc in
          List.iter 
            (fun (dp : param desc) -> Hashtbl.add env_vars dp.desc.nom dp.desc.typ.desc)
            constr.params ;
          verifie_bloc_instrs None dconst.loc env_typage env_vars constr.body 
    in
    List.iter verifie_decl body ;
  in
  
  IdSet.iter verifie_corps_c (diff env_global.c (IdSet.of_list ["Object";"String"]))

  (* Enfin, on traite Main *)
  let env_vars = Hashtbl.create 10 in
  let loc_main = Hashtbl.find env_typage_global.tab_loc "Main" in
  verifie_bloc_instrs None loc_main env_typage_global env_vars !body_main ;
in

