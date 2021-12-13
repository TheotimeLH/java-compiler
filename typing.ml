open Ast
open Ast_typing

type error_typ = { loc : localisation ; msg : string }
exception Typing_error of error_typ
 
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
  let c_body : (ident,decl desc list) Hashtbl.t = Hashtbl.create 5 in 
  let c_constr : (ident,info_constr) Hashtbl.t = Hashtbl.create 5 in
  let body_main : instr desc list ref = ref [] in
  
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

      if IdSet.mem nom env_typage_global.ci
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Nom de classe ou interface déjà utilisé."})
      else (
        Hashtbl.add graph_c nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]} ;
        new_c nom )

    | Interface {nom ; params ; body} ->
      Hashtbl.add ci_params nom params ;
      Hashtbl.add i_body nom body ;
      Hashtbl.add env_typage_global.tab_loc nom ci.loc ;

      if IdSet.mem nom env_typage_global.ci
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Nom de classe ou interface déjà utilisé."})
      else (
        Hashtbl.add graph_i nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]} ;
        new_i nom )

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
    | Class {nom ; extd=Some cp ; implmts = l} ->
        init_extends nom [cp] ; 
        init_implements nom l ;
        let node_id1 = Hashtbl.find graph_c nom in
        graph_add_rel graph_c node_id1 cp
    | Interface {nom ; extds = l} ->
        init_extends nom l ;
        init_implements nom [] ;
        let node_i = Hashtbl.find graph_i nom in
        List.iter (graph_add_rel graph_i node_i) l 
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
    let dparams = Hashtbl.find ci_params ci in
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
  let substi_jt sigma jt = match jt with
    | Jboolean | Jint -> jt
    | Jtypenull -> failwith "Normalement, le parser fait que ça n'arrive pas"
    | Jntype dnt -> Jntype ({loc = dnt.loc ; desc = substi sigma dnt.desc})
  in
  let substi_dj sigma (dj : jtype desc) =
    {loc = dj.loc ; desc = substi_jt sigma dj.desc}
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
  let verifie_sous_type_opt (djo1 : jtype desc option) loc1 
    (djo2 : jtype desc option) env_typage = match djo1 , djo2 with
      | None , None -> () (* void et void *)
      | Some dj1 , Some dj2 ->
          verifie_sous_type dj1.desc dj1.loc dj1.desc env_typage
      | _ , _ -> raise (Typing_error {loc = loc1 ;
      msg = (str_of_djo djo1) ^ " n'est pas un sous-type de " ^ (str_of_djo djo2) })
  in
  (* ======================= *)

  (* === Bien Fondé === *)
  let rec verifie_bf jtyp env_typage = match jtyp with
    | Jboolean | Jint | Jtypenull -> () (* une fonction vérifie est à valeur dans unit *)
    | Jntype {loc ; desc = Ntype (id_ci,l_ntypes)} ->
        if not (IdSet.mem id_ci env_typage.ci)
          then raise (Typing_error {loc=loc ;
            msg = "Classe ou interface inconnue"}) ;
        if l_ntypes = [] then ()
        else begin
        (* id a des paramtypes, en particulier id n'est pas un paramtype *)
        let dparams = Hashtbl.find ci_params id_ci in
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
    let info_tmp = Hashtbl.create (List.length dparams) in
    (* (ident , info_paramtype_tmp) Hashtbl.t *)
    List.iter 
      (fun (p : paramtype desc) -> 
        Hashtbl.add env_typage.tab_loc (p.desc).nom p.loc ;
        Hashtbl.add info_tmp (p.desc).nom 
        {tk_mark = NotVisited ; tk_loc = p.loc ; 
         tk_contraintes = (p.desc).extds})
      dparams ;
    
    let recup_tk' tk = function (* cf la remarque précédente sur le comportement de java *)
      | [({desc = Ntype (tk',[])} : ntype desc)] 
          when IdSet.mem tk' env_typage.paramstype -> Some tk' 
      | _ -> None
    in

    let params_id_tri = ref [] in
    let rec parcours (tk : ident) =
      let info_tk = Hashtbl.find info_tmp tk in
      if info_tk.tk_mark = NotVisited 
      then begin 
        info_tk.tk_mark <- InProgress ; 
        (match (recup_tk' tk info_tk.tk_contraintes) with
          | None -> ()
          | Some tk' -> parcours tk' ) ;
        info_tk.tk_mark <- Visited ;
        params_id_tri := tk :: !params_id_tri end
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
            let info_tk' = Hashtbl.find info_tmp tk' in
            Hashtbl.add env_typage.extends tk 
              [{loc = info_tk'.tk_loc ; desc = Ntype (tk',[])}] ;
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
        if not (jtype_equal d_jtype.desc d_jtype'.desc)
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

  let heritage_d'une_surci id_ci loc_ci methodes_heritees env_typage (dci' : ntype desc) =
    let Ntype (id_ci',l_ntypes_ci') = dci'.desc in
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
                  ^ id_ci' ^ " avec le type de retour " ^ (str_of_djo meth'.typ)
                  ^ " mais aussi via " ^ meth''.id_ci ^ " avec le type de retour "
                  ^ (str_of_djo meth''.typ) 
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
    List.iter (heritage_d'une_surci id_ci loc_ci methodes_heritees env_typage)  extends ;
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
      (fun (dp : param desc) -> verifie_bf dp.desc.typ.desc env_typage)
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
          verifie_sous_type_opt meth.typ loc meth'.typ env_typage end ;
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
      heritage_d'une_surci id_t loc_t methodes_heritees env_typage dc_mere ;
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
        (Hashtbl.find env_typage.champs id_m) ; 
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
  let verifie_bf_et_i env_typage (di' : ntype desc) =
      verifie_bf (Jntype di') env_typage ;
      let Ntype (id_i',l_ntypes_i') = di'.desc in
      if not (IdSet.mem id_i' env_typage.i)
      then raise (Typing_error {loc = di'.loc ;
        msg = "On attendait une interface et non une classe/paramtype"})
  in
  let verifie_interface id_i=
    let env_typage = env_copy env_typage_global in

    (* Première étape : les paramstype *)
    verifie_et_fait_paramstype id_i env_typage ;

    (* Deuxième étape : les extends *)
    let extends = Hashtbl.find env_typage.extends id_i in
    List.iter (verifie_bf_et_i env_typage) extends ;
    
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
    let loc_c = Hashtbl.find env_typage.tab_loc id_c in
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
    heritage_d'une_surci id_c loc_c methodes env_typage d_mere ;
    let Ntype (id_m,l_ntypes_m) = d_mere.desc in
    let sigma = fait_sigma id_m d_mere.loc l_ntypes_m in
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
          if Hashtbl.mem champs nom
          then raise (Typing_error {loc = decl.loc ;
            msg = id_c ^ " hérite déjà d'un champ " ^ nom 
              ^ " il est interdit de rédéfinir un champ."})
            (* l'erreur vaut aussi si on définit 2 fois un champ au sein d'une classe *)
          else (verifie_bf dj.desc env_typage;
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
    List.iter (verifie_bf_et_i env_typage) implements ;
    let verification_implements (di : ntype desc) =
      let Ntype (id_i,l_ntypes_i) = di.desc in
      let meth_demandees = recup_methodes di env_typage in
      let verifie_meth nom (meth_i : info_methode) = 
        match Hashtbl.find_opt methodes nom with
        | None -> raise (Typing_error {loc = di.loc ;
            msg = id_c ^ " n'implémente pas " ^ id_i 
              ^ " parce qu'elle n'a pas de méthode " ^ nom})
        | Some meth_c -> 
            verifie_meme_parametres meth_i meth_c di.loc ;
            verifie_sous_type_opt meth_c.typ di.loc meth_i.typ env_typage
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
  (* Il nous reste à vérifier les corps, composés d'inscrutions. Pour cela on utilise
     en plus des env_typage (locaux), des env_vars une info_var IdMap.t 
     qui pour une variable locale donne son jtype et si elle est initialisée. 
     Ce booléen sert si on déclare une variable avec "I x;"
     "x" sera toujours de type I une interface, mais il faut lui trouver son type
     effectif, sinon que faire si on demande x.m() (même si l'interface I demande m();)

     Mais on ne peut pas garder le type effectif, car on ne le connait pas forcément :
     << I c;
        if (b) {c = new C(7);}
          {c = new A(4);}
      System.out.print(c.m());>>
     Selon la valeur de b, on utilise une méthode différente !

     On voit ici une autre difficulté, c peut être initialisée sous condition !
     Et là ça devient obscure, en effet si c est initialisée dans les deux options 
     (b true ou false), c'est toujours ok. En revanche si c est initilisée dans une 
     seule option, et si b est true ou false, alors on peut quand même considérer
     que c est toujours initialisée. Ahhhhhhhhhhhhhhhhhhhhhh

     Donc pour le coup j'ai besoin d'une Map, pour pouvoir chercher dans les deux branches
     voir quelles variables sont initialisées. Si certaines étaient dans la map mère,
     non initialisées, et qu'elles sont maintenant initialisées dans les deux chemins,
     alors elles deviennent initialisées dans la map mère.
     Pour b = true ou b = false, je fais un cas particulier.
     Il faut gérer les while de même.

     Ça se complique encore davantage avec ce genre de chose :
     << I c;
        int n = (c = new C(7)).m(); >>

     Voir tests_perso/test11.java pour plus d'exemples.

     J'utilise donc trois fonctions : jtype_of_acces, jtype_of_expr, jtype_of_expr_s
     qui renvoie un triplet (nom_var,jtype option,env_vars) 
     (excepté pour jtype_of_acces, voir plus bas)
      - nom_var renseigne le nom de la variable dont on parle: 
        - si c'est une variable on utilise le constructeur Nom of ident
        - si c'est un objet primitif, on utilise Muet (par exemple pour 42 ou null)
        - enfin si c'est un objet juste créé on utilise New
      - Some le jtype de ce dont on parle, None si void
      --> J'ai hate de passer les jtype option en Jvoid
      - La nouvelle Map env_vars (on a pu initialiser des variables)

     Exemple : 
     - pour (adrien.ville_natale.nb_d'habitants = 700) on renvoie (Nom "adrien",Some int)
     - pour (new C(7)).m() on renvoie (New,type de retour de m dans C) *)

  (* ATTENTION C'EST ICI QUE NOUS PRODUIRONS LE NOUVEL ARBRE DE SYNTAXE
     MAIS VU MON RETARD, JE TIENS D'ABORD À TESTER LE TYPEUR    *)

  (* === LES ACCES === *)
  let rec jtype_of_acces loc_acc env_typage env_vars b = function
    (* b : true si on demande quelque chose de modifiable : un champ ou une variable,
       faux sinon, ie si on demande une méthode.
       J'aurais pu faire deux fonctions complètement séparées.

       Cette fonction renvoie finalement un quadruplet 
       (nom_var,jtype option,jtype desc list , env_vars) :
         - Son nom (pour le coup toujours un Nom of ident)
         - Le type de la variable à laquelle on accède. (Pour un champ, le type du champ,
         pour une méthode, le type de retour de la méthode ! Potentiellement void... )
         - La liste types_params dans le cas d'une méthode, [] sinon
         - La nouvelle Map env_vars, car dans l'expr_simple on a pu la modifier *)
    | Aident id ->
      if b then 
        begin match (IdMap.find_opt id env_vars) with
        | Some {jt} -> (Nom id,Some jt,[],env_vars)
        | None -> 
          begin match (IdMap.find_opt "this" env_vars) with
          | Some {jt = Jntype dn} -> 
            let Ntype(id_c,_) = dn.desc in
            let champs = Hashtbl.find env_typage.champs id_c in
            begin match (Hashtbl.find_opt champs id) with
            | Some info_ch -> (Nom "this",Some info_ch.typ.desc ,[],env_vars)
            | None -> raise (Typing_error {loc = loc_acc ;
              msg = id ^ " est inconnue, ni une variable local, ni un champ de this"})
            end
          | _ (*None*) -> raise (Typing_error {loc = loc_acc ;
              msg = id ^ " est inconnue: pas une variable local et il n'y a pas de this \
                    dans le contexte actuel (probablement Main)"})
          end
        end
      else
        raise (Typing_error {loc = loc_acc ;
        msg = id ^ " ne peut être une méthode, une méthode s'écrit toujours en précisant \
              l'objet sur lequel elle est appliquée" })
    
    | Achemin (dexpr_s,id) ->
      begin match jtype_of_expr_s dexpr_s.loc env_typage env_vars dexpr_s.desc with
      (* ce qu'on nous donne est initialisé ! *)
      | (Muet,_,_) -> raise (Typing_error {loc = dexpr_s.loc ;
            msg = "Les objets primitifs n'ont pas de méthodes ou de champs" })
      | (nom_var, Some (Jntype dn),env_vars') ->
        let Ntype (id_ci,l_ntypes_ci) = dn.desc in
        let sigma = fait_sigma id_ci loc_dum l_ntypes_ci in
        (* On pourrait l'enregistrer dans env_vars... *)
        if b then
          if not (IdSet.mem id_ci env_typage.c)
          then raise (Typing_error {loc = dexpr_s.loc ;
            msg = "Est de type " ^ id_ci ^ " qui n'est pas une classe (ou un paramtype), \
                   et donc ne possède pas de champs (probablement une interface)"})
          else begin
          let champs = Hashtbl.find env_typage.champs id_ci in 
          begin match (Hashtbl.find_opt champs id) with
          | None -> raise (Typing_error {loc = loc_acc ;
              msg = id_ci ^ " ne possède pas de champ " ^ id })
          | Some champ ->
              (nom_var,Some (substi_jt sigma champ.typ.desc),[],env_vars')
          end end
        else begin
          let methodes = Hashtbl.find env_typage.methodes id_ci in
          begin match Hashtbl.find_opt methodes id with
          | None  -> raise (Typing_error {loc = loc_acc ;
              msg = id_ci ^ " ne possède pas de méthode " ^ id })
          | Some meth -> 
            (*AHHHHH Il faut que j'arrête avec ces jtype desc option
            déjà jtype option desc serait mieux, mais finalement je veux un Jvoid
            comme un Jstring *)
            (nom_var,
            begin match (substi_djo sigma meth.typ) with
            | None -> None
            | Some dj -> Some dj.desc
            end , meth.types_params , env_vars')
          end end
      
      | (_,_,_) -> raise (Typing_error {loc = dexpr_s.loc ;
            msg = "Les types primitifs n'ont pas de méthodes ou de champs" })
      end


  (* === LES EXPRESSIONS === *)
  (* Le <acces> = <expr> apparait aussi dans les instructions, donc je fais
     une fonction auxiliaire pour ne pas l'écrire deux fois. *)
  and acces_equal_expr env_typage env_vars (dacces : acces desc) (dexpr : expr desc) loc =
    let (_,jo_expr,env_vars') = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
    let (nom_var, jo_acces, _ , env_vars'') = 
      jtype_of_acces dacces.loc env_typage env_vars' true dacces.desc in
    (* J'ai fait env_vars -> env_vars' via l'expr -> env_vars'' via l'accès
       Mais je n'ai pas vérifié le comportement de java, peut-être que
       pour gérer l'accès on n'a pas les infos d'initialisation hérité de l'expr *)
    (* C'est l'occasion d'initialiser la variable si ce n'est déjà fait ! *)
    let env_vars''' = begin match nom_var with
    | Nom id_var -> 
        let info_var = IdMap.find id_var env_vars'' in
        IdMap.add id_var {jt = info_var.jt ; init = true} env_vars''
        (* On écrase l'ancienne *)
    | _ -> raise (Typing_error {loc = dacces.loc ;
        msg = "On ne peut pas modifier des valeurs, il faut nommer les variables !"}) 
    end in
    (* === *)
    begin match jo_expr,jo_acces with
    | None,None -> ()
    | Some jt_expr,Some jt_acces ->
        if not (sous_type jt_expr jt_acces env_typage)
        then raise (Typing_error {loc=loc ;
          msg = "Pour changer une valeur, il faut un sous-type de ce qui est demandé "
              ^ (str_of_jtp jt_expr) ^ " n'est pas un sous-type de "
              ^ (str_of_jtp jt_acces)})
    | _,_ -> raise (Typing_error {loc=loc ;
          msg = "Pour changer une valeur, il faut un sous-type de ce qui est demandé "
              ^ (str_of_jo jo_expr) ^ " n'est pas un sous-type de "
              ^ (str_of_jo jo_acces)})
    end ;
    (nom_var,jo_acces,env_vars''')

  (* Pour toutes les expressions *)
  and jtype_of_expr loc_expr env_typage env_vars = function
    | Enull -> (Muet,Some Jtypenull,env_vars)
    | Esimple dexpr_s -> jtype_of_expr_s dexpr_s.loc env_typage env_vars dexpr_s.desc
    | Eequal (dacces,dexpr) -> (* permet a = b = c qui change b en c puis a en b *)
        acces_equal_expr env_typage env_vars dacces dexpr loc_expr
    | Eunop (unop,dexpr) -> 
        let (_,jo_expr,env_vars') = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
        (* Si c'est bien un Jint ou un Jboolean, on passe forcément en Muet *)
        (Muet , begin match unop with
          | Unot -> 
              if jo_expr <> (Some Jboolean) 
              then raise (Typing_error {loc=dexpr.loc ;
                msg = "Le not s'applique sur un boolean"}) ;
              Some Jboolean
          | Uneg ->
              if jo_expr <> (Some Jint) 
              then raise (Typing_error {loc=dexpr.loc ;
                msg = "Le moins unaire s'applique sur un entier"}) ;
              Some Jint
        end , env_vars' )
    | Ebinop (dexpr1,binop,dexpr2) ->
        let (_,jo_expr1,env_vars') = jtype_of_expr dexpr1.loc env_typage env_vars dexpr1.desc in
        let (_,jo_expr2,env_vars'') = jtype_of_expr dexpr2.loc env_typage env_vars' dexpr2.desc in
        (* idem on peut passer en Muet *)
        (* j'ai fait env_vars -> env_vars' via l'expr 1 -> env_vars'' via l'expr2
           pour suivre l'idée d'évaluation paresseuse, mais je n'ai pas vérifier
           Il est fort probable qu'il faille faire env_vars -> env_vars1 et env_vars2
           pour ensuite les fusionner. *)
        begin match jo_expr1,jo_expr2 with
        | Some jt_expr1,Some jt_expr2 ->
          ( Muet, Some begin match jt_expr1,binop,jt_expr2 with
          | Jint,Badd,Jint | Jint,Bsub,Jint | Jint,Bmul,Jint
          | Jint,Bdiv,Jint | Jint,Bmod,Jint -> Jint
          | Jint,Blt,Jint | Jint,Ble,Jint
          | Jint,Bgt,Jint | Jint,Bge,Jint -> Jboolean
          | Jboolean,Band,Jboolean | Jboolean,Bor,Jboolean -> Jboolean
          | (Jntype {desc=Ntype("String",[])} as s),Badd,(Jntype {desc=Ntype("String",[])})  
          | (Jntype {desc=Ntype("String",[])} as s),Badd,Jint
          | Jint,Badd,(Jntype {desc=Ntype("String",[])} as s) -> s
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
          end , env_vars'' )
        | _,_ -> raise (Typing_error {loc = loc_expr ;
            msg = "Les opérations ne s'appliquent pas avec des expressions de type void"})
        end


  (* === LES EXPRESSIONS SIMPLES === *)
  and jtype_of_expr_s loc_expr_s env_typage env_vars = function
    | ESint n -> Muet,Some Jint,env_vars
    | ESstr s -> Muet,Some (Jntype {loc = loc_dum ; desc=Ntype("String",[])}),env_vars
        (* Il faut absoluement que je fasse un Jstring, ça sera tellement plus simple *)
    | ESbool b -> Muet,Some Jboolean,env_vars
    | ESthis ->
      begin match (IdMap.find_opt "this" env_vars) with
      | None -> raise (Typing_error {loc = loc_expr_s ;
          msg = "Aucun this actuellement, probablement parce que dans Main"})
      | Some {jt} -> (Nom "this",Some jt,env_vars)
      end
    | ESexpr dexpr -> jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc 
    | ESnew (dn,params_dexpr) ->
        verifie_bf (Jntype dn) env_typage ;
        let Ntype(id_c,l_ntypes) = dn.desc in
        if id_c = "Object"
        then begin if l_ntypes = [] then (New , Some (Jntype dn),env_vars)
            else raise (Typing_error {loc = dn.loc ;
              msg = "Le constructeur Object() n'attend pas de paramètre"}) end
        else begin match Hashtbl.find_opt c_constr id_c with
          | None -> raise (Typing_error {loc = dn.loc ;
              msg = id_c ^ " ne possède pas de constructeur, est-ce bien une classe \
                et non interface ou un paramtype par exemple" })
          | Some params_dn ->
              let env_vars' = ref env_vars in
              try List.iter2 
                (fun (dn : param desc) (dexpr : expr desc) ->
                  let (_,jo_expr,env_vars'') = 
                    jtype_of_expr dexpr.loc env_typage !env_vars' dexpr.desc in
                  let jt_expr = begin match jo_expr with
                  | None -> raise (Typing_error {loc = dexpr.loc ;
                      msg = "Cette expression est de type void, ce qui n'est jamais un \
                            paramètre recevable !"})
                  | Some jt -> jt end in
                  verifie_sous_type jt_expr dexpr.loc dn.desc.typ.desc env_typage ;
                  env_vars' := env_vars'' )
                params_dn params_dexpr ;
                (New , Some (Jntype dn) , !env_vars')
              with | Invalid_argument _ -> raise (Typing_error {loc = loc_expr_s ;
                msg = "Le constructeur de " ^ id_c 
                    ^ " est appelé sur trop ou pas assez de paramètres"})
        end

    | ESacces_meth (dacces,l_dexpr) ->
        let nom_var,jo_acces,types_params,env_vars' = 
          jtype_of_acces dacces.loc env_typage env_vars false dacces.desc in
        begin match nom_var with
        | Muet | New -> ()
        | Nom id -> 
          let {init} = IdMap.find id env_vars in
          if not init 
          then raise (Typing_error {loc = loc_expr_s ;
            msg = id ^ " n'est peut-être pas initialisée, il faut qu'elle soit plus \
                  clairement initialisée." })
        end ;
        let env_vars' = ref env_vars' in
        begin
        try List.iter2
          (fun (dj_demande : jtype desc) (dexpr_donnee : expr desc) ->
            let (_,jo_expr,env_vars'') = 
              jtype_of_expr dexpr_donnee.loc env_typage !env_vars' dexpr_donnee.desc in
            let jt_expr = begin match jo_expr with
            | None -> raise (Typing_error {loc = dexpr_donnee.loc ;
              msg = "Cette expression est de type void, ce qui n'est jamais un \
                    paramètre recevable !"})
            | Some jt -> jt end in
            verifie_sous_type jt_expr dexpr_donnee.loc dj_demande.desc env_typage ;
            env_vars' := env_vars'')
          types_params l_dexpr
        with | Invalid_argument _ -> raise (Typing_error {loc = loc_expr_s ;
            msg = "La méthode n'est pas appliquée avec le bon nombre de paramètres"})
        end ;
        (nom_var,jo_acces,!env_vars')
    | ESacces_var dacces ->
        let nom_var,jo_acces,_,env_vars' = 
          jtype_of_acces dacces.loc env_typage env_vars true dacces.desc in
        begin match nom_var with
        | Muet | New -> ()
        | Nom id -> 
          let {init} = IdMap.find id env_vars in
          if not init 
          then raise (Typing_error {loc = loc_expr_s ;
            msg = id ^ " n'est peut-être pas initialisée, il faut qu'elle soit plus \
                  clairement initialisée." })
        end ;
        (nom_var,jo_acces,env_vars')
  in
  

  (* === LES INSTRUCTIONS === *)
  let rec verifie_bloc_instrs (type_r : jtype desc option) loc_bloc 
        env_typage env_vars (instrs : instr desc list) = match instrs with
    | [] -> (* Si on attendait un return, on en a pas trouvé... *)
      begin match type_r with
      | None -> ()
      | Some dj -> raise (Typing_error {loc = loc_bloc ;
        msg = "Il manque un return à ces instructions, on attend " ^ (str_of_djo type_r) })
      end ;
      env_vars 
      (* On renvoie l'env_vars, utile pour récupérer les initialisations
         de variables au sein de sous bloc d'instructions *)

    | dinstr :: q -> 
      begin match dinstr.desc with
      | Ireturn dexpr_opt ->
        let djo,env_vars' = match dexpr_opt with 
          | None -> None,env_vars
          | Some dexpr ->
            let (_,jo_expr,env_vars') = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
            begin match jo_expr with
            | None -> None
            | Some jt -> Some {loc = dexpr.loc ; desc = jt}
            end (* foutu jtype desc option *) , env_vars'
        in
        verifie_sous_type_opt djo dinstr.loc type_r env_typage ;
        (* Il faudrait VRAIMENT rattraper l'erreur, et préciser que c'est 
           pour faire office de type de retour *)
        env_vars'
      
      | Inil -> verifie_bloc_instrs type_r loc_bloc env_typage env_vars q 
          (* Au début j'ai voulu séparer Ireturn du reste, pour n'écrire 
             << verifie_bloc_instrs type_r loc_bloc env_typage env_vars q >>
             qu'une fois, mais parfois l'env_vars change ! 
             J'aurais pu faire renvoyer env_vars' au matching*)

      | Isimple dexpr_s -> 
        let (_,_,env_vars') = jtype_of_expr_s dexpr_s.loc env_typage env_vars dexpr_s.desc in
        (* Attention, ici on autorise ce genre de chose pour simplifier la
           grammaire, mais en java c'est interdit, d'ailleurs on ignore le retour
           excepté la modification de l'env_envars *)
        verifie_bloc_instrs type_r loc_bloc env_typage env_vars' q 

      | Iequal (dacces,dexpr) ->
        let (_,_,env_vars') = acces_equal_expr env_typage env_vars dacces dexpr dinstr.loc in
        verifie_bloc_instrs type_r loc_bloc env_typage env_vars' q
      
      | Idef (dj,id) ->
        begin match IdMap.find_opt id env_vars with
        | Some _ -> raise (Typing_error {loc = dinstr.loc ;
          msg = "Il est interdit de redéfinir une variable"})
        | None ->
          let env_vars' = IdMap.add id {jt = dj.desc ; init = false} env_vars in
          verifie_bloc_instrs type_r loc_bloc env_typage env_vars' q
        end

      | Idef_init (dj,id,dexpr) ->
        let (_,jo_expr,env_vars') = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
        begin match jo_expr with
        | None -> raise (Typing_error {loc = dexpr.loc ;
          msg = "Problème pour initialiser " ^ id ^ "on attendait une valeur de type " 
              ^ (str_of_jtp dj.desc) ^ " et on a reçu un type Void" })
        | Some jt_expr -> verifie_sous_type jt_expr dexpr.loc dj.desc env_typage
        end ;
        begin match IdMap.find_opt id env_vars' with
        | Some _ -> raise (Typing_error {loc = dinstr.loc ;
          msg = "Il est interdit de redéfinir une variable"})
        | None ->
          let env_vars' = IdMap.add id {jt = dj.desc ; init = true} env_vars' in
          verifie_bloc_instrs type_r loc_bloc env_typage env_vars' q
        end
        (* On pourrait faire une fonction auxiliaire pour éviter de se répéter *)

      | Iif(dexpr,dinstr1,dinstr2) ->
        let (_,jo_expr,env_vars') = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
        (* J'ai mis les cas particulier avec true ou false, et de la vérification paresseuse *)
        if jo_expr <> Some Jboolean 
        then raise (Typing_error {loc = dexpr.loc ;
          msg = "La condition d'un if doit être un booléen !" }) ;
        let env_vars'' = begin match dexpr.desc with
        | Esimple {desc = ESbool true} ->
          let env_vars1 = verifie_bloc_instrs None dinstr1.loc env_typage env_vars' [dinstr1] in
          IdMap.mapi (fun id _ -> IdMap.find id env_vars1) env_vars'
        | Esimple {desc = ESbool false} ->
          let env_vars2 = verifie_bloc_instrs None dinstr2.loc env_typage env_vars' [dinstr2] in
          IdMap.mapi (fun id _ -> IdMap.find id env_vars2) env_vars'
        | _ ->
          let env_vars1 = verifie_bloc_instrs None dinstr1.loc env_typage env_vars' [dinstr1] in
          let env_vars2 = verifie_bloc_instrs None dinstr2.loc env_typage env_vars' [dinstr2] in
          IdMap.mapi 
            (fun id _ ->
              let info1 = IdMap.find id env_vars1 in
              let info2 = IdMap.find id env_vars2 in
              {jt = info1.jt ; init = (info1.init && info2.init)})
            env_vars'
          end in
        verifie_bloc_instrs type_r loc_bloc env_typage env_vars'' q

      | Iwhile(dexpr,dinstr') ->
        let (_,jo_expr,env_vars') = jtype_of_expr dexpr.loc env_typage env_vars dexpr.desc in
        if jo_expr <> Some Jboolean 
        then raise (Typing_error {loc = dexpr.loc ;
          msg = "La condition d'un while doit être un booléen !" }) ;
        (* On ne peut pas faire confiance au while pour initialiser des variables, donc
           on ne fait rien du nouvel env_vars *)
        ignore (verifie_bloc_instrs None dinstr'.loc env_typage env_vars' [dinstr']) ;
        env_vars'

      | Ibloc(l_dinstrs) ->
        let env_vars' = verifie_bloc_instrs None dinstr.loc env_typage env_vars l_dinstrs in
        (* Le type de retour d'un sous bloc doit bien être Void ? et non type_r *)
        verifie_bloc_instrs type_r loc_bloc env_typage env_vars' q
      end 
  in
  
  (* === Fonctions principales === *)
  let verifie_corps_c id_c = 
    let env_typage = Hashtbl.find env_locaux id_c in
    let loc_c = Hashtbl.find env_typage.tab_loc id_c in 
    let body = Hashtbl.find c_body id_c in
    let params_dn = List.map
      (fun (dpt : paramtype desc) ->
        {loc = dpt.loc ; desc = Ntype (dpt.desc.nom,[]) })
      (Hashtbl.find ci_params id_c) in
    let info_this = 
      { jt = Jntype {loc = loc_c ; desc = Ntype (id_c , params_dn)} ; init = true} in
    (* this est une variable spéciale, de type C<T1,...,Tk> *)
    let verifie_decl (decl : decl desc) = match decl.desc with
      | Dchamp _ -> () (* tout est déjà fait *)
      | Dmeth dmeth ->
          let env_vars = ref (IdMap.singleton "this" info_this) in
          let meth = dmeth.desc in
          let pro = meth.info.desc in
          let type_retour = pro.typ in
          List.iter 
            (fun (dp : param desc) -> 
              env_vars := IdMap.add dp.desc.nom {jt = dp.desc.typ.desc ; init = true} !env_vars )
            pro.params ;
          ignore (verifie_bloc_instrs type_retour decl.loc env_typage !env_vars meth.body)
      
      | Dconstr dconstr -> 
          (* On pourrait faire une fonction auxiliaire, puisqu'on copie le cas précédent *)
          let env_vars = ref (IdMap.singleton "this" info_this) in
          let constr = dconstr.desc in
          List.iter 
            (fun (dp : param desc) -> 
              env_vars := IdMap.add dp.desc.nom {jt = dp.desc.typ.desc ; init = true} !env_vars )
            constr.params ;
          ignore (verifie_bloc_instrs None dconstr.loc env_typage !env_vars constr.body)
    in
    List.iter verifie_decl body ;
  in
  
  IdSet.iter verifie_corps_c 
    (IdSet.diff env_typage_global.c (IdSet.of_list ["Object";"String"])) ;

  (* Enfin, on traite Main *)
  let env_vars = IdMap.empty in
  let loc_main = Hashtbl.find env_typage_global.tab_loc "Main" in
  ignore (verifie_bloc_instrs None loc_main env_typage_global env_vars !body_main)

