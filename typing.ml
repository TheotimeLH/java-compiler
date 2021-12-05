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
  let tab_pos_ci = Hashtbl.create 10 in (* Hashtbl : id -> loc *)
  let graph_c = Hashtbl.create 5 in (* Hashtbl : id -> node *)
  let graph_i = Hashtbl.create 5 in (* Hashtbl : id -> node *)
  let ci_methodes = Hashtbl.create 5 in 
    (* Hashtbl : id -> MethSet
       Methodes demandées pour i, présente pour c, 
       y compris indirectement via les héritages ! *)
  let ci_params = Hashtbl.create 5 in 
    (* Hashtbl : id (ci) -> paramtype desc list 
           * (Hashtbl : id (T) -> MethSet des méthodes que possède T
           * (Hashtbl : id (T) -> ChSet idem 
       Pour garder ces informations après la vérification des classes. 
       Rem : on n'a pas besoin de ces informations pour les interfaces. *)
  let i_body = Hashtbl.create 5 in (* Hashtbl : id -> proto desc list *)
  let c_body = Hashtbl.create 5 in (* Hashtbl : id -> decl desc list *)
  let c_champs = Hashtbl.create 5 in 
  let body_main = ref [] in (* instr desc list *)
  (* Rem : 
     Toutes ces informations sont globales, seules les "vraies" ci en ont 
     (a contrario des paramtype). Récupérer via l'arbre de syntaxe d'entrée 
     ou construite lors des vérifications des i puis des c *)
  
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
    | Class {nom ; params ; body} ->
      Hashtbl.add ci_params nom params ;
      Hashtbl.add c_body nom body ;
      Hashtbl.add tab_pos_ci nom ci.loc ;

      if IdSet.mem env_typage_global.ci nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Nom de classe ou interface déjà utilisé."})
      else (
        Hashtbl.add graph_c nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
        new_c nom ;
    | Interface {nom ; params ; body} ->
      Hashtbl.add ci_params nom params ;
      Hashtbl.add i_body nom body ;
      Hashtbl.add tab_pos_ci nom ci.loc ;

      if IdSet.mem env_typage_global.ci nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Nom de classe ou interface déjà utilisé."})
      else (
        Hashtbl.add graph_i nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
        new_i nom ;
    | Main l -> 
      Hashtbl.add tab_pos_ci "Main" ci.loc ;
      body_main := l
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
  let fait_sigma ci loc l_ntypes =
    let sigma = Hashtbl.create (List.length l_ntypes) in
    let params_id = params_to_ids (Hashtbl.find ci_params ci) in
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
        let params_id = params_to_ids (Hashtbl.find ci_params id) in 
        (* T1 , ... , Tn, juste les idents *)
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
    contraintes = Hashtbl.copy e.contraintes }
  in
  (* Remarque : on aurait mieux fait d'utiliser des Map et non des Hashtbl :/ *) 
  
  (* === Vérification des paramstype === *)
  (* Pour une ci X<T1,...,Tn> il faut vérfier que les contraintes (/les extends)
     des Ti ne forment pas de cycle, puis on les traite dans un ordre topologique.
     On vérifie que les theta_i sont connus, et que ce sont des interfaces pour i>1.
     Si les conditions sont vérifiés, on rajoute les interfaces dans l'env_typage.  
     
     REMARQUE sur le comportement de java, on peut avoir Tk extends Tk' 
     MAIS dans ce cas Tk' doit être l'unique contrainte ! *)
  let verifie_et_fait_paramstype (ci : ident) env_typage =
    let params = Hashtbl.find ci_params ci in
    let params_id = params_to_ids params in
    env_typage.paramstype <- IdSet.of_list params_id ;
    let info = Hashtbl.create (List.length params) in
    List.iter 
      (fun (p : paramtype desc) -> 
        Hashtbl.add info (p.desc).nom 
        (NotVisited, p.loc, (p.desc).extds) )
      params ;
    
    let recup_tk' tk = function (* cf la remarque précédente *)
      | [({desc = Ntype (tk',[])} : ntype desc)] 
          when IdSet.mem tk' env_typage.paramstype -> Some tk' 
      | _ -> None
    in

    let params_tri = ref [] in
    let rec parcours (tk : ident) =
      let (tk_mark,tk_loc,tk_contraintes) = Hashtbl.find info tk in
      if tk_mark = NotVisited 
      then begin Hashtbl.replace info tk (InProgress,tk_loc,tk_contraintes) ;
         (match (recup_tk' tk tk_contraintes) with
          | None -> ()
          | Some tk' -> parcours tk' )
         Hashtbl.replace info tk (Visited,tk_loc,tk_contraintes) ;
         params_tri := tk :: !params_tri ; end
      else if tk_mark = InProgress
      then raise (Typing_error {loc = tk_loc ;
            msg = "Il y a un cycle dans les paramstype"})
    in
    
    List.iter parcours params_id ;

    (* FINALEMENT peu importe dans quels sens on vérifie les paramstype,
       puisque soit cas 1 on a Tk extends Tk', auquel cas c'est ok.
       Soit cas 2 Tk ne dépend pas de d'autres paramstype.

       D'ailleurs dans le cas 2 quand on fait les vérications, si on tombe sur
       un Tk' il faut planter. Malheureusement ici je le fais planter sur un 
       "Tk' est inconnu", ce serait beaucoup mieux de dire "Tk' est un paramtype, 
       donc Tk' est une contrainte parmi d'autres ce qui est interdit".
       Actuellement ma solution est de ne pas mettre les T dans l'env...
       et les rajouter seulement après les vérifications *)

    let verifie (tk : ident) = 
      let (_,_,tk_contraintes) = Hashtbl.find info tk in
      match recup_tk' tk tk_contraintes with (* Pour faire les relations *)
        | Some tk' ->
            Hashtbl.add env_typage.extends tk 
              [{loc = tk'_loc ; desc = Ntype (tk',[])}] ;
            Hashtbl.add env_typage.implements tk []
        | None -> begin
            match tk_contraintes with 
            | [] -> 
                Hashtbl.add env_typage.extends tk [dobj] ;
                Hashtbl.add env_typage.implements tk [] 

            | (dci : ntype desc) :: q ->
                verifie_bf (Jntype dci) env_typage ;
                let Ntype (id_ci,l_ntypes_ci) = dci.desc in
                if IdSet.mem id_ci env_typage.c
                then (Hashtbl.add env_typage.extends tk [dci] ;
                      Hashtbl.add env_typage.implements tk [])
                else (
                  Hashtbl.add env_typage.extends tk [dobj] ;
                  Hashtbl.add env_typage.implements tk [dci]) ;
                List.iter (* On vérifie que les contraintes suivantes st des interfaces *)
                  (fun (dn : ntype desc) -> 
                    verifie_bf (Jntype dn) env_typage ;
                    let Ntype (id',l_ntypes') = dn.desc in
                    if not (IdSet.mem id' env_typage.i)
                    then raise (Typing_error {loc = dn.loc ;
                        msg = "On attend des interfaces en contrainte supplémentaire"})
                  ) q ;
                let h = Hashtbl.find env_typage.implements tk in
                Hashtbl.replace env_typage.implements tk (h @ q)
        end
    in
    List.iter verifie params_id ;

    List.iter (fun tk ->
      let (_,_,tk_contraintes) = Hashtbl.find info tk in
       Hashtbl.add env_typage.contraintes tk tk_contraintes ;
       env_typage.ci <- IdSet.add tk env_typage.ci ;
       env_typage.c <- IdSet.add tk env_typage.c
      ) params_id 
  in
  (* ======================= *)

  (* === Vérification redéfinition d'une méthode === *)
  let rec verifie_redef_methode (meth : ty_methode) loc id_ci env_typage =
    let extends = Hashtbl.find env_typage.extends id_ci in
    List.iter 
      (fun (dci' : ntype desc) ->
        let Ntype (id_ci',l_ntypes_ci') = dci'.desc in
        let methodes_ci' = Hashtbl.find ci_methodes id_ci' in
        if begin IdSet.exists (* si la méthode est présente à un niveau on ne remonte pas *) 
          (fun (meth' : ty_methode) ->
            if meth'.nom = meth.nom
            then begin
              begin match meth.typ,meth'.typ with
                | None,None -> () (* void *)
                | Some djtype,Some djtype' -> 
                    verifie_sous_type djtype.desc djtype.loc djtype'.desc env_typage
                | _,_ -> raise (Typing_error {loc = loc ;
                     msg = (str_of_jtp_opt meth.typ) 
                        ^ " n'est pas un sous type de "
                        ^ (str_of_jtp_opt meth'.typ) 
                        ^ " ce qu'il faudrait pour une redéfinition de méthode" })
              end ;
              begin try List.iter2
                (fun (d_jtype : jtype desc) (d_jjype' : jtype desc) ->
                  if not (jtype_equal d_jtype.desc djtype'.desc)
                  then raise (Typing_error {loc = d_jtype.loc ;
                    msg = "Dans une rédéfinition de méthode \
                           il faut garder les mêmes types pour les paramètres"})  ) 
                meth.types_params meth'.types_params
              with | Invalid_argument _ -> 
                raise (Typing_error {loc = loc ;
                    msg = "Dans une rédéfinition de méthode \
                           il faut garder le même nombre de paramètres"}) 
              end ;
              true end
            else false (* Nouvelle méthode *) )
          methodes_ci' end
        then ()
        else 
          (* On part chercher plus haut dans les extends si la méthode existait déjà *)
          verifie_redef_methode meth loc id_ci' env_typage
      )
      extends
  in
  let verifie_et_fait_methode (type_retour : jtype desc option)  nom params loc env_typage = 
    (* vérifie type de retour *)
    begin match type_retour with
      | None -> ()
      | Some tr -> verifie_bf tr.desc env_typage
    end ;
    (* vérifie type des paramètres *)
    List.iter 
      (fun (dp : param desc) ->
        let p = dp.desc in
        verifie_bf p.desc env_typage)
      params ;
    (* vérifie rédéfinition propre *)
    let types_params = 
      List.map (fun (dp : param desc) -> (dp.desc).typ) params in
    let meth = {nom = nom ; typ = type_retour ; types_params = types_params} in
    verifie_redef_methode meth loc id_i env_typage ;
    meth 
  in
  let herite_methode extends loc_i =
    (* Renvoie un MethSet contenant toutes les méthodes héritées.
       
       ATTENTION : si une méthode est présente dans deux classes mères, alors
       il faut les mêmes arguments, et il faut une relation entre les types de
       retour, typiquement si dans une des classes/interfaces mères on a T1 m() et dans
       une autre T2 m(), alors il faut T1 extends(généralisée) T2 ou T2 extends T1
       (en particulier T1 et T2 doivent être deux classes ou deux interfaces).
       auquel cas le type de retour hérité sera le plus petit des différents 
       type de retour. 
       Ensuite si on redéfinit il faudra un sous-type de ce type hérité. *)
    let methodes_heritees = MethSet.empty in
    let heritage_d'une_surci (dci : ntype desc) =
      let 
      let sur_methode = Hashtbl.find ci_methodes 
  (* ======================= *)


  (* === Les interfaces === *)
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
       de même type, et que le type de retour est un sous-type. *)

    let (body : proto desc list) = Hashtbl.find i_body id_i in
    let l_methodes = 
      List.map 
        (fun (d_proto : proto desc) -> 
          let pro = d_proto.desc in
          verifie_et_fait_methode pro.typ pro.nom pro.params d_proto.loc env_typage)
        (Hashtbl.find i_body id_i) in
    Hashtbl.add ci_methodes id_i (MethSet.of_list l_methodes)
    (* Attention : les méthodes partent dans l'env global, via ci_methodes !! *)
  in
  
  List.iter verifie_interface !list_intf ;
  (* ======================= *)

  let verifie_classe id_c =
    (* Ici on veut vérifier les héritages et déclarer les méthodes, la vérification
       du corps et la production du nouvel arbre de syntaxe viennent après.  *)
    let env_typage = env_copy env_typage_global in

    (* Première étape : les paramstype *)
    verifie_et_fait_paramstype id_i env_typage ;  
    
    (* Deuxième étape : la sur-classe *)
    let d_mere = List.hd (Hashtbl.find env_typage.extends id_c) in
    (* Une classe hérite toujours d'une seule autre classe, possiblement d'Object,
       exceptée pour Object, mais qu'on n'a pas besoin de traiter. *)
    let Ntype(id_mere,l_ntypes_mere) = d_mere.desc in
    if id_mere = "String"
    then raise (Typing_error {loc=d_mere.loc ;
      msg = "On ne doit pas hériter de la classe String" }) ;
    if not (IdSet.mem id_mere env_typage.c)
    then raise (Typing_error {loc = d_mere.loc ;
      msg = "On attendait une classe et non une interface"}) ;
    if (IdSet.mem id_mere env_typage.paramstype)
    then raise (Typing_error {loc = d_mere.loc ;
      msg = "Une classe ne peut étendre un de ses paramstype, beurk"}) ;
    verifie_bf (Jntype d_mere) env_typage ;
    
       
    (* Troisième étape les implements *)
    let implements = Hashtbl.find env_typage.implements id_c in
    List.iter verifie_bf_et_i implements ;

    (* Quatrième étape vérification du corps *)
    let (body : decl desc list) = Hashtbl.find c_body id_c in
    let l_champs = ref [] in
    let l_methodes = ref [] in
    let verifie_decl = function
      | Dvar (djtype,nom) ->
          verifie_bf djtype.desc ; 

    ATTENTION À RAJOUTER STRING.EQUALS ET TRAITER SYSTEM.OUT.PRINT ET PRINTLN
