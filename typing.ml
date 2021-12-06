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

let type_fichier l_ci =
  (* ===== LES VARIABLES GLOBALES ===== *)
  let tab_pos_ci = Hashtbl.create 10 in (* Hashtbl : id -> loc *)
  let graph_c = Hashtbl.create 5 in (* Hashtbl : id -> node *)
  let graph_i = Hashtbl.create 5 in (* Hashtbl : id -> node *)
  let ci_methodes = Hashtbl.create 5 in 
    (* Hashtbl : id -> MethSet
       Methodes demandées pour i, présente pour c, 
       y compris indirectement via les héritages ! *)
  let ci_params = Hashtbl.create 5 in 
    (* Hashtbl : id (ci) -> ty_params
       Avec { dparams :  paramtype desc list ;
                | Liste des paramstype avec leurs contraintes. 
              tbl_params_methodes : Hashtbl : id (T) -> MethSet ;
                | Table des méthodes que possède T, utile uniquement 
                | pour des paramstype de classe, pour les instructions.
                | Dans le cas d'interface, on met une Hashtbl vide.
              tbl_params_champs : Hashtbl : id (T) -> ChSet      *)
  let i_body = Hashtbl.create 5 in (* Hashtbl : id -> proto desc list *)
  let c_body = Hashtbl.create 5 in (* Hashtbl : id -> decl desc list *)
  let c_champs = Hashtbl.create 5 in (* Hashtbl : id -> ChSet *)
  let body_main = ref [] in (* instr desc list *)
  (* Rem : 
     Toutes ces informations sont globales, seules les "vraies" ci en ont 
     (a contrario des paramstype). Récupérées via l'arbre de syntaxe d'entrée 
     ou construite lors des vérifications des i puis des c. *)
  
  let params_to_ids params = (* T1 , ... , Tn, juste les idents *)
    List.map (fun (p : paramtype desc) -> (p.desc).nom) params 
  in 
  
  let env_typage_global = {
    paramstype = IdSet.empty ; 
    ci = IdSet.empty ;
    c = IdSet.empty ; 
    i = IdSet.empty ;
    extends = Hashtbl.create 5 ;
    implements = Hashtbl.create 5 } in
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
  
  Hashtbl.add ci_methodes "String" 
    (MethSet.singleton 
      {nom = "equals" ; 
       typ = Some ({loc = loc_dum ; desc = Jboolean} : jtype desc) ;
       types_params = []} ) ;
  Hashtbl.add ci_champs "String" ChSet.empty ;
  Hashtbl.add ci_methodes "Object" MethSet.empty ;
  Hashtbl.add ci_champs "Object" ChSet.empty ;


  (* ===== GRAPHES DES RELATIONS ENTRE LES C / LES I ===== *)
  (* On commence par récupérer toutes les relations, pour pouvoir traiter les I PUIS 
     les C dans un ordre topologique.
     ATTENTION, contrairement à ce qu'on pourrait penser, si on a :
     " class A <T extends B> ", A ne dépend pas pour autant de B.
     
     On en profite pour décortiquer l'arbre de syntaxe, 
     et mettre les informations dans nos variables globales. *)

  let tbl_empty_meth = Hashtbl.create 1 in
  let tbl_empty_ch = Hashtbl.create 1 in
  (* Les tables tbl_params_methodes et tbl_params_champs 
     des interfaces resteront vides, on en utilise qu'une seule.
     Attention, on a deux tbl_empty, car pas de même type. *)  
  let init_params (nom : ident) params b =
    Hashtbl.add ci_params nom
      {dparams = params ;
       tbl_params_methodes = if b then (Hashtbl.create 5) else tbl_empty_meth ;
       tbl_params_methodes = if b then (Hashtbl.create 5) else tbl_empty_ch }
  in 
  
  (* === Ajout des noeuds === *)
  let node_obj = {id="Object" ; mark = NotVisited ; prec=[] ; succ=[]} in

  let graph_add_node ci = match ci.desc with
    | Class {nom ; params ; body} ->
      init_params nom params true ;
      Hashtbl.add c_body nom body ;
      Hashtbl.add tab_pos_ci nom ci.loc ;

      if IdSet.mem env_typage_global.ci nom
        then raise (Typing_error {loc = ci.loc ; 
            msg = "Nom de classe ou interface déjà utilisé."})
      else (
        Hashtbl.add graph_c nom {id=nom ; mark = NotVisited ; prec=[] ; succ=[]}
        new_c nom ;
    | Interface {nom ; params ; body} ->
      init_params nom params false ;
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
    then raise (Typing_error {loc = Hashtbl.find tab_pos_ci n.id ;
          msg = "Il y a un cycle dans les héritages !"})
  in

  let list_cl = ref [] in (* ident list *)
  parcours list_cl node_obj ; (* Object est en tête *)
  
  let list_intf = ref [] in (* ident list *)
  Hashtbl.iter (fun i n -> parcours list_intf n) graph_i ;
  
  
  (* ===== Sous-type / Extends / Implements Généralisées / Bien fondé ===== *)
  (* ATTENTION, là on utilise les relations, on ne les vérifie pas *)
  (* Les fonctions sont des tests, par exemple verifie_bf vérifie si un type est bien
     fondé, si c'est le cas le retour est unit, en revanche sinon on raise l'erreur
     et on peut ainsi localiser très proprement le problème.   *)

  (* === Pour les substitutions des paramstype avec sigma === *)
  let fait_sigma ci loc l_ntypes =
    let sigma = Hashtbl.create (List.length l_ntypes) in
    let dparams = (Hashtbl.find ci_params ci_params ci).dparams in
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
        let dparams = (Hashtbl.find ci_params ci_params ci).dparams in
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

  (* === Pour créer des env_typages locaux === *)
  let env_copy e =
    {paramstype = e.paramstype ;
    ci = e.ci ; c = e.c ; i = e.i ;
    extends = Hashtbl.copy e.extends ;
    implements = Hashtbl.copy e.implements }
  in
  (* Remarque : on aurait mieux fait d'utiliser des Map et non des Hashtbl :/ *) 
  
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
     utiles pour le traitement du corps des classes sont gardées dans ci_params. *)
     
  let verifie_et_fait_paramstype (ci : ident) env_typage =
    let dparams = (Hashtbl.find ci_params ci_params ci).dparams in
    let params_id = params_to_ids dparams in (* T1 , ... , Tn, juste les idents *)
    env_typage.paramstype <- IdSet.of_list params_id ;
    let info_tmp = Hashtbl.create (List.length params) in
    (* (ident , info_paramtype_tmp) Hashtbl.t *)
    List.iter 
      (fun (p : paramtype desc) -> 
        Hashtbl.add info_tmp (p.desc).nom 
        {tk_mark = NotVisited ; tk_loc = p.loc ; 
         tk_contraintes = (p.desc).extds})
      params ;
    
    let recup_tk' tk = function (* cf la remarque précédente sur le comportement de java *)
      | [({desc = Ntype (tk',[])} : ntype desc)] 
          when IdSet.mem tk' env_typage.paramstype -> Some tk' 
      | _ -> None
    in

    let params_tri = ref [] in
    let rec parcours (tk : ident) =
      let info_tk = Hashtbl.find info_tmp tk in
      if info_tk.tk_mark = NotVisited 
      then begin info_tk.tk_mark <- InProgress ; 
         (match (recup_tk' tk info_tk.tk_contraintes) with
          | None -> ()
          | Some tk' -> parcours tk' )
         info_tk.tk_mark <- Visited ;
         params_tri := tk :: !params_tri ; end
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
       peut-être un jour une meilleure façon de faire. *)

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
      (fun (d_jtype : jtype desc) (d_jjype' : jtype desc) ->
        if not (jtype_equal d_jtype.desc djtype'.desc)
        then raise (Typing_error {loc = d_jtype.loc ;
          msg = "Deux méthodes en relation doivent avoir des paramètres de même types."}))
      meth.types_params meth'.types_params
    with | Invalid_argument _ -> 
        raise (Typing_error {loc = loc ;
          msg = "Deux méthodes en relation doivent avoir autant de paramètres."})
  in

  
  let herite_methodes id_ci loc_ci =
    (* Renvoie un MethSet contenant toutes les méthodes héritées.
       
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
       les ci_meres contiennent déjà celles des ancêtres. *)

    let methodes_heritees = Hashtbl.create 5 in
    (* (ident , (ty_methode,ident)) Hashtbl.t 
       Ici beaucoup plus pratique qu'un MethSet, car on veut retrouver 
       les méthodes déjà héritées, à partir de leur nom. 
       On sauvegarde aussi le nom de la ci par laquelle on hérite, pour 
       envoyer des messages d'erreurs précis. *)
    let heritage_d'une_surci (dci' : ntype desc) =
      let Ntype (id_ci',_) = dci'.desc in
      let sur_methodes = Hashtbl.find ci_methodes id_ci' in
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
    let extends = Hashtbl.find env_typage.extends id_ci in
    List.iter heritage_d'une_surci extends ;
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
      (fun (dp : param desc) ->
        let p = dp.desc in
        verifie_bf p.desc env_typage)
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
       de même type, et que le type de retour est un sous-type. 
       Cf les très nombreuses remarques à ce propos dans les fonctions dédiées. *)

    let (body : proto desc list) = Hashtbl.find i_body id_i in
    let loc_i = Hashtbl.find tab_pos_ci id_i in
    let methodes_heritees = herite_methodes id_i loc_i in 
    let ajoute_meth (d_proto : proto desc) =
      let pro = d_proto.desc in
      verifie_et_fait_methode pro.typ pro.nom pro.params 
        d_proto.loc env_typage methodes_heritees in
    List.iter ajoute_meth body ;
    let l_methodes = ref [] in
    Hashtbl.iter 
      (fun nom (meth,id_ci') -> l_methodes := meth :: !l_methodes) 
      methodes_heritees ;
    Hashtbl.add ci_methodes id_i (MethSet.of_list !l_methodes)
    (* Attention : les méthodes partent dans l'env global, via ci_methodes,
       et ici, pour les interfaces, c'est tout. *)
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
