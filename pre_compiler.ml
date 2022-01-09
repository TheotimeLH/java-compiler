open Ast
open Ast_typing

(* On veut construire deux tables : 
  - offset_meth : (ident , int) Hashtbl.t
    Qui donne l'offset d'une méthode par rapport au descripteur
    des classes ayant une méthode de ce nom. En effet, deux méthodes
    ayant le même nom auront toujours le même offset. C'est un choix
    qui nous simplifie la vie, même si j'aimerai faire un peu mieux
    en ne m'étant au même offset que les méthodes de même nom et ayant
    un lien (via une classe ou une interface). (Ce serait sûrement bien
    plus simple dans ce cas de récupérer les infos de env_typage global,
    pour savoir exactement quels champs et méthodes possède une classe.)

  - offset_ch : (ident , ( int IdMap.t)) Hashtbl.t 
    Qui à un nom de classe associe une IdMap qui donne l'offset de 
    chacun de ses arguments (pour tout objet de cette classe créé
    sur le tas).

  Pour les faire je me base uniquement sur les relations d'héritages
  des classes (cf ma rem précédente, on pourrait améliorer en prenant
  les interfaces). *)

type node_meth_tmp = (* cf mk_offset_tbl *)
  { mutable vg : IdSet.t ; (* les méthodes voisines *)
    mutable nb_c : int ; (* le nb de classes ayant la méthode *) 
    mutable mini : int ; mutable maxi : int ;
  }

module IntSet = Set.Make(Int)

let mk_offset_tbl (lc : ty_classe list) node_obj =
  (* On réutilise le graphe de nodes que j'avais fabriquer pour construire un ordre
     topologique. Mais en fait c'est simplement un arbre enraciné en node_obj !
     Pour offset_ch il suffit de parcourir les classes, et on fait grandir l'offset
     au fur et à mesure. Pour offset_meth on crée un nouveau graphe ayant pour 
     sommets les noms de méthodes. Ensuite on a une arête entre deux méthodes "m"
     et "p" si il existe une classe ou "m" et "p" co-existe. Il faut ensuite
     colorier ce graphe, si possible en priorisant les méthodes qui apparaissent 
     le plus souvent et tout particulièrement on priorise les méthodes m pour 
     lesquelles la différence suivante est maximale : 
     max (|nb méthodes de A| avec A une classe ayant la méthode m) - min (idem)
     Pour ce faire on garde en mémoire le nombre de classes où m est présent,
     ainsi que les max et min. *)

  (* En plus de l'arbre des héritages, on a besoin des infos sur les classes,
     donc on transfert lc dans une table. *)
  let len_lc = List.lenght lc in
  let tab_c = Hashtbl.create len_lc in
  List.iter (fun (c : ty_classe) -> Hashtbl.add tab_c c.nom c) lc ;
  let graphe_tmp : (ident,node_meth_tmp) Hashtbl.t  = Hashtbl.create 15 in

  (* On numérote les méthodes pour avoir un graphe avec des sommets int *)
  let numero = ref (-1) in
  let num () = incr numero ; !numero in
  let tbl_num = Hashtbl.create 10 in 

  (* On fait offset_ch au passage *)
  let offset_ch : (ident , (int IdMap.t)) Hashtbl.t = Hashtbl.create len_lc in
  
  let rec parcours_arbre map_tmp_meth co_meth map_ch off_ch (node_c : node) =
    (* Cette fonction renvoie le nb de noeuds dans l'arbre. 
       Ainsi on récupère le nb de classes implémentant m *)
    let c = Hashtbl.find tab_c node_c.id in
    (* LES CHAMPS *)
    let (map_ch,off_ch) = List.fold_left 
      (fun (map_ch,off_ch) id_ch -> 
        (IdMap.add id_ch (off_ch + 8) map_ch , off_ch + 8) )
      (map_ch,off_ch) c.id_champs in
    Hashtbl.add offset_ch c.nom map_ch ;
    (* LES METHODES *)
    let new_meth = IdSet.of_list (List.map (fun (_,id_m) -> id_m) c.cle_methodes) in
    let co_meth = IdSet.union co_meth new_meth in
    let nb_meth = IdSet.cardinal co_meth in
    let vrai_new_meth = ref [] in
    let aux id_m map_tmp co_meth nb_meth (* = card(co_meth) *) =
      match IdMap.find_opt id_m map_tmp with
      | None -> 
          vrai_new_meth := id_m :: !vrai_new_meth ;
          IdMap.add id_m 
            {vg = co_meth ; nb_c = 1 ; mini = nb_meth ; maxi = nb_meth} 
            map_tmp
      | Some node_tmp ->
          node_tmp.vg <- co_meth ;
          map_tmp 
    in
    let new_map = 
      IdSet.fold (fun id_m map_tmp -> aux id_m map_tmp co_meth nb_meth)
      new_meth map_tmp_meth in

    let nb_noeuds = 
      if node_c.succ = [] then (
        (* On arrive en bout de course, on défini le maxi *)
        IdMap.iter (fun _ node_tmp -> node_tmp.maxi <- max node_tmp.maxi nb_meth) co_meth ;
        1 )
      else (
        List.fold_left 
          (fun nb node_fils -> nb + 
            (parcours_arbre new_map co_meth map_ch off_ch node_fils)) 
          1 node_c.succ)
    in

    (* On va passer les nouvelles méthodes dans le graphe *)
    List.iter 
      (fun id_m -> match Hashtbl.find_opt graphe_tmp id_m with
      | None ->
        let node_tmp = IdMap.find id_m new_map in
        node_tmp.nb_c <- nb_noeuds ;
        Hashtbl.add graphe_tmp id_m node_tmp ;
        Hashtbl.add tab_num id_m (num ()) 
      | Some node_tmp ->
        let node_tmp' = IdMap.find id_m new_map in
        node_tmp.vg <- IdSet.union node_tmp.vg node_tmp'.vg ;
        node_tmp.nb_c <- node_tmp.nb_c + nb_noeuds ;
        node_tmp.mini <- min node_tmp.mini node_tmp'.mini ;
        node_tmp.maxi <- max node_tmp.maxi node_tmp'.maxi
      )
      !vrai_new_meth ;
    nb_noeuds 
  in

  (* On a désormais le graphe_tmp : (ident , node_meth_tmp) Hashtbl.t *)
  (* On construit le graphe numéroté associé *)
  let nb_meth = !numero + 1 in
  let t_g = Array.make nb_meth [] in
  let t_id_m = Array.make nb_meth "" in
  let importance = Array.make nb_meth 0 in (* La priorité accorder à chaque sommet *)
  Hashtbl.iter 
   (fun id_m node_tmp ->
     let num_m = Hashtbl.find tab_num id_m in
     t_id_m.(num_m) <- id_m ;
     t_g.(num_m) <- IdSet.fold 
       (fun id_v vg_m -> (Hashtbl.find tab_num id_v) :: vg_m)
       node_tmp.vg [] ;
     importance.(num_m) <- node_tmp.nb_c * (node_tmp.maxi - node_tmp.mini) 
     (* Mon heristique *)
   ) graphe_tmp ;
  
  let l_num = List.sort 
    (fun i j -> - (compare importance.(i) importance.(j))) 
    (List.init nb_meth (fun i -> i)) in
  (* En ordre décroissant d'importance *)

  let couleur = Array.make nb_meth (-1) in
  let min_coul vg =
    let coul_prises = IntSet.of_list (List.map (fun i -> couleur.(i)) vg) in
    let k = ref 1 in
    while IntSet.mem !k coul_prises do incr k done ;
    !k
  in

  let offset_meth : (ident,int) Hashtbl.t = Hashtbl.create nb_meth 0 in

  let colorie x = 
    let c = min_coul t_g.(x) in
    couleur.(x) <- c ;
    Hashtbl.add offset_meth t_id_m.(x) c in
  List.iter colorie l_num ;

   offset_meth , offset_ch
