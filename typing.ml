





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
    
    Doit-on faire i) pour toutes les C/I avant de passer au ii) ?

   On a l'env de typage globale, avec les C/I, et tout ce qu'on récupère dans i) ?
   et les env locaux pour vérifier ii) ? Mais on a juste à utiliser le global au
   moment de la vérification de C/I.
   *)
let type_fichier l =
  
