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

  - offset_ch : (ident , ( (ident,int) Hashtbl.t)) Hashtbl.t 
    Qui à un nom de classe associe une table qui donne l'offset de 
    chacun de ses arguments (pour tout objet de cette classe créée
    sur le tas).

  Pour les faire je me base uniquement sur les relations d'héritages
  des classes (cf ma rem précédente, on pourrait améliorer en prenant
  les interfaces). *)

let mk_offset_tbl (lc : ty_classe list) node_obj =
  (* On réutilise la node que j'avais utilisé pour construire un ordre
     topologique. Mais en fait c'est simplement un arbre enraciné en node_obj !
     Pour offset_ch il suffit de parcourir les classes, et on fait grandir l'offset
     au fur et à mesure. Pour offset_meth on crée un nouveau graphe ayant pour 
     sommets les noms de méthodes. Ensuite on a une arête entre deux méthodes "m"
     et "p" si il existe une classe ou "m" et "p" co-existe. Il faut ensuite
     colorier ce graphe, si possible en priorisant les méthodes qui apparaissent 
     le plus souvent et tout particulièrement on priorise les méthodes m pour 
     lequelles la différence suivante est maximale : 
     max (|nb méthodes de A| avec A une classe ayant la méthode m) - min (idem)
     Pour ce faire on garde en mémoire le nombre de classes où m est présent,
     ainsi que les max et min. *) 
  


