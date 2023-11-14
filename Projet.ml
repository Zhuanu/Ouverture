open Int64

(*1.1*)
module ListInt64 =
struct
  type 'a t  = 'a list ref
      
  let create() = ref []
  
  let insertHead x list = list:= [x] @ !list
                                       
  let insertTail x list = list:= !list @ [x]
  
  let removeHead list = 
    match !list with 
      [] -> failwith"Empty"
    | hd::tl -> list := tl; hd
        
  let length list = List.length !list  
end ;;


(*1.2*)
let rec bit64 n accu = if n <= 0 then accu else bit64 (n-1) (accu@[false]);;


let decomposition l = 
  let rec loop x list =
    if x = 0L then List.rev list 
    else if (Int64.unsigned_rem x 2L = 1L)
    then loop (Int64.unsigned_div x 2L) (true::list)
    else loop (Int64.unsigned_div x 2L) (false::list)
  in
  let rec loop2 l list = 
    match l with 
    | [] -> list
    | hd::tl -> 
      if hd = 0L 
        then loop2 tl (list @ (bit64 64 []))
        else loop2 tl (loop hd list)
  in
  loop2 l [];;
    

(*1.3*)
let rec ajoutFalse list n accu =
  if (n <= 0)
  then list @ accu
  else (ajoutFalse list (n-1) (false::accu));;

       
let rec suppElem list n accu =
  if (n <= 0) then (List.rev accu, list)
  else match list with
    | [] -> failwith "Empty"
    | hd::tl -> suppElem tl (n-1) (hd::accu);;
        
  
let completion list n =
  let len = List.length list in
  if (len <= n) then (ajoutFalse list (n-len) [], [])
  else suppElem list n [];;


let package list = 
  let rec loop l =
    let (hd, tl) = completion l 64 in
    match tl with
    | [] -> [(List.rev hd)]
    | _ -> (List.rev hd)::(loop tl)
  in loop list;;


let composition list =
  let rec loopExt l =
    match l with
    | [] -> []
    | hd::tl -> 
      let rec loopInt l accu =
        match l with
        | [] -> Int64.of_int (Int64.to_int accu)
        | hd::tl -> 
          loopInt tl (Int64.logor (Int64.shift_left accu 1) (if hd then 1L else 0L))
      in loopInt hd 0L :: loopExt tl
  in loopExt (package list);;


(*1.5*)
let table x n = 
  let binary_list = decomposition x in
  completion binary_list n;;


(*1.6*)
let gen_alea n =
  let rec loop acc n  = 
    if (n <= 0) then List.rev acc
    else
    if (n < 64)
    then 
      let rand_arg = if n = 63 then Int64.max_int else Int64.shift_left 1L n in
      loop (Random.int64 rand_arg::acc) (n-64) (* le dernier entier de n-l*64 bits *)
    else loop (Random.int64 Int64.max_int::acc) (n-64) (* l entier de 64 bits *)
  in
  loop [] n
  


(*2.7*)
type btree = 
  | Leaf of bool
  | Node of int * btree * btree


(*2.8*)
let diviser_liste liste =
  let rec aux taille l1 l2 = 
    match l2 with
    | [] -> List.rev l1, []
    | x::y as l -> 
        if taille = 0 
        then List.rev l1, l
        else aux (taille-1) (x::l1) y  
  in
  aux (List.length liste/2) [] liste


let cons_arbre table = 
  let rec construction depth table = 
    match table with
    | [] -> failwith "Table de vérité vide"
    | [b] -> Leaf b
    | tab -> 
        let left_table, right_table = diviser_liste tab in
        Node (depth, construction (depth+1) left_table, construction (depth+1) right_table)
  in
  construction 1 table


(*2.9*)
let rec liste_feuilles n = 
  match n with
  | Leaf b -> [b]
  | Node (_, gauche, droite) -> liste_feuilles gauche @ liste_feuilles droite


(*3.10*)
type dejaVus = int64 list * btree ref;;
type listeDejaVus = dejaVus list;;


let findSeen seen x =
  let rec aux seen x =
    match !seen with
    | [] -> None
    | (nombre, pointeur)::reste -> 
      let egaux = List.compare (fun a b -> Int64.unsigned_compare a b) nombre x in
        if egaux = 0
          then Some pointeur
          else aux (ref reste) x
  in aux seen x


let onlyFalse list =
  let rec loop list =
    match list with
    | [] -> true
    | hd::tl -> if hd then false else loop tl
  in loop list


let regleM tree seen liste =
  let n = composition liste in
  let node = findSeen seen n in
  match node with
    | None -> seen := (n, ref tree)::!seen; tree
    | Some node -> !node


let compressionParListe tree listseen =
  let rec loop tree listseen =
    match tree with
    | Leaf b -> regleM tree listseen [b]
    | Node (depth, left, right) ->
      let liste = liste_feuilles tree in
      let liste_droite = liste_feuilles right in
      if (onlyFalse (liste_droite))
      then ( (* Règle Z *)
        loop left listseen;
      )
      else (
        let newTree = Node (depth, loop left listseen, loop right listseen) in
        regleM newTree listseen liste
      );
  in loop tree listseen;;


let nodeGraph arbre buffer =
  let id_map = Hashtbl.create 256 in
  let cpt = ref 0 in
  let rec loop node cpt buffer =
    match node with
    | Leaf b ->
      begin
        try
          let _ = Hashtbl.find id_map node in ()
        with Not_found -> 
          Hashtbl.add id_map node !cpt;
          buffer := !buffer ^ (Printf.sprintf "%d [label=\"%s\"];\n" !cpt (if b then "True" else "False"))
      end
    | Node (prof, gauche, droite) ->
      begin
        try
          let _ = Hashtbl.find id_map node in ()
        with Not_found ->
          Hashtbl.add id_map node !cpt;
          buffer := !buffer ^ (Printf.sprintf "%d [label=\"%d\"];\n" !cpt prof);
      end;
      begin
        try
          let _ = Hashtbl.find id_map gauche in ()
        with Not_found ->
          cpt := !cpt + 1;
          loop gauche cpt buffer;
      end;
      begin
        try
          let _ = Hashtbl.find id_map droite in ()
        with Not_found ->
          cpt := !cpt + 1;
          loop droite cpt buffer;
      end;
  in loop arbre cpt buffer;;


let edgeGraph arbre buffer =
  let id_map = Hashtbl.create 256 in
  let cpt = ref 0 in
  let rec loop node cpt buffer =
    match node with
    | Leaf b -> ()
    | Node (prof, gauche, droite) ->
      let id = !cpt in
      begin
        try
          let id_gauche = Hashtbl.find id_map gauche in 
          buffer := !buffer ^ (Printf.sprintf "%d -> %d [style=\"dotted\"];\n" id id_gauche);
        with Not_found ->
          cpt := !cpt + 1;
          Hashtbl.add id_map gauche !cpt;
          buffer := !buffer ^ (Printf.sprintf "%d -> %d [style=\"dotted\"];\n" id !cpt);
          loop gauche cpt buffer;
      end;
      begin
        try
          let id_droite = Hashtbl.find id_map droite in
          buffer := !buffer ^ (Printf.sprintf "%d -> %d;\n" id id_droite);
        with Not_found ->
          cpt := !cpt + 1;
          Hashtbl.add id_map droite !cpt;
          buffer := !buffer ^ (Printf.sprintf "%d -> %d;\n" id !cpt);
          loop droite cpt buffer;
      end;
  in loop arbre cpt buffer;;


let graph l n =
  let (table, _) = (table l n) in
  let arbre = cons_arbre table in

  (* Arbre non compressé *)
  let buffer2 = ref "digraph ArbreDecision {\n" in
  nodeGraph arbre buffer2;
  edgeGraph arbre buffer2;
  buffer2 := !buffer2 ^ "}";
  let dot_file = open_out "Figure 1.dot" in
  Printf.fprintf dot_file "%s" !buffer2;
  close_out dot_file;

  (* Arbre compressé *)
  let buffer = ref "digraph ArbreDecision {\n" in
  let seen = ref [] in
  let arbre_comp = compressionParListe arbre seen in 
  nodeGraph arbre_comp buffer;
  edgeGraph arbre_comp buffer;
  buffer := !buffer ^ "}";
  let dot_file = open_out "Figure 2.dot" in
  Printf.fprintf dot_file "%s" !buffer;
  close_out dot_file;;

let () = graph [25899L] 16;;



(*4.15*)
type arbreDejaVus =
| Leaf_
| Node_ of btree option * (arbreDejaVus ref) * (arbreDejaVus ref) (* pointeur vers noeud du graphe, false : arbreG, true : arbreD *)


let insertionArbre arbre bits node =
  let rec loop arbre bits =
    match !arbre, bits with
    | Leaf_, [] -> ref (Node_ (Some node, ref Leaf_, ref Leaf_))
    | Leaf_, true::xs -> ref (Node_ (None, ref Leaf_, loop (ref Leaf_) xs))
    | Leaf_, false::xs -> ref (Node_ (None, loop (ref Leaf_) xs, ref Leaf_))
    | Node_ (_, gauche, droite), [] -> ref (Node_ (Some node, gauche, droite)) (* forcement None sinon on ferait pas d'insertion *)
    | Node_ (pointeur, gauche, droite), true::xs -> ref (Node_ (pointeur, gauche, loop droite xs))
    | Node_ (pointeur, gauche, droite), false::xs -> ref (Node_ (pointeur, loop gauche xs, droite))
  in loop arbre bits


let findSeenArbre seenArbre bits =
  let rec loop seenArbre bits =
    match !seenArbre, bits with
    | Leaf_, _ -> None
    | Node_ (pointeur, _, _), [] -> Some pointeur
    | Node_ (_, gauche, droite), true::xs -> loop droite xs
    | Node_ (_, gauche, droite), false::xs -> loop gauche xs
  in loop seenArbre bits


let regleM_Arbre tree seenArbre liste =
  let node = findSeenArbre seenArbre liste in
  match node with
    | None -> seenArbre := !(insertionArbre seenArbre liste tree); tree
    | Some pointeur ->
      match pointeur with
      | None -> failwith "Erreur"
      | Some node -> node


let compressionParArbre tree seenArbre =
  let rec loop tree seenArbre =
    match tree with
    | Leaf b -> regleM_Arbre tree seenArbre [b]
    | Node (depth, left, right) ->
      let liste = liste_feuilles tree in
      let liste_droite = liste_feuilles right in
      if (onlyFalse (liste_droite))
      then ( (* Règle Z *)
        loop left seenArbre;
      )
      else (
        let newTree = Node (depth, loop left seenArbre, loop right seenArbre) in
        regleM_Arbre newTree seenArbre liste
      );
  in loop tree seenArbre;;


let graphArbre l n =
    let (table, _) = (table l n) in
    let arbre = cons_arbre table in

    (* Arbre compressé *)
    let buffer = ref "digraph ArbreDecision {\n" in
    let seen = ref Leaf_ in
    let arbre_comp = compressionParArbre arbre seen in 
    nodeGraph arbre_comp buffer;
    edgeGraph arbre_comp buffer;
    buffer := !buffer ^ "}";
    let dot_file = open_out "Figure 2 Arbre.dot" in
    Printf.fprintf dot_file "%s" !buffer;
    close_out dot_file;;
  
let () = graphArbre [25899L] 16;;

let nodeCount arbre =
  let count = ref 0 in
  let rec loop arbre =
    match arbre with
    | Leaf_ -> ()
    | Node_ (pointeur, gauche, droite) -> 
      (match pointeur with
      | None -> ()
      | Some _ -> count := !count + 1);
      loop !gauche; loop !droite
  in loop arbre;
  !count;;

let treeHeight arbre =
  let h = ref 0 in
  let rec loop arbre =
    match arbre with
    | Leaf b -> ()
    | Node (_, gauche, droite) -> 
      h := !h + 1;
      loop gauche;
  in loop arbre; 
  !h;;


let experimentalCurvesTree n nbBits =
  let (table, _) = (table n nbBits) in
  let seenArbre = ref Leaf_ in
  let arbre = cons_arbre table in
  let t = Sys.time () in
  let arbre_comp = compressionParArbre arbre seenArbre in
  (* 2^(h+1) - 1 est le nombre de noeud avant compression *)
  let h = treeHeight arbre in
  let nb_nodes = (int_of_float (2.0 ** ((float_of_int h) +. 1.))) - 1 in
  let nb_nodes_comp = nodeCount !seenArbre in
  let rapport = (float_of_int nb_nodes_comp) /. (float_of_int nb_nodes) in
  ((1. -. rapport) *. 100., Sys.time() -. t);;


let experimentalCurvesList n nbBits =
  let (table, _) = (table n nbBits) in
  let listseen = ref [] in
  let arbre = cons_arbre table in
  let t = Sys.time () in
  let arbre_comp = compressionParListe arbre listseen in
  (* 2^(h+1) - 1 est le nombre de noeud avant compression *)
  let h = treeHeight arbre in
  let nb_nodes = (int_of_float (2.0 ** ((float_of_int h) +. 1.))) - 1 in
  let nb_nodes_comp = List.length !listseen in
  let rapport = (float_of_int nb_nodes_comp) /. (float_of_int nb_nodes) in
  ((1. -. rapport) *. 100., Sys.time() -. t);;


let () = 
  let buffer = ref "" in
  let buffer2 = ref "" in
  let nbFeuilles = ref 1 in
  let nbIterations = 1040 in
  let rec loop nbBits =
    if nbBits = nbIterations then ()
    else
      let int64n = (gen_alea nbBits) in
      (* let n = Int64.to_int (List.hd int64n) in *)
      if nbBits > !nbFeuilles then nbFeuilles := !nbFeuilles * 2;
      let (taux, temps) = (experimentalCurvesTree int64n !nbFeuilles) in
      let (taux2, temps2) = (experimentalCurvesList int64n !nbFeuilles) in
      buffer := !buffer ^ (Printf.sprintf "%d %f %f\n" nbBits taux temps);
      buffer2 := !buffer ^ (Printf.sprintf "%d %f %f\n" nbBits taux2 temps2);
      loop (nbBits+1)
  in loop 1;
  let csv_file = open_out "compressionArbre.txt" in
  Printf.fprintf csv_file "%s" !buffer;
  close_out csv_file;
  let csv_file2 = open_out "compressionListe.txt" in
  Printf.fprintf csv_file2 "%s" !buffer2;
  close_out csv_file2;; 


let nb_Feuilles n = 
  let rec loop n accu =
    if accu > n then accu
    else loop n (accu * 2)
  in loop n 1;;


type listeOcc = (int * int ref) list ref;;


let rechercheListe list x =
  let rec aux reste x =
    match !reste with
    | [] -> list := (x, ref 1)::!list
    | (tailleZDD, occ)::reste -> 
      if (tailleZDD = x) then occ := !occ + 1
      else aux (ref reste) x
  in aux list x;;


let distributionOcc n nbIterations occTaille =
  let rec loop nbIterations =
    if nbIterations = 0 then ()
    else 
      let bits = gen_alea n in
      let nbFeuilles = nb_Feuilles n in
      let (table, _) = (table bits nbFeuilles) in
      let arbre = cons_arbre table in
      let seenArbre = ref Leaf_ in
      let arbre_comp = compressionParArbre arbre seenArbre in
      let tailleZDD = nodeCount !seenArbre in
      rechercheListe occTaille tailleZDD;
      loop (nbIterations-1);
  in loop nbIterations;;


let distributionProba occTaille nbIterations probaTaille =
  let rec loop occTaille =
    match !occTaille with
    | [] -> ()
    | (tailleZDD, occ)::reste -> 
      probaTaille := (tailleZDD, (float_of_int !occ) /. (float_of_int nbIterations))::!probaTaille;
      loop (ref reste)
  in loop occTaille;;

  
let () = 
  let buffer = ref "" in
  let nbIterations = 3000 in
  let n = 600 in
  let occTaille = ref [] in
  let probaTaille = ref [] in
  distributionOcc n nbIterations occTaille;
  distributionProba occTaille nbIterations probaTaille;
  let rec loop probaTaille =
    match !probaTaille with
    | [] -> ()
    | (tailleZDD, proba)::reste -> 
      buffer := !buffer ^ (Printf.sprintf "%d %f\n" tailleZDD proba);
      loop (ref reste)
  in loop probaTaille;
  let csv_file = open_out "distributionProba.txt" in
  Printf.fprintf csv_file "%s" !buffer;
  close_out csv_file;; 
