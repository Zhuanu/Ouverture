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

let rec bit64 n accu = if n <= 0 then accu else bit64 (n-1) (accu@[false]);;

(*1.2*)
let decomposition l = 
  let rec loop x list =
    if x = 0L then list 
    else if (Int64.unsigned_rem x 2L = 1L)
    then loop (Int64.unsigned_div x 2L) (list@[true])
    else loop (Int64.unsigned_div x 2L) (list@[false])
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
    then loop (Random.int64 (Int64.shift_left 1L n)::acc) (n-64) (* le dernier entier de n-l*64 bits *)
    else loop (Random.int64 Int64.max_int::acc) (n-64) (* l entier de 64 bits *)
  in
  loop [] n

(*2.7*)
type btree = 
  | Leaf of bool
  | Node of int * btree * btree

(*2.8*)
let diviser_liste taille_l1 liste =
  let rec aux taille_l1 res liste = 
    match liste with
    | [] -> List.rev res, []
    | x::y as l -> 
        if taille_l1 = 0 
        then List.rev res, l
        else aux (taille_l1-1) (x::res) y  
  in
  aux taille_l1 [] liste

let cons_arbre table = 
  let rec construction depth table = 
    match table with
    | [] -> failwith "Table de vérité vide"
    | [b] -> Leaf b
    | tab -> 
        let table_gauche, table_droite = diviser_liste (List.length tab/2) tab in
        Node (depth, construction (depth+1) table_gauche, construction (depth+1) table_droite)
  in
  construction 1 table

(*2.9*)
let rec liste_feuilles arbre = 
  match arbre with
  | Leaf b -> [b]
  | Node (_, gauche, droite) -> liste_feuilles gauche @ liste_feuilles droite


(*3.10*)

type dejaVus = int64 list * btree ref;;
type listeDejaVus = dejaVus list;;

let findSeen liste x =
  let rec aux liste x =
    match liste with
    | [] -> None
    | (nombre, pointeur)::q -> 
      let egaux = List.compare (fun a b -> Int64.unsigned_compare a b) nombre x in
        if egaux = 0
          then Some pointeur
          else aux q x
  in
  aux liste x

  let onlyFalse list =
    let rec loop list =
      match list with
      | [] -> true
      | hd::tl -> if hd then false else loop tl
    in loop list



  let compressionParListe tree seen =
    let rec loop tree seen =
      match tree with
      | Leaf b -> 
        let n = composition [b] in
        let node = findSeen seen n in
        (match node with
        | None -> (n, ref tree)::seen
        | Some node -> !node)
      | Node (depth, gauche, droite) -> 
          loop gauche seen;
          loop droite seen;
          let liste_gauche = liste_feuilles gauche in
          let liste_droite = liste_feuilles droite in
          let liste = liste_gauche @ liste_droite in
          if (onlyFalse liste_droite)
          then gauche
          else 
            let n = composition liste in
            let node = findSeen seen n in
            match node with
            | None -> (n, ref tree)::seen
            | Some node -> !node
    in loop tree seen ;;




