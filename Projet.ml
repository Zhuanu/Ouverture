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

let rec bit65 n accu = if n <= 0 then accu@[true] else bit65 (n-1) (accu@[false]);;

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
        then loop2 tl (list @ (bit65 64 []))
        else loop2 tl (loop hd list)
  in
  loop2 l [];;
    
(*1.3*)
let rec ajoutFalse list n accu =
  if (n <= 0)
  then list @ accu
  else (ajoutFalse list (n-1) (false::accu));;

       
let rec suppElem list n accu =
  if (n <= 0) then (List.rev accu)
  else match list with
    | [] -> failwith "Empty"
    | hd::tl -> suppElem tl (n-1) (hd::accu);;
        
  
let completion list n =
  let len = List.length list in
  if (len <= n) then ajoutFalse list (n-len) []
  else suppElem list n []


(* let composition list = 
  let rec loop l accu cpt =
    match l with
    | [] -> accu
    | hd::tl -> 
      if cpt = 0 
        then loop tl (Int64.logor (Int64.shift_left accu 1) 1L) 0
        else loop tl (Int64.logor (Int64.shift_left accu 1) 0L) (cpt-1)
      if hd 
        then loop tl (Int64.logor (Int64.shift_left accu 1) 1L) 0
        else loop tl (Int64.logor (Int64.shift_left accu 1) 0L) (cpt+1)
  in loop (List.rev list) 0L;; *)
  
(*1.4*)
let composition list =
  let rec loop l accu cpt = 
    match l with
    | [] -> accu
    | hd::tl -> 
      if hd 
        then loop tl (Int64.logor (Int64.shift_left accu 1) 1L) 0
        else loop tl (Int64.logor (Int64.shift_left accu 1) 0L) (cpt+1)
  in loop (List.rev list) 0L 0;;

(*1.5*)
let table x n = 
  let binary_list = decomposition [(Int64.of_int x)] in
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