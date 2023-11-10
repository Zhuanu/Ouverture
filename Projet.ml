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
    then loop (Random.int64 (Int64.shift_left 1L n)::acc) (n-64) (* le dernier entier de n-l*64 bits *)
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
let rec liste_feuilles N = 
  match N with
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

(* let regleM tree seen liste =
  let n = composition liste in
  let node = findSeen seen n in
  (match node with
    | None -> seen := (n, tree)::!seen
    | Some node -> tree := !node);; *)
    let regleM tree seen liste =
      let n = composition liste in
      let node = findSeen seen n in
      (match node with
        | None -> print_string "None\n" ; seen := (n, tree)::!seen
        | Some node -> print_string "Some\n");;

(* version Unit *)
let compressionParListe tree listseen = 
  let rec loop tree listseen =
    match !tree with
    | Leaf b -> regleM tree listseen [b]
    | Node (depth, left, right) ->
      let gauche = (ref left) in
      let droite = (ref right) in
      let liste = liste_feuilles (!tree) in
      let liste_droite = liste_feuilles right in
      if (onlyFalse (liste_droite)) (* Règle Z *)
      then (
        loop gauche listseen;
        tree := !gauche;
      )
      else (
        loop gauche listseen;
        loop droite listseen;
        regleM tree listseen liste;
      );
      Printf.printf "Taille de seen %d\n" (List.length !listseen);
  in loop tree listseen;;

let nodeGraph arbre buffer = 
  let cpt = ref 0 in
  let rec loop node cpt buffer = 
    match !node with
    | Leaf b -> 
      buffer := !buffer ^ (Printf.sprintf "%d [label=\"%s\"];\n" !cpt (if b then "True" else "False"))
    | Node (prof, gauche, droite) -> 
      buffer := !buffer ^ (Printf.sprintf "%d [label=\"%d\"];\n" !cpt prof);
      cpt := !cpt + 1;
      loop (ref gauche) cpt buffer;
      cpt := !cpt + 1;
      loop (ref droite) cpt buffer;
  in loop arbre cpt buffer;;


let edgeGraph arbre buffer =
  let cpt = ref 0 in
  let rec loop node cpt buffer =
    let id = !cpt in
    match !node with
    | Leaf b -> ()
    | Node (prof, gauche, droite) -> 
      cpt := !cpt + 1;
      buffer := !buffer ^ (Printf.sprintf "%d -> %d [style=\"dotted\"];\n" id !cpt);
      loop (ref gauche) cpt buffer;
      cpt := !cpt + 1;
      buffer := !buffer ^ (Printf.sprintf "%d -> %d;\n" id !cpt);
      loop (ref droite) cpt buffer;
  in loop arbre cpt buffer;;


let graph l n =
  let buffer = ref "digraph ArbreDecision {\n" in
  let (table, _) = (table l n) in
  let arbre = ref (cons_arbre table) in
  let seen = ref [] in
  compressionParListe arbre seen;
  nodeGraph arbre buffer;
  edgeGraph arbre buffer;
  buffer := !buffer ^ "}";
  (* print_string !buffer;; *)
  let dot_file = open_out "arbre_decision.dot" in
  Printf.fprintf dot_file "%s" !buffer;
  close_out dot_file;;

let () = graph [8L] 4;;
