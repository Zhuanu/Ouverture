open Int64
    
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


(* let composition list = 
  let rec loop l accuElem cpt accuList =
    match l with
    | [] -> accuElem::accuList
    | hd::tl -> 
      if hd then 
        if cpt = 64
          then loop tl 0L 0 [0L]@accuList
          else loop tl (Int64.logor (Int64.shift_left accuElem 1) 1L) 0 accuList
      else loop tl (Int64.logor (Int64.shift_left accuElem 1) 0L) (cpt+1) accuList
  in loop list 0L 0 [];; *)

  let package list = 
    let rec loop l =
      let (hd, tl) = completion l 64 in
      match tl with
      | [] -> [hd]
      | _ -> hd::(loop tl)
    in loop list;;

  let composition list =
    let rec loopExt l =
      match l with
      | [] -> []
      | hd::tl -> 
        let rec loopInt l accu =
          match l with
          | [] -> accu
          | hd::tl -> 
            loopInt tl (Int64.logor (Int64.shift_left accu 1) (if hd then 1L else 0L))
        in loopInt (List.rev hd) 0L :: loopExt tl
    in loopExt (package list);;

    let print_list lst =
      List.iter (fun x -> Printf.printf "%b\n" x) lst
    ;;


let table x n = 
  let binary_list = decomposition [(Int64.of_int x)] in
  completion binary_list n;;

       