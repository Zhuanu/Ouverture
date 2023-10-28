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

let rec bit65 n accu = if n <= 0 then accu@[true] else bit65 (n-1) (accu@[false]);;

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

let composition list =
  let rec loop l accu cpt = 
    match l with
    | [] -> accu
    | hd::tl -> 
      if hd 
        then loop tl (Int64.logor (Int64.shift_left accu 1) 1L) 0
        else loop tl (Int64.logor (Int64.shift_left accu 1) 0L) (cpt+1)
  in loop (List.rev list) 0L 0;;

let table x n = 
  let binary_list = decomposition [(Int64.of_int x)] in
  completion binary_list n;;
       
  let gen_alea n =
    let rec loop acc n  = 
      if (n <= 0) then List.rev acc
      else
      if (n < 64)
      then loop (Random.int64 (Int64.shift_left 1L n)::acc) (n-64) (* le dernier entier de n-l*64 bits *)
      else loop (Random.int64 Int64.max_int::acc) (n-64) (* l entier de 64 bits *)
    in
    loop [] n

(*let gen_alea n =
  
   let l = n / 64 in
   let bits = n - l * 64 in
  
   let rec loop l acc =
     if l <= 0 then List.rev acc
     else 
       loop (l - 1) (Random.int64 Int64.max_int::acc)
   in 
  
   if bits > 0 then
     (loop l [])@[Random.int64 (Int64.shift_left 1L bits)]
   else
     loop l []*)

