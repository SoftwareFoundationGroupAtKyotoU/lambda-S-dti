let rec mklist (n : int) (i : int) (acc : [int]) : [int] = 
  if i = n then acc else mklist n (i + 1) (i :: acc) 
in 
let rec map (f : int -> int) (lst : [int]) : [int] = match lst with 
  | [] -> [] 
  | x :: xs -> f x :: (map f xs) 
in 
let xs = mklist 10000 0 [] in 
let double (x : int) = x * 2 in 
map double xs;;