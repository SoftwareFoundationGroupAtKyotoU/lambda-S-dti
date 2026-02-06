let rec mklist n i acc =
  if i = n then acc else mklist n (i + 1) (i :: acc)
in let rec map f lst =
  match lst with
  | [] -> []
  | x :: xs -> f x :: (map f xs) in
let xs = mklist 10000 0 [] in
let double x = x * 2 in
map double xs;;
