let rec mklist n i acc =
  if i = n then acc else mklist n (i + 1) (i :: acc) 
in let rec zipWith op xs ys acc =
  match xs with
  | [] -> acc
  | x :: xt ->
    match ys with
    | [] -> acc
    | y :: yt -> zipWith op xt yt ((op x y) :: acc) 
in let add a b = a + b in
let xs = mklist 500 0 [] in
let ys = mklist 500 0 [] in
zipWith add xs ys [];;
