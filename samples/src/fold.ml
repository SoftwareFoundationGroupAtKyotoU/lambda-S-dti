let rec mklist n i acc =
  if i = n
    then acc
    else mklist n (i + 1) (i :: acc) in
let rec foldl f acc xs =
  match xs with
  | [] -> acc
  | x :: xt -> foldl f (f acc x) xt in
let add a b = a + b in
let xs = mklist 10000 0 [] in
foldl add 0 xs;;
