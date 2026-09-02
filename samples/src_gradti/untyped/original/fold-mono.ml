let rec mklist (n : int) (i : int) (acc : int list) : int list =
  if i = n
    then acc
    else mklist n (i + 1) (i :: acc) in
let rec foldl (f : int -> int -> int) (acc : int) (xs : int list) : int =
  match xs with
    []     -> acc
  | x :: xt -> foldl f (f acc x) xt in
let add (a : int) (b : int) : int = a + b in
let xs = mklist (read_int ()) 0 [] in
foldl add 0 xs;;