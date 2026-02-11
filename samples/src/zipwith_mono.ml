let rec mklist (n : int) (i : int) (acc : [int]) : [int] =
  if i = n then acc else mklist n (i + 1) (i :: acc) in

let rec zipWith (op : int -> int -> int) (xs : [int]) (ys : [int]) (acc : [int]) : [int] =
  match xs with
    [] -> acc
  | x :: xt ->
    match ys with
      [] -> acc
    | y :: yt -> zipWith op xt yt ((op x y) :: acc) in

let add (a : int) (b : int) : int = a + b in
let i = read_int () in
let xs = mklist i 0 [] in
let ys = mklist i 0 [] in
zipWith add xs ys [];;