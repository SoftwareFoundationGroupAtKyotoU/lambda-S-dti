let swap (a : int array) (i : int) (j : int) =
  if i = j then
    ()
  else let t = a.(i) in
    (**)
    a.(i) <- a.(j);
    a.(j) <- t;;

let partition (a : int array) (p : int) (r : int) =
  let i = ref (p - 1) in
  let x = a.(r) in
  (**)
  for j = p to r - 1 do
    if a.(j) <= x then
      (**)
      (i := !i + 1;
       swap a !i j)
    else ()
  done;
  swap a (!i + 1) r;
  !i + 1;;

let rec sort (a : int array) (p : int) (r : int) : unit =
  if p < r then
    let q = partition a p r in
    (**)
    sort a p (q - 1);
    sort a (q + 1) r
  else ();;

(* main *)
let size = read_int () in
let a = Array.make size 1 in
(**)
for i = 0 to size - 1 do
  a.(i) <- read_int ()
done;
sort a 0 (size - 1);
print_int (a.(size - 1));;
