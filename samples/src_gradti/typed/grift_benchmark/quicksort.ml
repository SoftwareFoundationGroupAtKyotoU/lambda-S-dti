let swap (a : int array) (i : int) (j : int) =
  if i <> j then
    let t = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- t
  else ()
in
let partition (a : int array) (p : int) (r : int) =
  let i : int ref = ref (p - 1) in
  let x : int = a.(r) in
  for j = p to r - 1 do
    if a.(j) <= x then
      (i := !i + 1;
       swap a !i j)
    else ()
  done;
  swap a (!i + 1) r;
  !i + 1
in
let rec sort (a : int array) (p : int) (r : int) =
  if p < r then
    let q = partition a p r in
    sort a p (q - 1);
    sort a (q + 1) r
  else ()
in
let rec print_r x size i =
  if i = size then ()
  else (print_int (x.(i)); print_r x size (i + 1))
in
let size = read_int () in
let a = Array.make size 0 in
for i = 0 to size - 1 do
  a.(i) <- read_int ()
done;
print_r a size 0;
print_newline ();
sort a 0 (size - 1);
print_r a size 0;;
(* print_int (a.(size - 1));; *)
