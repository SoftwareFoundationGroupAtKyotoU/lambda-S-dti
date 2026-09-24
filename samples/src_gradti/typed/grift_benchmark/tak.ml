let rec tak (x : int) (y : int) (z : int) : int =
  if y >= x then z
  else tak (tak (x - 1) y z)
           (tak (y - 1) z x)
           (tak (z - 1) x y);;

(* main *)
let x = read_int () in
let y = read_int () in
let z = read_int () in
print_int (tak x y z);;
