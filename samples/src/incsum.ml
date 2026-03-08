let rec countdown n =
  if n <= 0 then [] else n :: countdown (n - 1)
in let rec inc_list lst =
  match lst with
  | [] -> []
  | x :: xs -> (x + 1) :: inc_list xs
in let rec sum_list lst =
  match lst with
  | [] -> 0
  | x :: xs -> x + sum_list xs
in let n = read_int () in
let xs = countdown n in
let ys = inc_list xs in
print_int (sum_list ys);;