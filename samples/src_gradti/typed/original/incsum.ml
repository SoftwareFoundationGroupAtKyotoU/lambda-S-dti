let rec countdown (n : int) : int list =
  if n <= 0 then [] else n :: countdown (n - 1)
in let rec inc_list (lst : int list) : int list =
  match lst with
  | [] -> []
  | x :: xs -> (x + 1) :: inc_list xs
in let rec sum_list (lst : int list) : int =
  match lst with
  | [] -> 0
  | x :: xs -> x + sum_list xs
in let n = read_int () in
let xs = countdown n in
let ys = inc_list xs in
print_int (sum_list ys);;
