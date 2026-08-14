let rec sum lst = match lst with
  | [] -> 0.0
  | x :: xs -> x +. sum xs
in
print_float (sum [1.0; 2.0; 3.0]);;
