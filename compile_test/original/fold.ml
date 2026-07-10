let rec fold_left f acc lst =
  match lst with
  | [] -> acc
  | h :: t -> fold_left f (f acc h) t
in
print_int (fold_left (fun acc x -> acc + x) 0 [1; 2; 3; 4; 5]);;