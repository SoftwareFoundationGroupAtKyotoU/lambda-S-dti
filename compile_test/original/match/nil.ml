let is_empty lst = match lst with
  | [] -> 1
  | _ :: _ -> 0
in
print_int (is_empty []);
print_int (is_empty [1; 2]);;