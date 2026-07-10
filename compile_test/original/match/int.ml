let classify x = match x with
  | 0 -> 10
  | 1 -> 20
  | _ -> 99
in
print_int (classify 0);
print_int (classify 1);
print_int (classify 5);;