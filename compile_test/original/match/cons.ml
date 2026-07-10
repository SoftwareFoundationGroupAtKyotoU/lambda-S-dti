let second lst = match lst with
  | _ :: x :: _ -> x
  | _ -> 0
in
print_int (second [10; 20; 30]);;