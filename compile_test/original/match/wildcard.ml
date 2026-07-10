let always42 x = match x with _ -> 42 in
print_int (always42 0);
print_int (always42 true);;