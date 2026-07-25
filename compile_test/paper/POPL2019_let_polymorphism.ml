let g x = ((fun y -> y):? -> ?) x in
match (g 2, g true) with a, b -> print_int a; print_bool b;;