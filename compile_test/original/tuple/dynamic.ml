let p = ((1, 2) : ?) in
match (p : int * int) with (a, b) -> print_int (a + b);;