let swap (x : 'a) (y : 'b) = (y, x) in
match swap 3 true with (a, _) -> print_bool a;;