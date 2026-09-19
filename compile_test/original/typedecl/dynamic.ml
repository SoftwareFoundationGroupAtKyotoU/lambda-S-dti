type pair = int * bool;;
let p : pair = (1, true) in
let q : ? = p in
match (q : pair) with (a, b) -> if b then print_int a else print_int 0;;
