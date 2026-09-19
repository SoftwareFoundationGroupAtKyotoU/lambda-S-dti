let f (x: ?) = x in
let b : bool = f true in
let u : unit = f () in
let c1 : char = f (char_of_int 0) in
let c2 : char = f (char_of_int 255) in
print_bool b; print_string " "; print_int (int_of_char c1); print_string " "; print_int (int_of_char c2); u;;
