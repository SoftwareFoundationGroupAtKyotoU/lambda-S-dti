let r0 = (ref ((1:?), (2:?)) : ?) in
let r1 = (r0 : (int * ?) ref) in
let a = match !r1 with (x, _) -> x in
let r2 = (r0 : (int * int) ref) in
let b = match !r2 with (_, y) -> y in
print_int (a + b);;
