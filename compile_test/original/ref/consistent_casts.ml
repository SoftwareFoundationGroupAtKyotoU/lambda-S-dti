let r0 = (ref (5:?) : ?) in
let r1 = (r0 : int ref) in
let r2 = (r0 : int ref) in
r1 := !r1 + 1;
print_int !r2;;
