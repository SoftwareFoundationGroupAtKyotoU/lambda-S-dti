let r0 = ref (42:?) in
let r1 = (r0 : int ref) in
let r2 = (r0 : bool ref) in
print_int !r1;;
