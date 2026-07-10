let incr r = r := !r + 1 in
let x = ref 10 in
incr x; incr x;
print_int !x;;