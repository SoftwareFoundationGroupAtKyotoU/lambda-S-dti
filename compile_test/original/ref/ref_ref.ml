let inner = ref 1 in
let outer = ref inner in
(!outer) := !(!outer) + 41;
print_int !(!outer);;
