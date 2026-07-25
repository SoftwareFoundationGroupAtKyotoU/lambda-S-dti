let r = ref 42 in
let f = fun (h : int ref) -> !h in
print_int (f r);;
