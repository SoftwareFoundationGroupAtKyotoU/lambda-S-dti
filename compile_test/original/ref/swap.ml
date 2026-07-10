let x = ref 2 in
let y = ref 3 in
let tmp = !x in
x := !y;
y := tmp;
print_int !x;
print_int !y;;