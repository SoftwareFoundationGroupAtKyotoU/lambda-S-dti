let counter = ref 0 in
let inc x = counter := !counter + 1 in
inc (); inc (); inc ();
print_int !counter;;