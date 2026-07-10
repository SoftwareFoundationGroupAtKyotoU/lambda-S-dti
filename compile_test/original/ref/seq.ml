let x = ref 0 in
x := 1;
x := !x + 1;
x := !x + 1;
print_int !x;;