let a = Array.make 4 0 in
a.(0) <- 42;
a.(3) <- 99;
print_int (Array.length a);;
