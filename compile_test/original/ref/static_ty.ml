let r = (ref 5 : int ref) in
r := !r + 1;
print_int !r;;