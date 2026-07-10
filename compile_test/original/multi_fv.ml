let make_adder2 a b = fun x -> x + a + b in
let add9 = make_adder2 4 5 in
print_int (add9 1);
print_int (add9 10);;