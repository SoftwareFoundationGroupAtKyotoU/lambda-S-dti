let f x = x + 123 in
let g y = f in
print_int ((g 456) 789);;
