let r0 = ref ((42: ?), (7: ?), (0: ?)) in
r0 := ((42: ?), (7: ?), (r0: ?));
(let r1 = (r0: (int * ? * (int * int * ?) ref) ref) in
match !r1 with a, _, _ -> print_int a);;