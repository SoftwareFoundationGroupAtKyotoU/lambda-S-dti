let make_counter x =
  let n = ref 0 in
  (fun x -> n := !n + 1; !n)
in
let c = make_counter () in
print_int (c ());
print_int (c ());
print_int (c ());;