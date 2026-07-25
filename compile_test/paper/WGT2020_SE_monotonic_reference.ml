let f : ? = fun (x:?) -> x in
let r : ? = ref (f, (():?)) in
r := (f, r);
(let g (x : ((? -> int) * ((int -> ?) * ?) ref) ref) = match !x with (y, z) -> (y:?) 42 in
print_int (g r));;