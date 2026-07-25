let r0 = (ref (fun (x:?) -> x) : ?) in
let r1 = (r0 : (? -> int) ref) in
let a = (!r1) (7:?) in
let r2 = (r0 : (int -> int) ref) in
let b = (!r2) 8 in
print_int (a + b);;
