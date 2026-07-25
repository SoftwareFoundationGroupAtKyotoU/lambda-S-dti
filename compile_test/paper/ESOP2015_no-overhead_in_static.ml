let r1 = ref (fun (x:?) -> (x:int)) in
let r2 = (r1 : (int -> int) ref) in
print_int ((!r2) 42);;
