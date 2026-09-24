type fn_ii = int -> int;;
type nat0 = fn_ii -> int -> int;;
type nat1 = (fn_ii -> fn_ii) -> fn_ii -> fn_ii;;

let realnat (n : nat0) = n (fun (x : int) -> x + 1) 0 in
let exp (m : nat0) (n : nat1) (f : fn_ii) (x : int) = n m f x in
let two0 (f : fn_ii) (x : int) = f (f x) in
let two1 (f : fn_ii -> fn_ii) (x : fn_ii) = f (f x) in
let four = exp two0 two1 in
print_int (realnat four);;
