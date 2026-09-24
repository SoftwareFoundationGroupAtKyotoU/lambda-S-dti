type fn_ii = int -> int;;
type nat0 = fn_ii -> int -> int;;
type fn_ii2 = fn_ii -> fn_ii;;
type nat1 = fn_ii2 -> fn_ii -> fn_ii;;
type fn_ii3 = fn_ii2 -> fn_ii2;;
type nat2 = fn_ii3 -> fn_ii2 -> fn_ii2;;

let realnat (n : nat0) = n (fun (x : int) -> x + 1) 0 in

let exp0 (m : nat0) (n : nat1) (f : fn_ii) (x : int) = n m f x in
let two0 (f : fn_ii) (x : int) = f (f x) in
let two1 (f : fn_ii2) (x : fn_ii) = f (f x) in
let four0 (x : fn_ii) = exp0 two0 two1 x in

let exp1 (m : nat1) (n : nat2) (f : fn_ii2) (x : fn_ii) = n m f x in
let two2 (f : fn_ii3) (x : fn_ii2) = f (f x) in
let four1 (x : fn_ii2) = exp1 two1 two2 x in

let twoHundredFiftySix (y : fn_ii) = exp0 four0 four1 y in
let sixtyFiveThousandAndFiveHundredsThirtySix (z : fn_ii) = exp0 twoHundredFiftySix two1 z in
print_int (realnat sixtyFiveThousandAndFiveHundredsThirtySix);;
