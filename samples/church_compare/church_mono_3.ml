let realnat (n : (int -> int) -> int -> int) = n (fun (x : ?) -> x + 1) 0 in
let exp1 (m : (int -> int) -> int -> int) (n : ?) (f : int -> int) (x : int) : int = n m f x in
let two1 (f : ?) (x : int) : int = f (f x) in
let two2 (f : ?) (x : int -> int) : int -> int = f (f x) in
let four1 (x : ?) : int -> int = exp1 two1 two2 x in
let exp2 (m : ((int -> int) -> int -> int) -> (int -> int) -> int -> int) (n : ?) (f : (int -> int) -> int -> int) (x : int -> int) : int -> int = n m f x in
let two3 (f : ?) (x : int -> int) : int -> int = f (f x) in
let two4 (f : ?) (x : (int -> int) -> int -> int) : (int -> int) -> int -> int = f (f x) in
let four2 (x : ?) : (int -> int) -> int -> int = exp2 two3 two4 x in
let twoHundredFiftySix (y : ?) : int -> int = exp1 four1 four2 y in
let sixtyFiveThousandAndFiveHundredsThirtySix (z : ?) : int -> int = exp1 twoHundredFiftySix two2 z in
print_int (realnat sixtyFiveThousandAndFiveHundredsThirtySix);;