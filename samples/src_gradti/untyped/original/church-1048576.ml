(* let realnat n = n (fun x -> x + 1) 0 in
let exp m n f x = n m f x in
let two f x = f (f x) in
let four = exp two two in
let twoHundredFiftySix y = exp (four ()) (four ()) in
let sixtyFiveThousandAndFiveHundredsThirtySix z = exp (twoHundredFiftySix ()) two in
realnat sixtyFiveThousandAndFiveHundredsThirtySix;; *)

let realnat n = n (fun x -> x + 1) 0 in
let exp m n f x = n m f x in
let two f x = f (f x) in
let four x = exp two two x in
let twoHundredFiftySix y = exp four four y in
let sixtyFiveThousandAndFiveHundredsThirtySix z = exp twoHundredFiftySix two z in
let mult m n f x = m (n f) x in
let sixteen y = exp two four y in
print_int (realnat (mult sixtyFiveThousandAndFiveHundredsThirtySix sixteen));;
