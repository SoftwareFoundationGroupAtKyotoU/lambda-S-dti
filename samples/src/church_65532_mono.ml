(* type nat1 = (int -> int) -> int -> int
type int2 = int -> int
type nat2 = (int2 -> int2) -> int2 -> int2
type int3 = int2 -> int2
type nat3 = (int3 -> int3) -> int3 -> int3

let realnat (n:nat1) = n (fun (x:int) -> x + 1) 0 in
let exp1 (m : nat1) (n : nat2) (f : int -> int)  (x : int) : int = n m f x in
let two1 (f : int -> int)  (x : int) : int = f (f x) in
let two2 (f : int2 -> int2)  (x : int2) : int2 = f (f x) in
let four1 (x :int2) : int -> int = exp1 two1 two2 x in

let exp2 (m : nat2) (n : nat3) (f : int2 -> int2) (x : int2) : int2 = n m f x in
let two3 (f : int2 -> int2)  (x : int2) = f (f x) in
let two4 (f : int3 -> int3)  (x : int3) = f (f x) in
let four2 (x :int3) : int2 -> int2 = exp2 two3 two4 x in
let twoHundredFiftySix (y : int2) : int -> int = exp1 four1 four2 y in
let sixtyFiveThousandAndFiveHundredsThirtySix (z:int2) : int -> int = exp1 twoHundredFiftySix two2 z in
print_int (realnat sixtyFiveThousandAndFiveHundredsThirtySix) *)

let realnat (n : (int -> int) -> int -> int) = 
  n (fun (x : int) -> x + 1) 0 
in

let exp1 (m : (int -> int) -> int -> int) 
         (n : ((int -> int) -> int -> int) -> (int -> int) -> int -> int) 
         (f : int -> int) 
         (x : int) : int = 
  n m f x 
in

let two1 (f : int -> int) (x : int) : int = 
  f (f x) 
in

let two2 (f : (int -> int) -> int -> int) (x : int -> int) : int -> int = 
  f (f x) 
in

let four1 (x : int -> int) : int -> int = 
  exp1 two1 two2 x 
in

let exp2 (m : ((int -> int) -> int -> int) -> (int -> int) -> int -> int) 
         (n : (((int -> int) -> int -> int) -> (int -> int) -> int -> int) -> ((int -> int) -> int -> int) -> (int -> int) -> int -> int) 
         (f : (int -> int) -> int -> int) 
         (x : int -> int) : int -> int = 
  n m f x 
in

let two3 (f : (int -> int) -> int -> int) (x : int -> int) = 
  f (f x) 
in

let two4 (f : ((int -> int) -> int -> int) -> (int -> int) -> int -> int) 
         (x : (int -> int) -> int -> int) = 
  f (f x) 
in

let four2 (x : (int -> int) -> int -> int) : (int -> int) -> int -> int = 
  exp2 two3 two4 x 
in

let twoHundredFiftySix (y : int -> int) : int -> int = 
  exp1 four1 four2 y 
in

let sixtyFiveThousandAndFiveHundredsThirtySix (z : int -> int) : int -> int = 
  exp1 twoHundredFiftySix two2 z 
in

print_int (realnat sixtyFiveThousandAndFiveHundredsThirtySix);;