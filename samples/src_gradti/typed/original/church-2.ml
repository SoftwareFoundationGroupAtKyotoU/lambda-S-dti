let realnat (n : (int -> int) -> int -> int) = n (fun (x : int) -> x + 1) 0 in
let two (f : int -> int) (x : int) = f (f x) in
realnat two;;
