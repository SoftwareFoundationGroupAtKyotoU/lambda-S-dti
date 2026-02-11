let realnat = fun n -> n (fun x -> x + 1) 0 in
let two = fun f -> fun x -> f (f x) in
realnat two;;