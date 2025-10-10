let realnat = fun n -> n (fun x -> x + 1) 0 in
let exp =
  fun m ->
  fun n ->
  fun f ->
  fun x -> n m f x in
let two = fun f -> fun x -> f (f x) in
let four = exp two two in
let twoHundredFiftySix = exp four four in
realnat twoHundredFiftySix;;
(* let sixtyFiveThousandAndFiveHundredsThirtySix = exp twoHundredFiftySix two in *)
(* realnat sixtyFiveThousandAndFiveHundredsThirtySix;; *)