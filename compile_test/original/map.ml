let rec map f lst =
  match lst with
  | [] -> []
  | h :: t -> f h :: map f t
in
let result = map (fun x -> x * 2) [1; 2; 3] in
match result with
| a :: b :: c :: [] -> print_int (a + b + c)
| _ -> print_int 0;;