let create_x (n : int) : int array =
  let result : int array = Array.make n 0 in
  (**)
  for i = 0 to n - 1 do
    result.(i) <- i
  done;
  result;;

let create_y (x : int array) : int array =
  let n : int = Array.length x in
  let result : int array = Array.make n 0 in
  (**)
  for i = 0 to n - 1 do
    result.(n - i - 1) <- x.(n - i - 1)
  done;
  result;;

let my_try (n : int) : int =
  Array.length (create_y (create_x n));;

let rec go (m : int) (n : int) (r : int) : int =
  if m > 0 then
    go (m - 1) n (my_try n)
  else r;;

(* main *)
let input1 = read_int () in
let input2 = read_int () in
print_int (go input1 input2 0);;
