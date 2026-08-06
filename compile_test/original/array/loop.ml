let create_x (n : int) : (int array) =
  let result = Array.make n 0 in
  for i = 0 to n - 1 do
    result.(i) <- i
  done;
  result
in
let sum_via_length (x : int array) : int =
  let n = Array.length x in
  let result = ref 0 in
  for i = 0 to n - 1 do
    result := !result + x.(i)
  done;
  !result
in
print_int (sum_via_length (create_x 6));;
