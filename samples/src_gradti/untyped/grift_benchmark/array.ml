(* let create_x (n : int) : (int array) =
  let result = Array.make n 0 in
  (for i = 0 to n - 1 do
    result.(i) <- i;
  done;
  result)
in
let create_y (x : int array) : (int array) =
  let n = Array.length x in
  let result = Array.make n 0 in
  (for i = n - 1 downto 0 do
    result.(i) <- x.(i)
  done;
  result)
in
let my_try (n : int) : int =
  let x = create_y (create_x n) in 
  n
in
let rec go (m : int) (n : int) (r : int) : int =
  if m > 0 then
    go (m - 1) n (my_try n)
  else r
in
print_int (go (read_int ()) (read_int ()) 0);; *)
1;;