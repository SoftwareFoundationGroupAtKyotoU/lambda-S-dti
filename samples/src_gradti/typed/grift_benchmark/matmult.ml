let create_square (size : int) : int array =
  let x : int array = Array.make (size * size) 0 in
  (**)
  for i = 0 to size - 1 do
    for j = 0 to size - 1 do
      x.((size * i) + j) <- j + i
    done
  done;
  x;;

let mult_square (size : int) : int array =
  let x : int array = create_square size in
  let y : int array = create_square size in
  let r : int array = Array.make (size * size) 0 in
  (**)
  for i = 0 to size - 1 do
    for j = 0 to size - 1 do
      for k = 0 to size - 1 do
        r.(i * size + j) <- r.(i * size + j) + (x.(i * size + k) * y.(k * size + j))
      done
    done
  done;
  r;;

(* main *)
let size = read_int () in
let r = mult_square size in
print_int r.(size * size - 1);;
