let create (l1 : int) (l2 : int) : int array =
  let x = Array.make (l1 * l2) 0 in
  for i = 0 to l1-1 do
    for j = 0 to l2-1 do
      x.((l2 * i) + j) <- j + i
    done
  done;
  x
in
let mult (x : int array) (x1 : int) (x2 : int) (y : int array) (y1 : int) (y2 : int) : int array =
  let r : int array = Array.make (y2 * x1) 0 in
  for i = 0 to x1-1 do
    for j = 0 to y2-1 do
      if j < y2 then
        for k = 0 to y1-1 do
          r.(i * y2 + j) <- r.(i*y2+j) + (x.(i * x2 + k) * y.(k * y2 + j))
        done
      else ()
    done
  done;
  r
in
let rec print_r x size i =
  if i = size * size then ()
  else (print_int (x.(i)); print_r x size (i + 1))
in
let size = read_int () in
let a = create size size in
let b = create size size in
let r = mult a size size b size size in
print_r r size 0;;