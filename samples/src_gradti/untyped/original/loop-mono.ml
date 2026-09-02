let rec loop (n: int) (acc:int) (f:int -> int) : int =
  if n = 0 then acc 
  else loop (n - 1) (f acc) f 
in
let id (x:int) : int = x in
print_int (loop (read_int ()) 0 id);;