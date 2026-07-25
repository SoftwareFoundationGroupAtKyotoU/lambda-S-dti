let counter = ref 0 in
let bump = fun (f : ?) -> ((f : int ref) := !(f : int ref) + 1) in
let rec loop n =
  if n = 0 then ()
  else (bump (counter : ?); loop (n - 1))
in
loop 10;
print_int !counter;;
