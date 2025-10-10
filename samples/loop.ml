let rec loop n acc f =
  if n = 0 then acc else loop (n - 1) (f acc) f in
let id x = x in
loop 1000 0 id;;
