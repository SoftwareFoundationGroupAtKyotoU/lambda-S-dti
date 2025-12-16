let rec loop_poly n acc p =
  if n = 0 then acc else loop_poly (n - 1) (p acc) p in 
let id x = x in
loop_poly 1000 0 id;;
