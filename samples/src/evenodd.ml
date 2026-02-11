let rec even x = 
  if x = 0 then true 
  else (if x - 1 = 0 then false else (even (x - 2))) 
in print_bool (even (read_int ()));;
