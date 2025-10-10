let rec even (x:int) : bool = 
  if x = 0 then true else (if x - 1 = 0 then false else (even (x - 2))) 
in even 1000000;;