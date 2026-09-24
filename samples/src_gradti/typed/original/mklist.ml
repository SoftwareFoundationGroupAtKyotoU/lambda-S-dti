let rec mklist (n : int) (i : int) (acc : int list) : int list =
  if i = n then acc
  else mklist n (i + 1) (i :: acc)
in mklist (read_int ()) 0 [];;
