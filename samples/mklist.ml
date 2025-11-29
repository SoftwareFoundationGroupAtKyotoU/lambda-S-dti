let rec mklist n i acc =
  if i = n then acc else mklist n (i + 1) (i :: acc) in
mklist 500 0 [];;
