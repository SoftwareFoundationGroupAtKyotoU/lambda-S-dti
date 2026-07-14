let x = (([] : 'a list) : ?) in
(fun (b: ?) -> let y = (b: bool) :: x in ()) (true:?);
(match ((3: ?) :: x) with h :: t -> print_int ((h: 'a): ?));;

(* 
This program should occur a blame error.
However, because eager list erase the cast applied to empty list,
this program is now evaluated to 3 with -e flag
*)