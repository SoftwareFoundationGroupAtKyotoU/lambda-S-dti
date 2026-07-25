let r = (ref [1;2;3] : ?) in
let s = (r : int list ref) in
match !s with
| a :: b :: c :: [] -> print_int (a + b + c)
| _ -> print_int 0;;
