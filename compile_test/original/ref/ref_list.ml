let rs = [ref 1; ref 2; ref 3] in
match rs with
| a :: b :: c :: [] ->
    a := !a * 10;
    print_int (!a + !b + !c)
| _ -> print_int 0;;