let f (lst : ? list) = match lst with h :: _ -> (h : int) in
print_int (f [5; 6; 7]);;