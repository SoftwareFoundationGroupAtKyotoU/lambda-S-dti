let f x = 12345 in
let y = [3; 3; 3; 3; 3; 3; 3; 3; 3; 3] in
let x = 67890 in
print_int (match y with h :: t -> if h = 3 then f () + (match t with h :: _ -> h) + x else 7);;
