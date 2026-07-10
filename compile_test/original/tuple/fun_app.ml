let fst p = match p with (a, _) -> a in
let snd p = match p with (_, b) -> b in
print_int (fst (10, 20) + snd (10, 20));;