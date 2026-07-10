let rec f x = 123 in
let rec g x = 456 in
let x = f () in
print_int ((if x <= 0 then g () + x else x) + x);;
(* xがthen節ではセーブされ、else節ではセーブされない *)
(* さらに、xがthen節ではr0に、else節ではr1にある *)
