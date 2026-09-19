type point = { x: int; y: int };;
let f (v: ?) = v.x in
let p : point = { x = 7; y = 8 } in
print_int (f (p : ?));;
