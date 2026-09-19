type point = { x: int; y: int; z: int };;
let p = { x = 1; y = 2; z = 3 } in
let q = { p with x = 10; z = 30 } in
print_int (q.x + q.y + q.z);;
