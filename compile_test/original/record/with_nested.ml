type point = { x: int; y: int };;
type rect = { tl: point; br: point };;
let r = { tl = { x = 0; y = 0 }; br = { x = 10; y = 20 } } in
let r2 = { r with br = { r.br with x = 99 } } in
print_int (r2.br.x + r2.br.y);;
