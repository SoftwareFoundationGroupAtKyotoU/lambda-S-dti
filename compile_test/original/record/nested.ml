type point = { x: int; y: int };;
type rect = { tl: point; br: point };;
let r = { tl = { x = 0; y = 0 }; br = { x = 10; y = 20 } } in
print_int (r.br.x + r.br.y);;
