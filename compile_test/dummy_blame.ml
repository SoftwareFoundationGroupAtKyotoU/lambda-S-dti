let f (x:?) = x in
let g (y:int->int) = f y in
g ((fun z -> z + 1):?) (true:?);;

(* let f = fun ((x: ?), k17) -> x<k17> in 
let g = fun 'x17 -> fun ((x: 'x17), k16) -> f (x<'x17!>, k16) in 
g['x18] 
  (
    let k14 = (int?p;id{int})->(id{int};int!);(? -> ?)!;;'x18?p in 
    (fun ((x: int), k15) -> (x + 1)<k15>)<k14>, (? -> ?)?p;id{? -> ?}
  ) 
  (true<id{bool};bool!>, id{?})

DTI: 'x18 is instantiated to 'x20 -> 'x19
DTI: 'x20 is instantiated to int
DTI: 'x19 is instantiated to int

(fun ((x: int -> int), k16) -> f (x<|int -> int|!>, k16))
  (
    let k14 = id{int->int} in 
    (fun ((x: int), k15) -> (x + 1)<k15>)<k14>, (? -> ?)?p;id{? -> ?}
  ) 
  (true<id{bool};bool!>, id{?})

(fun ((x: ?), k17) -> x<k17>) 
  ((fun ((x: int), k15) -> (x + 1)<k15>)<|int -> int|!>, (? -> ?)?p;id{? -> ?})
  (true<id{bool};bool!>, id{?})

(fun ((x: int), k15) -> (x + 1)<k15>)<(int?p;id{int})->(id{int};int!)>
  (true<id{bool};bool!>, id{?})

true<<id{bool};bool!>><int?p;id{int}> -> blame *)
  

