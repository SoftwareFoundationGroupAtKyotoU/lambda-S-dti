let rec repeat n f x :int = 
  if n = 0 then x else repeat (n-1) f (f x) 
in print_int (repeat 10 (fun x -> x) 4);;

(*
let repeat = fun 'x13,'x14 -> fix repeat ((n: int), k11): ('x14 -> 'x13) -> ? -> int = (fun ((f: 'x14 -> 'x13), k12) -> (fun ((x: ?), k13) -> 
  if n = 0 then (let k14 = int?p;id{int};;k13 in x<k14>) 
  else repeat (n - 1, id{('x14 -> 'x13) -> ? -> int}) (f, id{? -> int}) (f (x<'x14?p>, 'x13!), k13))<k12>)<k11> 
in print_int (repeat['x10,'x10] (10, id{('x10 -> 'x10) -> ? -> int}) (fun ((x: 'x10), k10) -> x<k10>, id{? -> int}) (4<id{int};int!>, id{int}), id{unit})
*)

(*
let rec _var_52 ['x13,'x14] (x_48, k13_49) = 
  let _var_64 = 0 in 
  if n_42=_var_64 then 
    let _var_53 = int?p;id{int} in 
    let k14_50 = _var_53;;k13_49 in 
    x_48<k14_50> 
  else 
    let _var_54 = 1 in 
    let _var_55 = n_42 - _var_54 in 
    let _var_56 = id{('x14 -> 'x13) -> ? -> int} in 
    let _var_57 = repeat_41:cls (_var_55, _var_56) in 
    let _var_58 = id{? -> int} in 
    let _var_62 = _var_57:cls (f_46, _var_58) in 
    let _var_59 = 'x14?p in 
    let _var_60 = x_48<_var_59> in 
    let _var_61 = 'x13! in 
    let _var_63 = f_46:cls (_var_60, _var_61) in 
    _var_62:cls (_var_63, k13_49) (fv:f_46,n_42,repeat_41)

let rec _var_51 ['x13,'x14] (f_46, k12_47) = 
  pcls _var_52 = _var_52[f_46,n_42,repeat_41] in 
  _var_52<k12_47> (fv:n_42,repeat_41)

let rec repeat_41 ['x13,'x14] (n_42, k11_43) = 
  pcls _var_51 = _var_51[n_42,repeat_41] in 
  _var_51<k11_43>

let rec _var_70 (x_44, k10_45) = x_44<k10_45>

exp:
plbl repeat_41 = repeat_41 in
let _var_67 = repeat_41['x10,'x10] in 
let _var_68 = 10 in 
let _var_69 = id{('x10 -> 'x10) -> ? -> int} in 
let _var_71 = _var_67:cls (_var_68, _var_69) in 
lbl _var_70 = _var_70 in 
let _var_73 = id{? -> int} in 
let _var_76 = _var_71:cls (_var_70, _var_73) in 
let _var_74 = 4 in 
let _var_75 = id{int};int! in 
let _var_77 = _var_74<_var_75> in 
let _var_78 = id{int} in 
let _var_79 = _var_76:cls (_var_77, _var_78) in 
let _var_80 = id{unit} in 
print_int:label (_var_79, _var_80)
*)