let r0 = ref 42 in
let r1 = (r0 : ? ref) in
r1 := (true : ?);;
