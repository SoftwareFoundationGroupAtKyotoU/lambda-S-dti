(* A top-level partial application of fmin is a C global (I4) that the local
   function g reads without m appearing at the call site; sinking it towards its
   use (sink_prims in toC.ml) must not move it past the call (it segfaulted). *)
let m = fmin 1.0 in
let b = 1 in
let r = if b = 1 then (let g x = m x in g 2.0) else 0.0 in
print_float r;;
