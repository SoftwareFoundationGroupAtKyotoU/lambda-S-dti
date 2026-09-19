open Types_lib

let builtins : builtin list = [
    { name = "array_to_list";
      impl = ITGL "let array_to_list arr = let n = Array.length arr in let rec aux i = if i >= n then [] else arr.(i) :: aux (i + 1) in aux 0;;";
      c_backing = CImpl "array_to_list" };
    { name = "array_iteri";
      impl = ITGL "let array_iteri f arr = let n = Array.length arr in let rec aux i = if i >= n then () else (f i arr.(i); aux (i + 1)) in aux 0;;";
      c_backing = CUnimplemented };
  ]
