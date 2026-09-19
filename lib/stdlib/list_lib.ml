open Types_lib

let builtins : builtin list = [
    { name = "list_length";
      impl = ITGL "let rec list_length l = match l with [] -> 0 | _ :: t -> 1 + list_length t;;";
      c_backing = CUnimplemented };
    { name = "list_map";
      impl = ITGL "let rec list_map f l = match l with [] -> [] | h :: t -> f h :: list_map f t;;";
      c_backing = CUnimplemented };
    { name = "list_fold_left";
      impl = ITGL "let rec list_fold_left f acc l = match l with [] -> acc | h :: t -> list_fold_left f (f acc h) t;;";
      c_backing = CUnimplemented };
    { name = "list_init";
      impl = ITGL "let list_init n f = let rec aux i = if i >= n then [] else f i :: aux (i + 1) in aux 0;;";
      c_backing = CUnimplemented };
    { name = "list_mapi";
      impl = ITGL "let list_mapi f l = let rec aux i l = match l with [] -> [] | h :: t -> f i h :: aux (i + 1) t in aux 0 l;;";
      c_backing = CUnimplemented };
    { name = "list_iteri";
      impl = ITGL "let list_iteri f l = let rec aux i l = match l with [] -> () | h :: t -> f i h; aux (i + 1) t in aux 0 l;;";
      c_backing = CUnimplemented };
  ]
