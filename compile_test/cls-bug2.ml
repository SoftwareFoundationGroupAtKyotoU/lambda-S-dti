let rec f n =
  if n < 0 then () 
  else (
  	print_int n;
  	(let a = [f] in
  	match a with 
  	| h :: _ -> h (n - 1)
		)
	) 
in f 9;;
