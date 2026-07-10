let b2i b = match b with true -> 1 | false -> 0 in
print_int (b2i true);
print_int (b2i false);;