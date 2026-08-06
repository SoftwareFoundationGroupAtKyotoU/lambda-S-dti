let a = Array.make 3 (Array.make 2 0) in
a.(1) <- Array.make 5 0;
print_int (Array.length a + Array.length (a.(1)));;
