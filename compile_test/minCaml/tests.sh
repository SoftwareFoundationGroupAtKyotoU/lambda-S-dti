# --- minCaml tests without float, tuple, and array (https://github.com/esumii/min-caml) ---
  # omitting some "rec", introducing dummy variable name instead of _
run_test "ack.ml" "8189"
run_test "adder.ml" "10"
run_test "adder2.ml" "35"
run_test "cls-bug.ml" "912"
run_test "cls-bug2.ml" "9876543210" # using a list instead of an array
run_test "cls-rec.ml" "1230"
run_test "cls-reg-bug.ml" "$(printf "55\n")" # tuples are curried
run_test "even-odd.ml" "false" # introducing true and false
run_test "fib.ml" "832040"
# run_test "float.ml" : float
run_test "funcomp.ml" "247"
run_test "gcd.ml" "2700"
# run_test "inprod*.ml" : tuple
run_test "join-reg.ml" "912"
run_test "join-reg2.ml" "789"
run_test "join-stack.ml" "1037"
run_test "join-stack2.ml" "246"
run_test "join-stack3.ml" "912"
# run_test "matmul*.ml" : array
run_test "non-tail-if.ml" "-10" # using int nums instead of "truncate (float)"
run_test "non-tail-if2.ml" "80238" # using a list instead of an array
run_test "print.ml" "$(printf "123\ntrue")" # test other prints (print_newline, print_bool)
run_test "shuffle.ml" "214563"
run_test "spill.ml" "-431"
run_test "spill2.ml" "77880" # using a list instead of an array
run_test "spill3.ml" "1617"
run_test "sum-tail.ml" "50005000"
run_test "sum.ml" "50005000"