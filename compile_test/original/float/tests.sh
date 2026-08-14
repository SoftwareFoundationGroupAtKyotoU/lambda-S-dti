run_test "arith.ml" "4.0000003.5000006.0000003.500000"
run_test "comparison_all.ml" "truetruetruetruetruetrue"
run_test "dynamic.ml" "3.140000" "skip_static"
run_test "ref.ml" "2.500000"
run_test "array.ml" "1.5000002.5000001.500000"
run_test "tuple.ml" "4.000000"
run_test "list.ml" "6.000000"
run_test "blame.ml" \
  "$(printf "Blame on the expression side:\nFile \"blame.ml\", line 2, character 14 -- line 2, character 15")" \
  "skip_static"
