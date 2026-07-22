# --- examples on ldti paper (https://dl.acm.org/doi/pdf/10.1145/3290331) ---
run_test "example1_success.ml" "5" "skip_static"
run_test "example1_fail.ml" "$(printf "Blame on the expression side:\nFile \"example1_fail.ml\", line 1, character 25 -- line 1, character 26")" "skip_static"
run_test "example2.ml" "2" "skip_static"
run_test "example3.ml" "false" "skip_static"
# --- example on space-efficient monotonic reference paper (https://wgt20.irif.fr/wgt20-final70-acmpaginated.pdf) ---
run_test "example_of_monotonic_reference.ml" "42" "skip_static"