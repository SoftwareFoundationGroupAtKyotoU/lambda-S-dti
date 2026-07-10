run_test "assign.ml" "2"
run_test "basic.ml" "1"
# run_test "blame" \
#   "$(printf "Blame on the environment side:\nFile \"env_side.ml\", line 1, character 29 -- line 1, character 39")" \
#   "skip_static"
run_test "closuer.ml" "123"
run_test "counter.ml" "3"
run_test "dynamic.ml" "2" "skip_static"
run_test "incr.ml" "12"
run_test "list.ml" "15"
run_test "seq.ml" "3"
run_test "static_ty.ml" "6"
run_test "swap.ml" "32"