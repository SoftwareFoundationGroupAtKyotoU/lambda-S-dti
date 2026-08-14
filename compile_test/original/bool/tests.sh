run_test "bool_ops.ml"       "truefalsetruefalsefalsetrue"
run_test "comparison_all.ml" "truetruetruetruetruetrue"
run_test "dynamic.ml" "true" "skip_static"
run_test "unit_as_bool_blame.ml" \
  "$(printf "Blame on the expression side:\nFile \"unit_as_bool_blame.ml\", line 2, character 15 -- line 2, character 16")" \
  "skip_static"
run_test "bool_as_unit_blame.ml" \
  "$(printf "Blame on the expression side:\nFile \"bool_as_unit_blame.ml\", line 2, character 15 -- line 2, character 16")" \
  "skip_static"
