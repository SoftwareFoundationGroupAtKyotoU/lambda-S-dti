run_test "basic.ml"  "8"
run_test "blame.ml" \
  "$(printf "Blame on the expression side:\nFile \"cast-abort.ml\", line 3, character 7 -- line 3, character 8")" \
  "skip_static"
run_test "dynamic.ml" "3" "skip_static"
run_test "fun_app.ml" "30"
run_test "nested.ml" "6"
run_test "triple.ml" "4"