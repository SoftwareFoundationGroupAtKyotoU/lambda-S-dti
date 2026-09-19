run_test "basic.ml" "$(printf "Az48\n")"
run_test "dynamic.ml" "Q" "skip_static"
run_test "mix.ml" "true 0 255" "skip_static"
run_test "blame.ml" \
  "$(printf "Blame on the expression side:\nFile \"blame.ml\", line 2, character 14 -- line 2, character 15")" \
  "skip_static"
