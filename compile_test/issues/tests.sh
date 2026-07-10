run_test "issue1_example.ml" "3" "skip_static"
run_test "issue2_example1.ml" "3" "skip_static"
run_test "issue2_example2.ml" "$(printf "Blame on the expression side:\nFile \"issue2_example2.ml\", line 1, character 33 -- line 1, character 81")" "skip_static"