run_test "issue1_example.ml" "3" "skip_static"
run_test "issue2_example1.ml" "3" "skip_static"
run_test "issue2_example2.ml" "$(printf "Blame on the environment side:\nFile \"issue2_example2.ml\", line 1, character 40 -- line 1, character 41")" "skip_static"