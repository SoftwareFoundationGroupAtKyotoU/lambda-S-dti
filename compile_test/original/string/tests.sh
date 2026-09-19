run_test "basic.ml" "hello, world"
run_test "dynamic.ml" "dyn hello" "skip_static"
run_test "tuple.ml" "helloworld"
run_test "concat.ml" "hello world"
run_test "concat_dynamic.ml" "foobar" "skip_static"
run_test "ref.ml" "after"
run_test "blame.ml" \
  "$(printf "Blame on the expression side:\nFile \"blame.ml\", line 2, character 14 -- line 2, character 15")" \
  "skip_static"
