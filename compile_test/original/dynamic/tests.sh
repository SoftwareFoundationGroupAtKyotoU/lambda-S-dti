# run_test "cast_coercion_difference.ml" "..." "skip_static"  # TODO: expected値確認
run_test "cast-abort.ml" \
  "$(printf "Blame on the expression side:\nFile \"cast-abort.ml\", line 2, character 10 -- line 2, character 15")" \
  "skip_static"
run_test "env_side.ml" \
  "$(printf "Blame on the environment side:\nFile \"env_side.ml\", line 1, character 29 -- line 1, character 39")" \
  "skip_static"
run_test "many_coerce.ml"    "4" "skip_static"
# run_test "occur_check.ml"                                   # print なし → 要改修
run_test "poly.ml" "10true" "skip_static"
run_test "repeat_f_dyn.ml"   "4" "skip_static"
run_test "repeat_x_dyn.ml"   "4" "skip_static"