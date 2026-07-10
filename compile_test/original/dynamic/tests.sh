run_test "cast-abort.ml" \
  "$(printf "Blame on the expression side:\nFile \"cast-abort.ml\", line 2, character 10 -- line 2, character 15")" \
  "skip_static"
run_test "many_coerce.ml"    "4" "skip_static"
run_test "repeat_f_dyn.ml"   "4" "skip_static"
run_test "repeat_x_dyn.ml"   "4" "skip_static"
# run_test "cast_coercion_difference.ml" "..." "skip_static"  # TODO: expected値確認
# run_test "occur_check.ml"                                   # print なし → 要改修
