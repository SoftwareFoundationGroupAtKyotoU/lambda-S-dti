# --- examples on ldti paper (https://dl.acm.org/doi/pdf/10.1145/3290331) ---
run_test "POPL2019_gradual_success.ml" "5" "skip_static"
run_test "POPL2019_gradual_fail.ml" "$(printf "Blame on the expression side:\nFile \"POPL2019_gradual_fail.ml\", line 1, character 25 -- line 1, character 26")" "skip_static"
run_test "POPL2019_incoherence_problem.ml" "2" "skip_static"
run_test "POPL2019_let_polymorphism.ml" "2true" "skip_static"
# --- example on space-efficient monotonic reference paper (https://wgt20.irif.fr/wgt20-final70-acmpaginated.pdf) ---
run_test "WGT2020_SE_monotonic_reference.ml" "42" "skip_static"
# --- example on monotonic reference paper (https://scispace.com/pdf/monotonic-references-for-efficient-gradual-typing-28y5d9d8st.pdf) ---
run_test "ESOP2015_cyclic_triple_heap.ml" "42" "skip_static"
run_test "ESOP2015_no-overhead_in_static.ml" "42" "skip_static"

# --- known-bug reproductions (NOT wired into the pass/fail suite; run manually to reproduce) ---
# mono_conflicting_casts_KNOWNBUG.ml: transcribes the blame{l2,l3} example (ESOP15 Section 5) -- aliasing one
#   "? ref" as both "int ref" and "bool ref" should raise Blame at the second, conflicting cast. Instead it
#   raises an *uncaught* Lambda_S_dti.Unify.Unify_error("failed to generate constraints: meet(int, bool)") that
#   escapes the Blame-conversion handler in lib/interpreter/eval.ml (whose try/with only catches Typing.Type_error).
# mono_write_through_upcast_ref_KNOWNBUG.ml: transcribes the blame{l1} example (ESOP15 Section 5) -- casting an
#   "int ref" up to "? ref" and then writing an inconsistent "(true : ?)" through it should raise Blame. Under the
#   default monotonic "-c" and "-c -a" backends this instead **segfaults**; only "-c -b --non_monotonic" produces
#   the correct Blame message.