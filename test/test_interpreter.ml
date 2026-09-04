open Format

open OUnit2

open Lambda_S_dti
open Syntax
open Config

let id x = x

let run state program ~config =
  let ppf = Utils.Format.empty_formatter in
  let lexbuf = Lexing.from_string (program ^ ";;") in
  let cc_state, u =
    state 
    |> Pipeline.parse ppf lexbuf
    |> Pipeline.typing_ITGL ppf
    |> Pipeline.translate_to_CC ppf ~config ~bench_ppf:Utils.Format.empty_formatter ~bench:0
  in
  try
    let state, _, v = 
      cc_state
      |> Pipeline.eval ppf ppf ~config
    in
    Pipeline.fresh_program state, asprintf "%a" Pp.pp_ty2 u, asprintf "%a" Pp.CC.pp_value2 v
  with
  | Blame (_, Pos) -> state, asprintf "%a" Pp.pp_ty2 u, "blame+"
  | Blame (_, Neg) -> state, asprintf "%a" Pp.pp_ty2 u, "blame-"

let config_B_eager              = create ~intoB:true ~eager:true ~monotonic:false ()
let config_B_lazy               = create ~intoB:true ~eager:false ~monotonic:false ()
let config_S_lazy_monotonic     = create ()
let config_S_eager_monotonic    = create ~eager:true ()
let config_S_lazy_nonmonotonic  = create ~monotonic:false ()
let config_S_eager_nonmonotonic = create ~eager:true ~monotonic:false ()
let config_A_lazy_monotonic     = create ~alt:true ()
let config_A_eager_monotonic    = create ~alt:true ~eager:true ()
let config_A_lazy_nonmonotonic  = create ~alt:true ~monotonic:false ()
let config_A_eager_nonmonotonic = create ~alt:true ~eager:true ~monotonic:false ()

let test_examples config =
  let state = Pipeline.init_state () ~config in
  let create_test i cases =
    let test_name = match cases with
      | (program, _, _) :: _ -> Printf.sprintf "[%d] %s" i program
      | [] -> string_of_int i
    in
    test_name >:: fun ctxt ->
      ignore @@ List.fold_left
        (fun state (program, expected_ty, expected_value) ->
           let state, actual_ty, actual_value = run state program ~config in
           assert_equal ~ctxt:ctxt ~printer:id expected_ty actual_ty;
           assert_equal ~ctxt:ctxt ~printer:id expected_value actual_value;
           state
        )
        state
        cases
  in
  let create_suite (category_name, category_cases) =
    category_name >::: List.mapi create_test category_cases
  in

  (* すべてのカテゴリを処理してリストにする *)
  List.map create_suite (Testcases.suites ~config)

let suite = [
  "test_B_eager"              >::: test_examples config_B_eager;
  "test_B_lazy"               >::: test_examples config_B_lazy;
  "test_S_lazy_monotonic"     >::: test_examples config_S_lazy_monotonic;
  "test_S_eager_monotonic"    >::: test_examples config_S_eager_monotonic;
  "test_S_lazy_nonmonotonic"  >::: test_examples config_S_lazy_nonmonotonic;
  "test_S_eager_nonmonotonic" >::: test_examples config_S_eager_nonmonotonic;
  "test_A_lazy_monotonic"     >::: test_examples config_A_lazy_monotonic;
  "test_A_eager_monotonic"    >::: test_examples config_A_eager_monotonic;
  "test_A_lazy_nonmonotonic"  >::: test_examples config_A_lazy_nonmonotonic;
  "test_A_eager_nonmonotonic" >::: test_examples config_A_eager_nonmonotonic;
]