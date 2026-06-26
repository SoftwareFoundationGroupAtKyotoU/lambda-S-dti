open Format

open OUnit2

open Lambda_S_dti
open Syntax
open Config

let id x = x

let run state program ~config =
  let ppf = Utils.Format.empty_formatter in
  let lexbuf = Lexing.from_string (program ^ ";;") in
  let cc_state =
    state 
    |> Pipeline.parse ppf lexbuf
    |> Pipeline.typing_ITGL ppf
    |> Pipeline.translate_to_CC ppf ~config ~bench_ppf:Utils.Format.empty_formatter ~bench:0
  in
  try
    let state, _, v = 
      cc_state
      |> Pipeline.eval ppf ~config
    in
    state |> Pipeline.change_state_program (), asprintf "%a" Pp.pp_ty2 state.ty, asprintf "%a" Pp.CC.pp_value2 v
  with
  | Blame (_, Pos) -> state, asprintf "%a" Pp.pp_ty2 cc_state.ty, "blame+"
  | Blame (_, Neg) -> state, asprintf "%a" Pp.pp_ty2 cc_state.ty, "blame-"

let config_B = create ~intoB:true ~eager:true ~monotonic:false ()
let config_S = create ()
let config_A = create ~alt:true ()

let ext_B (a, b, c, _) = (a, b, c)
let ext_S (a, b, _, d) = (a, b, d)
let ext_A (a, b, _, d) = (a, b, d)

let test_examples config ext =
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
    let extracted_cases = List.map (fun l -> List.map ext l) category_cases in
    category_name >::: List.mapi create_test extracted_cases
  in

  (* すべてのカテゴリを処理してリストにする *)
  List.map create_suite Testcases.suites

let suite = [
  "test_B"   >::: test_examples config_B ext_B;
  "test_S"   >::: test_examples config_S ext_S;
  "test_A"   >::: test_examples config_A ext_A;
]