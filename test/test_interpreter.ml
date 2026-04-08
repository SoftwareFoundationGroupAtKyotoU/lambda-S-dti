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
    if config.kNorm then
      let state, _, kv = 
        cc_state
        |> Pipeline.kNorm_funs ppf ~config
        |> Pipeline.keval ppf ~config
      in
      state |> Pipeline.change_state_program (), asprintf "%a" Pp.pp_ty2 state.ty, asprintf "%a" Pp.KNorm.pp_value2 kv
    else
      let state, _, v = 
        cc_state
        |> Pipeline.eval ppf ~config
      in
      state |> Pipeline.change_state_program (), asprintf "%a" Pp.pp_ty2 state.ty, asprintf "%a" Pp.CC.pp_value2 v
  with
  | Blame (_, Pos) -> state, asprintf "%a" Pp.pp_ty2 cc_state.ty, "blame+"
  | Blame (_, Neg) -> state, asprintf "%a" Pp.pp_ty2 cc_state.ty, "blame-"

let config_B = create ~intoB:true ~eager:true ()
let config_S = create ()
let config_A = create ~alt:true ()
let config_B_k = create ~kNorm:true ~intoB:true ~eager:true ()
let config_S_k = create ~kNorm:true ()
let config_A_k = create ~kNorm:true ~alt:true ()

let ext_B (a, b, c, _, _, _) = (a, b, c)
let ext_S (a, b, _, d, _, _) = (a, b, d)
let ext_A (a, b, _, d, _, _) = (a, b, d)
let ext_B_k (a, b, _, _, e, _) = (a, b, e)
let ext_S_k (a, b, _, _, _, f) = (a, b, f)
let ext_A_k (a, b, _, _, _, f) = (a, b, f)

let test_examples config ext =
  let state = Pipeline.init_state () ~config in
  let test i cases =
    (string_of_int i) >:: fun ctxt ->
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
  List.mapi test (List.map (fun l -> List.map ext l) Testcases.tests)

let suite = [
  "test_B"   >::: test_examples config_B ext_B;
  "test_S"   >::: test_examples config_S ext_S;
  "test_A"   >::: test_examples config_A ext_A;
  "test_B_k" >::: test_examples config_B_k ext_B_k;
  "test_S_k" >::: test_examples config_S_k ext_S_k;
  "test_A_k" >::: test_examples config_A_k ext_A_k;
]