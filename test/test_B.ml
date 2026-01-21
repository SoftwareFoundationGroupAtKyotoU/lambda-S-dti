open Format

open OUnit2

open Lambda_S_dti
open Syntax

let test_cases = List.map (fun l -> List.map (fun (a, b, c, _, _, _) -> (a, b, c)) l) Testcases.tests

let id x = x

let run env tyenv program =
  let parse str = Parser.toplevel Lexer.main @@ Lexing.from_string str in
  let e = parse @@ program ^ ";;" in
  let e, u = Typing.ITGL.type_of_program tyenv e in
  let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
  let new_tyenv, f, u' = Translate.ITGL.translate ~intoB:true tyenv e in
  assert (Typing.is_equal u u');
  let u'' = Typing.CC.type_of_program tyenv f in
  assert (Typing.is_equal u u'');
  try
    let env, _, v = Eval.CC.eval_program env f in
    env, new_tyenv, asprintf "%a" Pp.pp_ty2 u, asprintf "%a" Pp.CC.pp_value2 v
  with
  | Blame (_, Pos) -> env, tyenv, asprintf "%a" Pp.pp_ty2 u, "blame+"
  | Blame (_, Neg) -> env, tyenv, asprintf "%a" Pp.pp_ty2 u, "blame-"

let test_examples =
  let test i cases =
    (string_of_int i) >:: fun ctxt ->
      ignore @@ List.fold_left
        (fun (env, tyenv) (program, expected_ty, expected_value) ->
           let env, tyenv, actual_ty, actual_value = run env tyenv program in
           assert_equal ~ctxt:ctxt ~printer:id expected_ty actual_ty;
           assert_equal ~ctxt:ctxt ~printer:id expected_value actual_value;
           env, tyenv
        )
        (let env, tyenv, _, _ = Stdlib.pervasives_LB ~debug:false ~compile:false in env, tyenv)
        cases
  in
  List.mapi test test_cases

let suite = [
  "test_examples">::: test_examples;
]