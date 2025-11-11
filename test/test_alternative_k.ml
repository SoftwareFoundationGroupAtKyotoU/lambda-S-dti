open Format

open OUnit2

open Lambda_S1_dti
open Syntax

let test_cases = List.map (fun l -> List.map (fun (a, _, _, d) -> (a, d)) l) Test_cases.tests

let id x = x

let run tyenv alphaenv kfunenvs kenv program =
  let parse str = Parser.toplevel Lexer.main @@ Lexing.from_string str in
  let e = parse @@ program ^ ";;" in
  let e, u = Typing.ITGL.type_of_program tyenv e in
  let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
  let new_tyenv, f, u' = Translate.ITGL.translate tyenv e in
  assert (Typing.is_equal u u');
  let u'' = Typing.LS.type_of_program tyenv f in
  assert (Typing.is_equal u u'');
  let f, alphaenv = KNormal.LS.alpha_program alphaenv f in
  (* let f, u''' = Translate.LS.translate_alt tyenv f in *)
  (* assert (Typing.is_equal u u''');*)
  let kf, kfunenvs = KNormal.kNorm_funs kfunenvs f in
  let kf = Translate.KNorm.translate_alt kf in
  try
    let kenv, _, kv = Eval.KNorm1.eval_program kenv kf ~debug:false in
    new_tyenv, alphaenv, kfunenvs, kenv, asprintf "%a" Pp.KNorm1.pp_value kv
  with
  | Eval.KBlame (_, Pos) -> tyenv, alphaenv, kfunenvs, kenv, "blame+"
  | Eval.KBlame (_, Neg) -> tyenv, alphaenv, kfunenvs, kenv, "blame-"

let test_examples =
  let test i cases =
    (string_of_int i) >:: fun ctxt ->
      ignore @@ List.fold_left
        (fun (tyenv, alphaenv, kfunenvs, kenv) (program, expected_kvalue) ->
           let tyenv, alphaenv, kfunenvs, kenv, actual_kvalue = run tyenv alphaenv kfunenvs kenv program in
           assert_equal ~ctxt:ctxt ~printer:id expected_kvalue actual_kvalue;
           tyenv, alphaenv, kfunenvs, kenv
        )
        (let _, tyenv, alphaenv, kfunenvs, kenv = Stdlib.pervasives in tyenv, alphaenv, kfunenvs, kenv)
        cases
  in
  List.mapi test test_cases

let suite = [
  "test_examples">::: test_examples;
]