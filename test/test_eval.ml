open Format

open OUnit2

open Lambda_S_dti
open Syntax
open Config

let id x = x

let run env tyenv kfunenvs kenv program ~config =
  let parse str = Parser.toplevel Lexer.main @@ Lexing.from_string str in
  let e = parse @@ program ^ ";;" in
  let e, u = Typing.ITGL.type_of_program tyenv e in
  let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
  let new_tyenv, f, u' = Translate.ITGL.translate ~intoB:config.intoB tyenv e in
  assert (Typing.is_equal u u');
  let u'' = Typing.CC.type_of_program tyenv f in
  assert (Typing.is_equal u u'');
  let f =
    if config.intoB then f
    else if config.alt then Translate.CC.translate_alt tyenv f
    else Translate.CC.translate tyenv f
  in
  try
    if config.kNorm then
      let kf, kfunenvs = KNormal.kNorm_funs kfunenvs f in
      let kenv, _, kv = Eval.KNorm.eval_program kenv kf in
      env, new_tyenv, kfunenvs, kenv, asprintf "%a" Pp.pp_ty2 u, asprintf "%a" Pp.KNorm.pp_value2 kv
    else
      let env, _, v = Eval.CC.eval_program env f in
      env, new_tyenv, kfunenvs, kenv, asprintf "%a" Pp.pp_ty2 u, asprintf "%a" Pp.CC.pp_value2 v
  with
  | Blame (_, Pos) -> env, tyenv, kfunenvs, kenv, asprintf "%a" Pp.pp_ty2 u, "blame+"
  | Blame (_, Neg) -> env, tyenv, kfunenvs, kenv, asprintf "%a" Pp.pp_ty2 u, "blame-"

let config_B = create ~kNorm:false ~alt:false ~intoB:true  ~eager:false ~compile:false ~static:false ~hash:false ~opt_file:None ()
let config_S = create ~kNorm:false ~alt:false ~intoB:false ~eager:false ~compile:false ~static:false ~hash:false ~opt_file:None ()
let config_A = create ~kNorm:false ~alt:true  ~intoB:false ~eager:false ~compile:false ~static:false ~hash:false ~opt_file:None ()
let config_B_k = create ~kNorm:true ~alt:false ~intoB:true  ~eager:false ~compile:false ~static:false ~hash:false ~opt_file:None ()
let config_S_k = create ~kNorm:true ~alt:false ~intoB:false ~eager:false ~compile:false ~static:false ~hash:false ~opt_file:None ()
let config_A_k = create ~kNorm:true ~alt:true  ~intoB:false ~eager:false ~compile:false ~static:false ~hash:false ~opt_file:None ()

let ext_B (a, b, c, _, _, _) = (a, b, c)
let ext_S (a, b, _, d, _, _) = (a, b, d)
let ext_A (a, b, _, d, _, _) = (a, b, d)
let ext_B_k (a, b, _, _, e, _) = (a, b, e)
let ext_S_k (a, b, _, _, _, f) = (a, b, f)
let ext_A_k (a, b, _, _, _, f) = (a, b, f)

let test_examples config ext =
  let test i cases =
    (string_of_int i) >:: fun ctxt ->
      ignore @@ List.fold_left
        (fun (env, tyenv, kfunenvs, kenv) (program, expected_ty, expected_value) ->
           let env, tyenv, kfunenvs, kenv, actual_ty, actual_value = run env tyenv kfunenvs kenv program ~config in
           assert_equal ~ctxt:ctxt ~printer:id expected_ty actual_ty;
           assert_equal ~ctxt:ctxt ~printer:id expected_value actual_value;
           env, tyenv, kfunenvs, kenv
        )
        (Stdlib.pervasives ~config)
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