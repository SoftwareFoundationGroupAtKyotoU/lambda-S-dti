open OUnit2

let suite = "test">:::[
    "test_examples">::: Test_examples.suite;
    "text_alternative">::: Test_alternative.suite;
    "test_kNormal">::: Test_kNormal.suite;
    "test_alternative_k">::: Test_alternative_k.suite;
    "test_pp">::: Test_pp.suite;
    "test_typing">::: Test_typing.suite;
  ]

let () = run_test_tt_main suite
