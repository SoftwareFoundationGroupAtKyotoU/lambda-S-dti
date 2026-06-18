open OUnit2

let suite = "test">:::[
    "test_interpreter">::: Test_interpreter.suite;
    "test_pp">::: Test_pp.suite;
    "test_typing">::: Test_typing.suite;
    "test_translate">::: Test_translate.suite;
  ]

let () = run_test_tt_main suite
