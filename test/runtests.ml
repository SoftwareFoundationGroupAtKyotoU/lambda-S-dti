open OUnit2

let suite = "test">:::[
    "test_S">::: Test_S.suite;
    "text_A">::: Test_A.suite;
    "text_B">::: Test_B.suite;    
    "test_S_k">::: Test_S_k.suite;
    "test_A_k">::: Test_A_k.suite;
    "test_B_k">::: Test_B_k.suite;
    "test_pp">::: Test_pp.suite;
    "test_typing">::: Test_typing.suite;
  ]

let () = run_test_tt_main suite
