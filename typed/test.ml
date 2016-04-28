open OUnit2

let suite =
  test_list [ "check test" >::: TestCheck.tests ;
	      "parser test" >::: ParserT.tests ;
	      "Eval test" >::: TestEval.tests
	    ]

let () =
  run_test_tt_main suite
