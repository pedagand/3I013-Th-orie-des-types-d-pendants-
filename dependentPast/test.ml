open OUnit2

let suite =
  test_list [ "Parser tests" >::: ParserT.tests
            (* ; "Boolean test" >::: BooleanT.tests *)
            ; "Nat test" >::: NatT.tests
	    ; "test unit" >::: TestUnit.eval
	    ; "test check" >::: TestCheck.tests
	    ; "test pretty" >::: TestPretty.tests
	    ; "test sub" >::: TestSub.tests
	    ; "test equal" >::: TestEqual.tests
	    ; "test big_step">::: TestBig_step.tests
	    ]

let () =
  run_test_tt_main suite
