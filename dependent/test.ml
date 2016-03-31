open OUnit2

let suite =
  test_list [ "Parser tests" >::: ParserT.tests
            (* ; "Boolean test" >::: BooleanT.tests *)
            ; "Nat test" >::: NatT.tests
	    ; "test unit" >::: TestUnit.eval
	    ; "test check" >::: TestCheck.eval]

let () =
  run_test_tt_main suite
