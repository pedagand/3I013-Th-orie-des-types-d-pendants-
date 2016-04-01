open OUnit2

let suite =
  test_list [ "Parser tests" >::: ParserT.tests
            ; "Boolean test" >::: BooleanT.tests 
            ; "Nat test" >::: NatT.tests ]

let () =
  run_test_tt_main suite
