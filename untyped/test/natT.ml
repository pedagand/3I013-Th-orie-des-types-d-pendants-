open OUnit2

open Lambda
open Nat

let testsucc = Appl(succ,(int_to_lambda_term 0))
let plus_test = Appl(Appl(plus,(int_to_lambda_term 2)),(int_to_lambda_term 2))

let test1 test_ctxt = assert_equal (FreeVar "y") (FreeVar "y")
let test2 test_ctxt = assert_equal (BoundVar 0) (BoundVar 0)

(* batterie de test sur les nats *)

let test3 test_ctxt = assert_equal (reduction_forte testsucc 0) (int_to_lambda_term 1)
let test4 test_ctxt = assert_equal (reduction_forte plus_test 0) (int_to_lambda_term 4) 


let tests = 
["test 1">:: test1; 
 "test 2">:: test2;
"test 3">:: test3;
"test 4">:: test4]


						

