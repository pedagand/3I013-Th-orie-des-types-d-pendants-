open OUnit2

open Lambda
open Nat


let test1 test_ctxt = assert_equal (BVar 0) (BVar 0);;
let test2 test_ctxt = assert_equal (FVar "y") (FVar "y");;

let tests = 
["test 1">:: test1;
 "test 2">:: test2]




		       

