open OUnit2
open Sexplib
open Lambda

let test1x = (Pi("A",Star,Pi("B",(Pi ("x", Inv(BVar 2),Star)),Pi("C",(Pi ("x", Inv(BVar 3),Star)), (Pi ("1",(Pi ("2", (Pi("a",Star,Pi("b",(Inv(Appl(BVar 5 ,Inv(BVar 1)))),Inv(Appl(BVar 4, Inv(BVar 1)))))),(Pi ("a",Inv(BVar 5),Inv(Appl(BVar 4,Inv(BVar 0))))))),(Pi ("a",Inv(BVar 4),Inv(Appl(BVar 2,Inv(BVar 0)))))))))))

let test1y = "(pi A * (pi B (pi x A *) (pi C (pi x A *) (pi 1 (pi 2 (pi a A (pi b (B a) (C a))) (pi a A (B a))) (pi a A (C a))))))"

let testcheck3x = "(pi A * (pi B (pi x A *) *))"

let testcheck4x = "(pi F (-> * *) (pi X * (-> (F X) *)))"


let testcheckPositive inputTerm inputType =
  assert_bool "Not type correct" (check [] (read inputTerm) inputType "" [])

let testcheckNegative inputTerm inputType =
  assert_bool "Unexpectedly type correct" (not (check [] (read inputTerm) inputType "" []))



(* let testcheck1 text_ctxt = assert_equal (check [] (test1x) Star "" []) (true) *)
let testcheck1 test_ctxt = assert_equal 
			     (check [] (read testcheck3x) Star "" []) 
			     (true) 
let testcheck2 test_ctxt = assert_equal 
			     (check [] (Pi("x",Star,Star)) Star "" []) 
			     (true)
let testcheck3 test_ctxt = assert_equal 
			     (check [] (read test1y) Star "" []) 
			     (true)
let testcheck4 test_ctxt = assert_equal 
			     (check [] (read testcheck4x) Star "" [])
			     (true)
let testcheck5 test_ctxt = assert_equal 
			     (check [] (read "(succ zero)") Nat "" [])
			     (true)


let eval = 
  ["testcheck1">:: testcheck1;
  "testcheck2">:: testcheck2;
  "testcheck3">:: testcheck3;
  "testcheck4">:: testcheck4;
  "testcheck5">:: testcheck5;]
