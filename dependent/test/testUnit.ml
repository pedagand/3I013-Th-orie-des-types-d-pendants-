open OUnit2
open Sexplib
open Lambda


(* ------------------------- test check ----------------------------------*)

(* TODO: put this in a separate file 'typecheckT.ml' *)
(* TODO: Write counter-examples, ie. terms that should not type check *)

(* TODO: use the following generic test handler: *)

let testcheckPositive inputTerm inputType =
  assert_bool "Not type correct" (check [] (read inputTerm) inputType "" [])

let testcheckNegative inputTerm inputType =
  assert_bool "Unexpectedly type correct" (not (check [] (read inputTerm) inputType "" []))


(*test de check terme *)

let test1x = (Pi("A",Star,Pi("B",(Pi ("x", Inv(BVar 2),Star)),Pi("C",(Pi ("x", Inv(BVar 3),Star)), (Pi ("1",(Pi ("2", (Pi("a",Star,Pi("b",(Inv(Appl(BVar 5 ,Inv(BVar 1)))),Inv(Appl(BVar 4, Inv(BVar 1)))))),(Pi ("a",Inv(BVar 5),Inv(Appl(BVar 4,Inv(BVar 0))))))),(Pi ("a",Inv(BVar 4),Inv(Appl(BVar 2,Inv(BVar 0)))))))))))

let test1y = "(pi A * (pi B (pi x A *) (pi C (pi x A *) (pi 1 (pi 2 (pi a A (pi b (B a) (C a))) (pi a A (B a))) (pi a A (C a))))))"

let testcheck3x = "(pi A * (pi B (pi x A *) *))"

let testcheck4x = "(pi F (-> * *) (pi X * (-> (F X) *)))"


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
			     




(* ------------------------- test pretty_print_inTm ----------------------- *)

(* TODO: put this in a separate file 'prettyPrintT.ml' *)

(* TODO: use the following generic test handler *)

(* We compare pretty-printed strings based on the tokens (ignoring spacing) *)
let compare_term a b = 
  Sexp.of_string a = Sexp.of_string b

let testpretty input = 
  assert_equal ~cmp:compare_term 
    (pretty_print_inTm (read input) [])
    input

let test_pretty1 test_ctxt = 
  testpretty "((: (lambda x x) *) y)"

let test_pretty2 test_ctxt = assert_equal
			 (read(pretty_print_inTm (Abs("x",Abs("y",Abs("z",Inv(Appl(BVar 2, Inv(Appl(BVar 1, Inv(BVar 0))))))))) [] ))
			 (read "(lambda (x y z) (x (y z)))")
let test_pretty3 test_ctxt = assert_equal 
			 (read(pretty_print_inTm (Inv(Ann(Abs("x",Inv(BVar 0)),Pi("x",Star,Star)))) []))
			 (read "(: (lambda x x) (pi x * *))")
let test_pretty4 test_ctxt = assert_equal 
			       (*(read (pretty_print_inTm (test1x) [])) 
			       (read (test1y)) *) () () 
let test_pretty5 test_ctxt = assert_equal 
			       (read (pretty_print_inTm ((Pi("x",Star,Pi("y",Star,Pi("z",Star,Star))))) [])) 
			       (read "(pi (x y z ) * *)") 
let test_pretty6 test_ctxt = assert_equal 
			       (read (pretty_print_inTm (Succ(Succ(Zero))) [])) 
			       (read "(succ (succ zero))") 
let test_pretty7 test_ctxt = assert_equal 
			       (read (pretty_print_inTm (Inv(Iter(Nat,Nat,Nat,Nat))) []))
			       (read "(iter N N N N)") 



(* ------------------------- test substitution  --------------------------- *)

(* TODO: put this in a separate file 'substT.ml' *)
let test_sub_inTm1 text_ctxt = assert_equal 
				 (substitution_inTm (read "(lambda x (x 0))") (FVar "y") (-1))
				 (read "(lambda x (y 0))")
let test_sub_inTm2 test_ctxt = assert_equal
				 (substitution_inTm (read "(pi x * (pi y x *))") (FVar "lol") (-1))
				 (read "(pi x * (pi y lol *))") 

let test_sub_inTm3 test_ctxt = assert_equal
				 (substitution_inTm (read "(lambda x (succ x))") (FVar "lol") (-1)) 
				 (read "(lambda x (succ lol))")
(* petite question esque c'est pas plus judicieu de mettre zero et succ dans 
les exTm *)
			       (* 
let test_sub_inTm4 test_ctxt = assert_equal
				 (substitution_inTm  (Inv(Ifte(True,BVar 0,BVar 0))) (FVar "x") 0 )
				 (Inv(Ifte(True,FVar "x",FVar "x")))
 *)
			       


let eval = 
 ["testcheck1">:: testcheck1;
  "testcheck2">:: testcheck2;
  "testcheck3">:: testcheck3;
  "testcheck4">:: testcheck4;
  "testcheck5">:: testcheck5;
  "test_pretty1">:: test_pretty1;
  "test_pretty2">:: test_pretty2;
  "test_pretty3">:: test_pretty3;
  "test_pretty4">:: test_pretty4;
  "test_pretty5">:: test_pretty5;
  "test_pretty6">:: test_pretty6;
  "test_pretty7">:: test_pretty7;
  "test_sub_inTm1">:: test_sub_inTm1;
  "test_sub_inTm2">:: test_sub_inTm2;
  "test_sub_inTm3">:: test_sub_inTm3;]

