open OUnit2
open Sexplib
open Lambda


(* ------------------------- test check ----------------------------------*)

(* TODO: put this in a separate file 'typecheckT.ml' *)
(* TODO: Write counter-examples, ie. terms that should not type check *)

(* TODO: use the following generic test handler: *)


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
  [  "test_pretty1">:: test_pretty1;
     "test_pretty2">:: test_pretty2;
     "test_pretty3">:: test_pretty3;
     "test_pretty4">:: test_pretty4;
     "test_pretty5">:: test_pretty5;
     "test_pretty6">:: test_pretty6;
     "test_pretty7">:: test_pretty7;
     "test_sub_inTm1">:: test_sub_inTm1;
     "test_sub_inTm2">:: test_sub_inTm2;
     "test_sub_inTm3">:: test_sub_inTm3;]
    
