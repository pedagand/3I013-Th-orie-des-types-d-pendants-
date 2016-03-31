open OUnit2
open Sexplib
open Lambda


(* ------------------------- test check ----------------------------------*)

(* TODO: put this in a separate file 'typecheckT.ml' *)
(* TODO: Write counter-examples, ie. terms that should not type check *)

(* TODO: use the following generic test handler: *)

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
  [  "test_sub_inTm1">:: test_sub_inTm1;
     "test_sub_inTm2">:: test_sub_inTm2;
     "test_sub_inTm3">:: test_sub_inTm3;]
    
