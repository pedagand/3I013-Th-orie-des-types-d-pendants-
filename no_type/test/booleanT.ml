open OUnit2 

open Lambda
open Boolean
	

let test = Appl(Appl(Appl(cifthenelse,cfalse),FreeVar "y"),FreeVar "x")


let tests = ["ifthenelse" >:: fun ctxt -> assert_equal (evaluation test) (FreeVar "x")]
	      
