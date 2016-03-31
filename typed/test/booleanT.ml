open OUnit2 

open Lambda
open Boolean
	

(* let test1 = Appl(Appl(Appl(cifthenelse,cfalse),FreeVar "y"),FreeVar "x") *)

(* XXX: Turn the 'printf's into proper tests *) 		
(* let test2 = Appl(Appl(cifthenelse, cfalse),FVar "y") *)
(* let () = Printf.printf "%s \n" (lambda_term_to_string (evaluation test2)) *)

(* let tests = ["ifthenelse" >:: fun ctxt -> assert_equal (evaluation test) (FreeVar "x")] *)

let tests = ["ifthenelse" >:: fun ctxt -> assert_equal (BVar 0) (BVar 0)] 
