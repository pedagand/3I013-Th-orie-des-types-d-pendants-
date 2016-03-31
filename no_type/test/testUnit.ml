open OUnit
open Lambda 

let test1 test_ctxt = assert_equal Appl(Abs(BoundVar 0),FreeVar v) (Lambda_calcul.evaluation (FreeVar v));;
let test2 test_ctxt = assert_equal Appl(Abs(BoundVar 0),Abs(BoundVar 0)) (Lambda_calcul.evaluation (Abs(BoundVar 0)));;
let test3 test_ctxt = assert_equal (relie_libre 1 0 (Abs(Abs(Appl((FreeVar "1"),FreeVar "0"))))) (Abs(Abs(Abs(Appl((BoundVar 2),FreeVar "0")))))

let eval = 
"eval">:::
["test 1">:: test1;
 "test 2">:: test2;
 "test 3">:: test3]

;;
let () = 
  run_test_tt_main eval

;;


(* 
(*test pour la fonction relie libre *)

let x = Abs(Abs(Appl((FreeVar "4"),FreeVar "0")))
let () = Printf.printf "%s \n" (lambda_term_to_string(x))
let () = Printf.printf "%s \n" (lambda_term_to_string(Abs(relie_libre 4 0 x)))
let y = Abs(Abs(Appl(FreeVar "1",Appl(FreeVar "0",BoundVar 0)))) 

 *)
