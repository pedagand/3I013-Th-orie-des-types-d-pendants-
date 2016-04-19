open OUnit2

open Lambda
open Nat

(* let testsucc = Appl(Ann(succ,(Fleche (Nat,(Fleche (Nat,(Fleche (Nat,Nat))))))),(value_to_inTm 0 (int_to_value 0))) *)

(*
let () = Printf.printf "test eval derniere chance \n";
	 Printf.printf "%s \n" (inTm_to_string (value_to_inTm 0 ( (big_step_eval_exTm testsucc [] )))[]);
	 Printf.printf "%s \n" (inTm_to_string (value_to_inTm 0 (int_to_value 1)) [])
 *)

(* test de relie libre *)
let test1 test_ctxt = assert_equal 
(Abs(Global "y",(relie_libre_inTm 0 0 (Abs(Global "x",Inv(Appl(BVar 0,Inv(FVar (Global "0")))))))))
(Abs(Global "y",Abs(Global "x",Inv(Appl(BVar 0,Inv(BVar 1))))))



(* let test2 test_ctxt = assert_equal (big_step_eval_exTm testsucc [] ) (int_to_value 1) poser la question de ce test qui ne marche pas *)
(* test de check *)
let test2 test_ctxt = assert_equal (check [] (Inv(Iter((Succ(Zero)),(Abs(Global "x",Succ(Inv(BVar 0)))),(Ann(Zero,Nat))))) Nat) (true)





let tests = 
["test 1">:: test1;
 "test 2">:: test2;
]

(* XXX: turn those 'printf's into actual tests. Cf. [booleanT] for examples *)

(* let tests = ["successeur" >:: fun ctxt -> assert_equal (BoundVar 1) (BoundVar 1);] *)



(*
(* let () = Printf.printf "%s \n" (lambda_term_to_string(reduction_forte succtest 0)) *)
let () = Printf.printf "%d \n" (lambda_term_to_int(reduction_forte testsucc 0))		

let () = Printf.printf "%s \n" (lambda_term_to_string(plus_test))
let () = Printf.printf "%s \n" (lambda_term_to_string(reduction_forte plus_test 0)) 
(*
let () = Printf.printf "%s \n" (lambda_term_to_string(reduction_forte testsucc))
let () = Printf.printf "%d \n" (lambda_term_to_int(reduction_forte testsucc))
 *)
(*let () = Printf.printf "%s \n" (lambda_term_to_string(reduction_forte plus_test)) *) 
						 
(*let () = Printf.printf "%s \n" (lambda_term_to_string(plus_test))
let () = Printf.printf "%s \n" (lambda_term_to_string(evaluation(plus_test))) *)


(*
let () = Printf.printf "%s \n" (lambda_term_to_string (int_to_lambda_term 0))
let () = Printf.printf "%s \n" (lambda_term_to_string (int_to_lambda_term 1))
let () = Printf.printf "%s \n" (lambda_term_to_string (int_to_lambda_term 2))
    

let () = Printf.printf "%d \n" (lambda_term_to_int(int_to_lambda_term 2))
let () = Printf.printf "%d \n" (lambda_term_to_int(int_to_lambda_term 1))
let () = Printf.printf "%d \n" (lambda_term_to_int(int_to_lambda_term 0)) *)
		       


 *)


(*
let () = 
  Printf.printf "\n test big step eval avec les nat \n";
  Printf.printf "%s \n" (lambda_term_to_string(typed_to_simple_exTm(testsucc)));
  Printf.printf "%s \n" (lambda_term_to_string(typed_to_simple_inTm (value_to_inTm 0 (big_step_eval_exTm testsucc []))));
  Printf.printf "%s \n" (lambda_term_to_string(typed_to_simple_exTm(testmegasucc)));
  Printf.printf "%s \n" (lambda_term_to_string(typed_to_simple_inTm (value_to_inTm 0 (big_step_eval_exTm testmegasucc []))))

  *)
