open OUnit2
open Lambda 


(* -----------------------------test du type_checker----------------------  *)

let test_check1 test_ctxt = assert_equal 
			      (check [] (Abs("f",Abs("g",Inv(Appl(BVar 1,Inv(BVar 0)))))) (Fleche(Fleche(Bool,Bool),Fleche(Bool,Bool)))) 
			      (true)
let test_check2 test_ctxt = assert_equal 
			      (check [] (Inv(Appl(Ann(Abs("x",Inv(BVar 0)),Fleche(Fleche(Bool,Bool),Fleche(Bool,Bool))),(Abs("y",(Inv(BVar 0))))))) (Fleche(Bool,Bool)) ) 
			      (true)
let test_check3 test_ctxt = assert_equal 
			      (check [] (Inv(Iter(Succ(Zero),Abs("x",Inv(BVar 0)),Ann(Zero,Nat)))) Nat) 
			      (true) 
let test_check4 test_ctxt = assert_equal
			      (check [] (read "(ifte true (: (, true false) (* B B)) (: (, true false) (* B B)) )") (Croix(Bool,Bool)))
			      (true)
let test_check5 test_ctxt = assert_equal 
			      (check [] (read "(, (lambda x x) zero)") (Croix(Fleche(Nat,Nat),Nat)))
			      (true)



(* -------------------------test de reduction forte  -------------------------*)

let test_red_forte1 test_ctxt = assert_equal 
			(reduction_forte (SAppl(SAbs(SBVar 0),SAbs(SBVar 0)))  0 )
			(SAbs(SBVar 0))
let test_red_forte2 test_ctxt = assert_equal 
				  (reduction_forte (SIfte(STrue,(SP0(SPair(SZero,SSucc(SZero)))),SSucc(SSucc(SZero)) )) 0) 
				  (SZero)




(* -------------------------test de typed_to_simple_inTm  ------------------- *)

let test1_typed_to_simple test_ctxt = assert_equal 
			(typed_to_simple_inTm (Abs("x",Inv(Appl(BVar 0,Inv(FVar "0"))))))
			(SAbs(SAppl(SBVar 0,SFVar "0")))
let test2_typed_to_simple test_ctxt = assert_equal 
			(typed_to_simple_inTm (Inv(Appl(Ann(Abs("x",Inv(BVar 0)),Fleche(Fleche(Bool,Bool),Fleche(Bool,Bool))),(Abs("y",(Inv(BVar 0))))))))
			(SAppl(SAbs(SBVar 0),SAbs(SBVar 0)))

let test3_typed_to_simple test_ctxt =  
  assert_equal
    (typed_to_simple_inTm (Inv((P0(Ann(Pair(Succ(Zero),(Inv(Ifte(True,Ann(True,Bool),Ann(False,Bool))))),Croix(Nat,Bool)))))))
    (SP0(SPair(SSucc(SZero),SIfte(STrue,STrue,SFalse)))) 
    

(* --------------------test de substitution_inTm ---------------------------*)

(* le -1 pour la substitution pour dire que l'on veut substituter la bound var 0 car normallement on appelle cette fonction sans passer au travers du premier lambda *)
let test_sub_inTm1 text_ctxt = assert_equal 
			 (substitution_inTm (Abs("x",Inv(Appl(BVar 0,Inv(FVar "0"))))) (FVar "y") (-1))
			 ((Abs("x",Inv(Appl(FVar "y",Inv(FVar "0"))))))

let test_sub_inTm2 test_ctxt = assert_equal
			(substitution_inTm (Abs("x",Inv(Appl(BVar 0,Inv(FVar "0"))))) (Ann(Abs("y",Inv(BVar 0)),Fleche(Bool,Bool))) (-1))
			((Abs("x",Inv(Appl((Ann(Abs("y",Inv(BVar 0)),Fleche(Bool,Bool))),Inv(FVar "0")))))) 
let test_sub_inTm3 test_ctxt = assert_equal
				 (substitution_inTm (Inv(P0(Ann(Pair(Inv(BVar 0),Inv(BVar 0)),(Croix(Nat,Nat)))))) (FVar "x") 0)
				 (Inv(P0(Ann(Pair(Inv(FVar "x"),Inv(FVar "x")),Croix(Nat,Nat)))))
let test_sub_inTm4 test_ctxt = assert_equal
				 (substitution_inTm  (Inv(Ifte(True,BVar 0,BVar 0))) (FVar "x") 0 )
				 (Inv(Ifte(True,FVar "x",FVar "x"))) 


(* ------------------------test de pretty printing------------------------ *)

let test8 test_ctxt = assert_equal 
			(read(pretty_print_inTm (Inv(Appl(Ann(Abs("x",Inv(BVar 0)),Nat),Inv(FVar "y")))) []))
			(read "((: (lambda x x) N) y)")
let test9 test_ctxt = assert_equal 
			(read(pretty_print_inTm (Inv(Iter((Succ(Zero)),(Abs("x",Inv(BVar 0))),FVar "y")))  [] ))
			(read "(iter (succ zero) (lambda x x) y)")
let test10 test_ctxt = assert_equal 
			 (read(pretty_print_inTm (Inv(Appl(Ann(Abs("x",Inv(BVar 0)),Fleche(Fleche(Bool,Bool),Fleche(Bool,Bool))),(Abs("y",(Inv(BVar 0))))))) [] ))
			 (read "((: (lambda (x) (x)) (-> (-> B B) (-> B B))) (lambda (y) (y)))")
let test11 test_ctxt = assert_equal
			 (read(pretty_print_inTm (Abs("x",Abs("y",Abs("z",Inv(Appl(BVar 2, Inv(Appl(BVar 1, Inv(BVar 0))))))))) [] ))
			 (read "(lambda (x y z) (x (y z)))")
let test12 test_ctxt = assert_equal
			 (read(pretty_print_inTm (Pair(Abs("x",Inv(BVar 0)),Inv(FVar("y")))) [] ))
			 (read "(, (lambda x x) (y))") 
let test13 test_ctxt = assert_equal 
			 (read(pretty_print_inTm (Inv(Ann(Abs("x",Inv(BVar 0)),Croix(Bool,Bool)))) []))
			 (read "(: (lambda x x) (* B B))")
let test14 test_ctxt = assert_equal 
			 (read(pretty_print_inTm (Inv(Ifte(True,Ann((Pair(True,False)),(Croix(Bool,Bool))),FVar "y")))[] ))
			 (read "(ifte true (: (, true false) (* B B)) y)")

(* ------------------------------test de big step eval ---------------------- *)
(* trouver une solution pour comparer *)
(*
let test_big_step1 test_ctxt = assert_equal 
				 (value_to_inTm 0 (big_step_eval_exTm (Appl(Ann(Abs("x",Inv(BVar 0 )),(Fleche(Nat,Nat))),Abs("y",Inv(BVar 0)))) []))
				 (value_to_inTm 0 (VLam(function arg -> arg)))
let () = Printf.printf "%s" (pretty_print_inTm (value_to_inTm 0 (VLam(function arg -> arg)))  [] )
let () = Printf.printf "%s"(pretty_print_inTm (value_to_inTm 0 (big_step_eval_exTm (Appl(Ann(Abs("x",Inv(BVar 0 )),(Fleche(Nat,Nat))),Abs("y",Inv(BVar 0)))) []) ) [] ) *) 
(*
let test_red_forte1 test_ctxt = assert_equal 
			(reduction_forte (SAppl(SAbs(SBVar 0),SAbs(SBVar 0)))  0 )
			(SAbs(SBVar 0))
let test_red_forte2 test_ctxt = assert_equal 
				  (reduction_forte (SIfte(STrue,(SP0(SPair(SZero,SSucc(SZero)))),SSucc(SSucc(SZero)) )) 0) 
				  (SZero)
 *)




let eval = 
["test 1">:: test_check1;
 "test 2">:: test_check2;
 "test_check3">:: test_check3;
 "test_check4">:: test_check4;
 "test_check4">:: test_check4;
 "test_check5">:: test_check5;
 "test_red_forte1">:: test_red_forte1;
 "test_red_forte2">::test_red_forte2;
 "test1_typed_to_simple">:: test1_typed_to_simple;
 "test2_typed_to_simple">:: test2_typed_to_simple;
 "test3_typed_to_simple">:: test3_typed_to_simple;
 "test_sub_inTm1">:: test_sub_inTm1;
 "test_sub_inTm2">:: test_sub_inTm2;
 "test_sub_inTm3">::test_sub_inTm3;
 "test_sub_inTm4">::test_sub_inTm4;
 "test 8">:: test8;
 "test 9">:: test9;
 "test 10">:: test10;
 "test 11">:: test11;
 "test 12">:: test12;
 "test 13">:: test13;
 "test 14">:: test14;]
