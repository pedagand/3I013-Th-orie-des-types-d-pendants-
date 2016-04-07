open OUnit2
open Sexplib
open Lambda

let test1y = "(pi A * (pi B (pi x A *) (pi C (pi x A *) (pi 1 (pi 2 (pi a A (pi b (B a) (C a))) (pi a A (B a))) (pi a A (C a))))))"

let testcheck3x = "(pi A * (pi B (pi x A *) *))"    

let testcheck4x = "(pi F (-> * *) (pi X * (-> (F X) *)))"   


(* let testcheckPositive inputTerm inputType =
  assert_bool "Not type correct" (check [] (read inputTerm) inputType "" [])

let testcheckNegative inputTerm inputType =
  assert_bool "Unexpectedly type correct" (not (check [] (read inputTerm) inputType "" [])) *)

let eq = "(lambda A (lambda a (lambda b (pi P (-> A *) (-> (P a) (P b))))))"


let inputs =   
  [
    
    ("(lambda x x)","(-> * *)",true);  
    ("(lambda x x)","(-> (-> * *) *)",false); 
    ("(pi x * *)","*",true);
(*    ("(pi x * *)","N",false); *)
    ("((: (lambda x x) (-> (-> * (-> * *)) (-> * (-> * *)))) (lambda (x y) x))","(-> * (-> * *))",true); (*
    ("(:(lambda x (succ x)) (-> N N))","(-> N N)",true);
    ("((: (lambda x (succ x)) (-> N N)) zero)","N",true); 
    ("((: (lambda x (succ x)) (-> * *)) zero)","N",false); 
    ("(-> * *)","*",true); *)
    ("(pi A * (pi B (pi x A *) *))","*",true); 
    (eq, "(pi A * (-> A (-> A *)))",true); 
    (test1y,"*",true);
 (*   ("(succ zero)","N",true);
    (testcheck4x,"*",true);
    ("(list N)","*",true);
    ("(nil N)","(list N)",true);
    ("(cons N zero (nil N))","(list N)",true);
    ("(cons N zero (nil *))","(list N)",false);
    ("(cons * zero (nil N))","(list N)",false); *)
    

  ]

    
let tests = List.map (fun (term,chek, res) -> term >:: fun ctxt -> assert_equal (res_debug(check [] (read term) (big_step_eval_inTm (read chek) []) "")) res) inputs 

