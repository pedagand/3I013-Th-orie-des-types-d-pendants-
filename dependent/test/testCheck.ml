open OUnit2
open Sexplib
open Lambda

let test1y = "(pi A * (pi B (pi x A *) (pi C (pi x A *) (pi 1 (pi 2 (pi a A (pi b (B a) (C a))) (pi a A (B a))) (pi a A (C a))))))"

let testcheck3x = "(pi A * (pi B (pi x A *) *))"    

let testcheck4x = "(pi F (-> * *) (pi X * (-> (F X) *)))"   

let eq = "(lambda A (lambda a (lambda b (pi P (-> A *) (-> (P a) (P b))))))"


let inputs =   
  [    
    ("(lambda x x)","(-> * *)",true);  
    ("(lambda x x)","(-> (-> * *) *)",false); 
    ("(pi x * *)","*",true);
    ("(lambda x (x y))","(-> * *)",false);
    ("(lambda x (lambda y y))","(-> * (-> * *))",true);
    ("(((: (lambda x (lambda y (y x))) (-> * (-> (-> * *) *))) N) (lambda z z))","*",true);
    
    ("(lambda x (lambda y (y x)))","(-> * (-> (-> * *) *))",true);
    ("(lambda x (lambda y (x y)))","(-> * (-> (-> * *) *))",false);
    ("(lambda x (lambda y x))","(-> * (-> (-> * *) *))",true); 
    ("(: (lambda x (lambda y y)) (-> * (-> * *)))","(-> * (-> * *))",true);
    ("(pi x * *)","N",false); 
    ("((: (lambda x x) (-> (-> * (-> * *)) (-> * (-> * *)))) (lambda (x y) x))","(-> * (-> * *))",true); (*
    ("(:(lambda x (succ x)) (-> N N))","(-> N N)",true);
    ("((: (lambda x (succ x)) (-> N N)) zero)","N",true); 
    ("((: (lambda x (succ x)) (-> * *)) zero)","N",false); 
    ("(-> * *)","*",true); *)
    ("(pi A * (pi B (pi x A *) *))","*",true); 
    (eq, "(pi A * (-> A (-> A *)))",true); 
    (test1y,"*",true);
    ("zero","N",true);
    ("(succ zero)","N",true);
    ("(lambda x N)","(-> N *)",true);
    ("(iter (lambda x N) (succ (succ zero)) (lambda n (lambda x (succ x))) zero)","N",true); 
    (testcheck4x,"*",true); 
    ("(vec N (succ (succ zero)))","*",true);
    ("(dnil N)","(vec N zero)",true);			      
    ("(dnil zero)","(vec N zero)",false);
    ("(dcons zero (dnil N))","(vec N (succ zero))",true);	  
    ("(dcons zero (dcons zero (dnil N)))","(vec N (succ (succ zero)))",true);
								      ("(lambda x ?)","(-> * *)",false);								      
										   ("(id N zero (succ zero))","*",true);
   ("(refl zero)","(id N zero zero)",true);				
   ("(+ (succ (succ zero)) (succ (succ zero)))","N",true);
(*
    ("(list N)","*",true);
    ("(nil N)","(list N)",true);
    ("(cons N zero (nil N))","(list N)",true);
    ("(cons N zero (nil *))","(list N)",false);
    ("(cons * zero (nil N))","(list N)",false); *)  
  ]

    
let tests = List.map (fun (term,chek, res) -> term >:: fun ctxt -> assert_equal (res_debug(check [] (read term) (big_step_eval_inTm (read chek) []) "")) res) inputs 

