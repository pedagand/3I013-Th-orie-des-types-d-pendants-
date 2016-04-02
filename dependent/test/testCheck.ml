open OUnit2
open Sexplib
open Lambda

let test1x = (Pi("A",Star,Pi("B",(Pi ("x", Inv(BVar 2),Star)),Pi("C",(Pi ("x", Inv(BVar 3),Star)), (Pi ("1",(Pi ("2", (Pi("a",Star,Pi("b",(Inv(Appl(BVar 5 ,Inv(BVar 1)))),Inv(Appl(BVar 4, Inv(BVar 1)))))),(Pi ("a",Inv(BVar 5),Inv(Appl(BVar 4,Inv(BVar 0))))))),(Pi ("a",Inv(BVar 4),Inv(Appl(BVar 2,Inv(BVar 0)))))))))))

let test1y = "(pi A * (pi B (pi x A *) (pi C (pi x A *) (pi 1 (pi 2 (pi a A (pi b (B a) (C a))) (pi a A (B a))) (pi a A (C a))))))"

let testcheck3x = "(pi A * (pi B (pi x A *) *))"    

let testcheck4x = "(pi F (-> * *) (pi X * (-> (F X) *)))"   


(* let testcheckPositive inputTerm inputType =
  assert_bool "Not type correct" (check [] (read inputTerm) inputType "" [])

let testcheckNegative inputTerm inputType =
  assert_bool "Unexpectedly type correct" (not (check [] (read inputTerm) inputType "" [])) *)


let inputs =   
  [
    
    ("(lambda x x)","(-> * *)",true);  
    ("(lambda x x)","(-> (-> * *) *)",false);
    ("(pi x * *)","*",true);
    ("(pi x * *)","N",false);
    ("((: (lambda x x) (-> (-> * (-> * *)) (-> * (-> * *)))) (lambda (x y) x))","(-> * (-> * *))",true);
    ("(:(lambda x (succ x)) (-> N N))","(-> N N)",true);
    ("((: (lambda x (succ x)) (-> N N)) zero)","N",true); 
    ("((: (lambda x (succ x)) (-> * *)) zero)","N",false); 
    ("(-> * *)","*",true);
    ("(pi A * (pi B (pi x A *) *))","*",true);
    ("(lambda A (lambda a (lambda b (pi P (-> A *) (-> (P a) (P b))))))",
     "(pi A * (-> A (-> A *)))",true); 
    (test1y,"*",true);
    ("(succ zero)","N",true);
    (testcheck4x,"*",true)
  ]

    
let tests = List.map (fun (term,chek, res) -> term >:: fun ctxt -> assert_equal (res_debug(check [] (read term) (read chek) "")) res) inputs 

