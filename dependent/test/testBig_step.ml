open OUnit2
open Sexplib
open Lambda



let inputs = 
[
  ("((: (lambda x x) (-> N N)) y)","y");
  ("(iter P zero (lambda x (succ x)) zero)","zero");
  ("(iter P (succ (succ (succ zero))) (lambda n (lambda x (succ x))) zero)","(succ (succ (succ zero)))"); 
  ("(dfold N (lambda n (lambda xs N)) (succ (succ zero)) (dcons (succ zero) (dcons (succ (succ zero)) (dnil N))) (lambda n (lambda xs (lambda a (lambda x (+ a x))))) zero)","(succ (succ (succ zero)))");
  
]


let tests = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal (value_to_inTm 0 (big_step_eval_inTm (read term) [])) (read res)) inputs 
