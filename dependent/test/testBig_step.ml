open OUnit2
open Sexplib
open Lambda


(* let () = 
  Printf.printf "%s" (pretty_print_inTm (value_to_inTm 0 (big_step_eval_inTm (read ("(iter (lambda x N) (succ (succ zero)) (lambda x (lambda y (succ x))) zero)")) [])) []) *)

let inputs = 
[
  ("((: (lambda x x) (-> N N)) y)","y");
  ("(iter P zero (lambda x (succ x)) zero)","zero");
  ("(iter P (succ (succ (succ zero))) (lambda x (succ x)) zero)","(succ (succ (succ zero)))"); 
  
]


let tests = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal (value_to_inTm 0 (big_step_eval_inTm (read term) [])) (read res)) inputs 
