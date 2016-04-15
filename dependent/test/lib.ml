open OUnit2
open Sexplib
open Lambda



let inputs =   
[
  (* ((read "(+ (succ (succ zero)) (succ (succ zero)))"),Nat,true); *)
]


(* let () = Printf.printf "%s" (pretty_print_inTm (value_to_inTm 0 (big_step_eval_inTm (read "(iter (lambda x N) (succ (succ zero)) (lambda n (lambda x(succ x))) zero)") [])) []) *)

(* let () = Printf.printf "%s" (pretty_print_inTm (read "(iter (lambda x N) (succ (succ zero)) (lambda n (lambda x (succ x))) zero)")[]) 

let x = (big_step_eval_inTm (read "(iter (lambda x N) (succ (succ zero)) (lambda n (lambda x (succ x))) zero)") []) *)

(* let () = Printf.printf "%s" (pretty_print_inTm (value_to_inTm 0 (big_step_eval_inTm ((read "(+ (succ (succ zero)) (succ (succ zero)))")) [])) []) *)
(* let () = Printf.printf "%s" (pretty_print_inTm (read "(+ (succ (succ zero)) (succ (succ zero)))") []) *)

let tests = List.map (fun (term,chek, res) -> (pretty_print_inTm term []) >:: fun ctxt -> assert_equal (res_debug(check [] term (big_step_eval_inTm chek []) "")) res) inputs 
