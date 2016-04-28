open OUnit2
open Sexplib
open Lambda


let inputs =
  [
    ("(lambda x x)","(lambda x x)");
  ]

let tests = List.map (fun (term,res) -> term >:: fun ctxt -> assert_equal
  (equal_inTm (value_to_inTm 0 (eval_inTm (read term) [])) (read res)) (true)) inputs     
