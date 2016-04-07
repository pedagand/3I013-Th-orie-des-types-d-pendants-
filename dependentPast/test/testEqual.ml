open OUnit2
open Sexplib
open Lambda
 


let inputs = 
[
  ("(lambda x x)","(lambda y y)",true);
  ("(pi x * *)","(pi y * *)",true);
]

let tests = List.map (fun (term1,term2 ,res) -> "test" >:: fun ctxt -> assert_equal (equal_inTm (read term1) (read term2)) res) inputs
