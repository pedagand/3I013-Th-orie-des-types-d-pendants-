open OUnit2
open Sexplib
open Lambda
 


let inputs = 
[
  ("(lambda x x)","(lambda y y)",true);
  ("(pi x * *)","(pi y * *)",true);
  ("(pi x1 x2 x3)","(pi x1 x2 x3)",true);
  ("(pi x1 x3 x2)","(pi x1 x2 x3)",false); 
]
  
  
let tests = List.map (fun (term1,term2 ,res) -> "test" >:: fun ctxt -> assert_equal (equal_inTm (read term1) (read term2)) res) inputs
