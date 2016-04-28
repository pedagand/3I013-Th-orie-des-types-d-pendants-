open OUnit2
open Sexplib
open Lambda


let inputs =
  [
    ("(lambda x x)","(-> N N)",true);
  ]

let tests = List.map (fun (term,chek, res) -> term >:: fun ctxt -> assert_equal (check [] (read_type chek) (read term)) res) inputs 
      
