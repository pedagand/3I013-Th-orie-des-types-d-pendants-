open Lambda

(* to run in top level
#use "topfind";;
#require "sexplib";;
#require "oUnit";;  
*)
  
let function_rapport = "(lambda x (lambda y (ifte y (: (succ x) N) (: x N))))" 
let type_function_rapport = "(-> N (-> B N))"

  
let res = check [] (read_type type_function_rapport) (read function_rapport)

  
(* let res = run_check function_rapport type_function_rapport *)

