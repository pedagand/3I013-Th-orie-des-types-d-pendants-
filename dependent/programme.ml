open Lambda

(* to run in top level
#use "topfind";;
#require "sexplib";;
#require "oUnit";; 
*)
  
let refl = "(lambda (A a b q) (trans A (lambda (a b c) (id A b a)) a b q (refl a)))"
let type_refl = "(pi A * (pi a A (pi b A (-> (id A a b) (id A b a)))))" 

let () = run_check refl type_refl

let 



  (* ancienne version 
let refl = "(lambda (A a b q) (trans A (lambda (a b) (id A b a)) a b q (lambda a (refl a))))"
let type_refl = "(pi A * (pi a A (pi b A (-> (id A a b) (id A b a)))))" 
  *)
