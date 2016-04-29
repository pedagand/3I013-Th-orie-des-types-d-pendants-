open Lambda

(* to run in top level
#use "topfind";;
#require "sexplib";;
#require "oUnit";; 
*)
  
let sym = "(lambda (A a b q) (trans A (lambda (a b c) (id A b a)) a b q (lambda a (refl a))))"
let type_sym = "(pi A * (pi a A (pi b A (-> (id A a b) (id A b a)))))" 

let () = run_check sym type_sym

let concat = "(lambda (A m xs n ys) (dfold A (lambda mp (lambda vp (vec A (+ mp n)))) m xs (lambda nf (lambda vecun (lambda a (lambda xsf (dcons a xsf))))) ys))"
let type_concat = "(pi A * (pi m N (pi xs (vec A m) (pi n N (pi ys (vec A n) (vec A (+ n m)))))))"

(* let () = run_check concat type_concat *)


  (* ancienne version 
let refl = "(lambda (A a b q) (trans A (lambda (a b) (id A b a)) a b q (lambda a (refl a))))"
let type_refl = "(pi A * (pi a A (pi b A (-> (id A a b) (id A b a)))))" 
  *)
