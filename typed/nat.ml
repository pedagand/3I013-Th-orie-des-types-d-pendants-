open Lambda

(** * Les entiers de church *)
let zero = Abs("x",Abs("y",Inv(BVar 0)))
let succ = Abs("n",Abs("f",Abs("x",Inv(Appl(BVar 1,(Inv(Appl(Appl(BVar 2,Inv(BVar 1)),Inv(BVar 0)))))))))


(* Fonctions de manipulation *)
(* a refaire quand j'aurais l'évaluation de l'itération qui marche *)
let rec int_to_value i = 
  match i with 
  | 0 -> big_step_eval_exTm (Appl(Ann(succ,(Fleche(Nat,Fleche(Nat,Nat)))),zero)) [] 
  | i -> big_step_eval_exTm (Appl(Ann(succ,(Fleche(Nat,Fleche(Nat,Nat)))),(value_to_inTm 0 (int_to_value (i-1))))) []

  
  
		       

(* Défintions des termes *)

let testsucc = Appl(Ann(succ,Nat),zero)
let testmegasucc = Appl(Ann(succ,Nat),Inv(Appl(Ann(succ,Nat),Inv(Appl(Ann(succ,Nat),zero)))))
let lzero = SAbs(SAbs(SBVar 0))
let lsucc = SAbs(SAbs(SAbs(SAppl(SBVar 1,SAppl(SAppl(SBVar 2,SBVar 1),SBVar 0)))))


