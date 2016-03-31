open Lambda

(** * Les entiers de church *)

(* Fonctions de manipulation *)

		       

(* Défintions des termes *)

let zero = Abs("x",Abs("y",Inv(BVar 0)))
let succ = Abs("n",Abs("f",Abs("x",Inv(Appl(BVar 1,(Inv(Appl(Appl(BVar 2,Inv(BVar 1)),Inv(BVar 0)))))))))

(* let testsucc = Appl(Ann(succ,Nat),zero)
let testmegasucc = Appl(Ann(succ,Nat),Inv(Appl(Ann(succ,Nat),Inv(Appl(Ann(succ,Nat),zero))))) *)

