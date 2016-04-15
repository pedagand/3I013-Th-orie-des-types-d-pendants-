open Sexplib
open Lambda

(* ------------------------Termes-----------------------*)
let plus = big_step_eval_inTm (read ") []


(* ----------Fonctions sur les entiers pour appliquer les termes--------*)



let plus a b = 
  if res_debug(check [] a VNat "") && res_debug(check [] b VNat "")
  then 
  else failwith "Plus :args must be nat"

