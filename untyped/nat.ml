open Lambda

(** * Les entiers de church *)

(* Fonctions de manipulation *)

(* XXX: build using the repeated application of 'succ' instead *)
let rec church_num n =
  match n with
  | 0 -> BoundVar 0
  | n -> Appl(BoundVar 1,(church_num (n-1)))
		       
let int_to_lambda_term n =
  Abs(Abs(church_num n))

(* XXX: kinda cheating. *)
let rec lambda_term_to_int t =
  match t with
  | BoundVar x -> 0
  | Abs(Abs(x)) -> 0 + (lambda_term_to_int x)
  | Appl(BoundVar x,y) -> 1 + (lambda_term_to_int y)
  | FreeVar y -> failwith " to_int FreeVar erreur"
  | Appl(x,y) -> failwith "to_int Appl erreur"
  | Abs(x) -> failwith "to_int Abs erreur"
  | _ -> failwith "erreur"

(* Défintions des termes *)

let zero = read "(lambda (f x) x)"
let succ = read "(lambda (n f x) (f (n f x)))"
let plus = read "(lambda (m n f x) (m f (n f x)))"

(* a mettre en test unitaires 
let () = Printf.printf "debut de nat.ml \n"

let () = Printf.printf "%d \n" (lambda_term_to_int(reduction_forte testsucc 0))		

let () = Printf.printf "%s \n" (lambda_term_to_string(plus_test))
let () = Printf.printf "%s \n" (lambda_term_to_string(reduction_forte plus_test 0)) 

let () = Printf.printf "petit test d'affichage des termes parser \n";
	 Printf.printf "%s \n " (lambda_term_to_string zero)
 *)
