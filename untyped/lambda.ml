open Sexplib

(*
  To load in the OCaml toplevel:
  
  #use "topfind";;
  #require "sexplib";;
 
*)

(*=untyped_term *)
type lambda_term =
  | FreeVar of string 
  | BoundVar of int 
  | Abs of lambda_term
  | Appl of (lambda_term * lambda_term)
(*=End *)
(*=bool_term *)
  | True | False 
  | IfThenElse of lambda_term * lambda_term * lambda_term
(*=End *)
(*=nat_term *)
  | Zero | Succ of lambda_term 
  | Iter of lambda_term * lambda_term * lambda_term
(*=End *)


(* TODO: remember the name of the abstractions, for pretty-printing *)
(* TODO: rajouter constructeur des vrais ect... *)

(** * A simple parser *)

let rec parse env t 
    = let rec lookup_var env n v
        = match env with
        | [] -> FreeVar v
        | w :: env when v = w -> BoundVar n
        | _ :: env -> lookup_var env (n+1) v 
      in
      match t with
      | Sexp.List [Sexp.Atom "if"; cond; thens ; elses ] -> 
	 IfThenElse((parse env cond),(parse env thens),(parse env elses))
      | Sexp.Atom "true" -> True 
      | Sexp.Atom "false" -> False
      | Sexp.Atom "zero" -> Zero
      | Sexp.List [Sexp.Atom "succ";n] -> Succ(parse env n)
      | Sexp.List [Sexp.Atom "iter";n;f;a] -> 
	 Iter((parse env n),(parse env f),(parse env a))
      | Sexp.List [Sexp.Atom "lambda"; Sexp.Atom var; body] -> 
         Abs (parse (var :: env) body)
      | Sexp.List [Sexp.Atom "lambda"; Sexp.List vars; body] -> 
         let vars = List.map (function 
           | Sexp.Atom v -> v
           | _ -> failwith "Parser: invalid variable") vars 
         in
         List.fold_right 
           (fun var b -> Abs b)
           vars
           (parse (List.append (List.rev vars) env) body)
      | Sexp.Atom v -> lookup_var env 0 v
      | Sexp.List (f :: args) -> 
         List.fold_left 
           (fun x y -> Appl (x, y))
           (parse env f) 
           (List.map (parse env) args)      
      | _ -> failwith "Parser: ill-formed input."

let read t = parse [] (Sexp.of_string t)

(** * A simple printer *)

(* TODO: print S-expression instead. *)


let gensym =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c



(* a tester*) 
let rec lambda_term_to_Sexpr t i = 
  match t with 
    | FreeVar v -> v 
    | BoundVar v -> string_of_int v 
    | Abs x -> 
       "(lambda (" ^ (string_of_int i) ^ ") " ^ lambda_term_to_Sexpr x (i+1)
    | Appl(x,y) -> 
       "(" ^ lambda_term_to_Sexpr x i  ^ " " ^ lambda_term_to_Sexpr y i ^ ")"
    | True -> "true"
    | False -> "false" 
    | IfThenElse (x,y,z) -> 
       "(if " ^ lambda_term_to_Sexpr x i ^ lambda_term_to_Sexpr x i ^ lambda_term_to_Sexpr x i ^ ")"
    | Zero -> "zero"
    | Succ n-> "(succ " ^ lambda_term_to_Sexpr n i ^ ")"
    | Iter(n,f,a) -> 
       "(iter " ^ lambda_term_to_Sexpr n i ^ lambda_term_to_Sexpr f i ^ lambda_term_to_Sexpr a i ^ ")"



let rec lambda_term_to_string t = 
  match t with
  | FreeVar v -> v
  | BoundVar v -> string_of_int v        
  | Abs x -> "[]." ^ lambda_term_to_string x 
  | Appl (x,y) -> "(" ^ lambda_term_to_string x ^ " " ^ lambda_term_to_string y ^ ")"
  | True -> "True"
  | False -> "False"
  | IfThenElse (x,y,z) -> "if " ^ lambda_term_to_string x ^ " then " ^ lambda_term_to_string y ^ " else " ^ lambda_term_to_string z 
  |_ ->  failwith "ne sert plus a rien de mettre cette fonction a jour" 

(** * Reduction *)

(*=substitution *)
let rec substitution term var tsub 
    = match term with 
    | FreeVar v -> FreeVar v 
    | BoundVar v when v = var -> tsub
    | BoundVar v -> BoundVar v
    | Abs x -> Abs(substitution x (var+1) tsub)
    | Appl (x,y) -> Appl(substitution x var tsub,substitution y var tsub)
(*=End *)
(*=bool_substitution *)
    | True -> True
    | False -> False
    | IfThenElse (x,y,z) -> 
       IfThenElse((substitution x var tsub),
		  (substitution y var tsub),
		  (substitution z var tsub))
(*=End *)
(*=nat_substitution *)
    | Zero -> Zero
    | Succ(n) -> Succ(substitution n var tsub)
    | Iter(n,f,a) -> Iter((substitution n var tsub),(substitution f var tsub),(substitution a var tsub))
(*=End *)



(* XXX: Unnecessarily complex: it is enough to compare the raw terms *)
let alpha_equiv terme1 terme2 = 
  lambda_term_to_string terme1 = lambda_term_to_string terme2

(*=reduction *)
let rec reduction t 
    = match t with
    | FreeVar v -> FreeVar v
    | BoundVar v -> BoundVar v
    | Abs x -> Abs(x)
    | Appl(Abs(x),y) -> substitution x 0 y
    | Appl(x,y) -> Appl(x,y)    
(*=End *)
(*=bool_reduction *)
    | True -> True
    | False -> False
    | IfThenElse(x,y,z) -> IfThenElse(x,y,z)
(*=End *)
(*=nat_reduction *)
    | Zero -> Zero 
    | Succ(n) -> Succ(n)
    | Iter(n,f,a) -> Iter(n,f,a)
(*=End *)


(*=evaluation *)
let rec evaluation t 
    = match t with 
    | FreeVar v -> FreeVar v 
    | BoundVar v -> BoundVar v 
    | Abs x -> Abs x
    | Appl(Abs(x),y) -> evaluation(reduction t)
    | Appl(BoundVar x,y) -> Appl(BoundVar x,y)
    | Appl(FreeVar x,y) -> Appl(FreeVar x,y)
    | Appl(x,y) -> evaluation(Appl(evaluation x, y))
(*=End *)
(*=bool_evaluation *)
    | True -> True
    | False -> False
    | IfThenElse (x,y,z) when x = True -> y
    | IfThenElse (x,y,z) when x = False -> z
    | IfThenElse (x,y,z) -> 
       evaluation((IfThenElse ((reduction x), y, z)))
(*=End *)
(*=nat_evaluation *)
    | Zero -> Zero 
    | Succ(n) -> Succ(n) 
    | Iter(n,f,a) -> 
       begin 
	 match n with 
	 | Zero -> a
	 | Succ(num) -> evaluation (Iter(num,f,evaluation(Appl(f,a))))
	 | _ -> Iter(n,f,a)
       end 
(*=End *)



let rec relie_libre i bv t =
  match t with 
  | BoundVar v -> BoundVar v
  | FreeVar v when v = string_of_int i -> BoundVar bv
  | FreeVar v -> FreeVar v
  | Abs(x) -> Abs(relie_libre i (bv + 1) x)
  | Appl(x,y) -> Appl(relie_libre i bv x,relie_libre i bv y)
  | True -> True
  | False -> False
  | IfThenElse(x,y,z) -> IfThenElse(x,y,z)
  | Zero -> Zero 
  | Succ(n) -> Succ(relie_libre i bv n)
  | Iter(n,f,a) -> Iter((relie_libre i bv n),(relie_libre i bv f),(relie_libre i bv a))
				   

(* on va pouvoir supprimer cette fonction normallement *)
let rec reduction_forte t i  = 
  match t with 
    | FreeVar v -> FreeVar v
    | BoundVar v -> BoundVar v
    | Abs x -> Abs(relie_libre i 0 (reduction_forte (substitution x 0 (FreeVar (string_of_int i))) (i+1)))
    | Appl(Abs(x),y) -> reduction_forte(substitution x 0 y) i
    | Appl(x,y) -> 
       begin 
	 match reduction_forte x i with 
	 | FreeVar z -> Appl(x,(reduction_forte y i))
	 | Abs z -> reduction_forte (Appl(Abs(z),y)) i 
	 | neutre -> Appl(neutre,reduction_forte y i)				   
       end 
    | True -> True
    | False -> False
    | IfThenElse (x,y,z) when x = True -> reduction_forte y i
    | IfThenElse (x,y,z) when x = False -> reduction_forte z i
    | IfThenElse (x,y,z) -> 
       begin 
	 match reduction_forte x i with
	 | True -> reduction_forte y i
	 | False -> reduction_forte z i
	 | _ -> IfThenElse(x,y,z)
       end 
    | _ -> failwith "on va la supprimer" 




	       








					      






