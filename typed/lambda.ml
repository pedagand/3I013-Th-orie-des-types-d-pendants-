open Sexplib

(*=name *)
type name =
  | Global of string 
  | Bound of int 
  | Quote of int
(*=End *)

(*=Type *)
type typ = 
  | Bool
  | Nat 
  | Fleche of typ * typ
  | Croix of typ * typ 
  | List of typ

  (*=End *)
		     
(* Correspondance avec le papier 
Abs = Lam
Inf = Inv *)

(*=inTm *)
type inTm = 
  | Abs of name * inTm
  | Inv of exTm
(*=End *)
  | True | False 
  | Zero 
  | Succ of inTm
(*=inTm_pair *)
  | Pair of inTm * inTm 
(*=End *)
  | Nil of typ
  | Cons of typ * inTm * inTm 
(*=exTm *)
and exTm = 
  | FVar of name
  | BVar of int
  | Appl of exTm * inTm
(*=End *)
  | Ifte of inTm * exTm * exTm
  | Ann of inTm * typ
  | Iter of inTm * inTm * exTm
(*=exTm_pair *) 
  | P0 of exTm
  | P1 of exTm 
(*=End *)
  | Fold of inTm * inTm * inTm * inTm 

type lambda_term =
  | SFVar of string 
  | SBVar of int 
  | SAbs of lambda_term
  | SAppl of (lambda_term * lambda_term)
  | STrue | SFalse | SIfte of lambda_term * lambda_term * lambda_term
  | SZero | SSucc of lambda_term | SIter of lambda_term * lambda_term * lambda_term
  | SPair of lambda_term * lambda_term 
  | SP0 of lambda_term 
  | SP1 of lambda_term

(*=value *)
type value = 
  | VLam of (value -> value)
  | VNeutral of neutral 
(*=End *)
  | VTrue 
  | VFalse
  | VSucc of value
  | VZero
(*=value_pair *)
  | VPair of value * value 
(*=End *)
(*=neutral *)
and neutral = 
  | NFree of name
  | NApp of neutral * value 
(*=End *)




let rec typ_to_string t = 
  match t with 
  | Bool -> "B"
  | Nat -> "N"
  | Fleche(x,y) -> typ_to_string x ^ "->" ^ typ_to_string y
  | Croix(x,y) -> "(" ^ typ_to_string x ^ " X " ^ typ_to_string y ^ ")"
  | List(x) -> "(list "^ typ_to_string x ^ ")"


let rec parse_term env t = 
      match t with   
      | Sexp.List [Sexp.Atom "lambda"; Sexp.Atom var; body] -> 
	 Abs(Global(var),(parse_term ((Global(var))::env) body)) 
      | Sexp.List [Sexp.Atom "lambda"; Sexp.List vars ; body] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser: invalid variable") vars
	 in 
	 List.fold_right 
           (fun var b -> Abs(var,b))
           (List.map (fun x -> Global(x)) vars)
           (parse_term (List.append (List.rev ((List.map (fun x -> Global(x)) vars))) env) body)      
      | Sexp.Atom "zero" -> Zero
      | Sexp.Atom "true" -> True 
      | Sexp.Atom "false" -> False 
      | Sexp.List [Sexp.Atom "succ"; n] ->
	 Succ(parse_term env n)
      | Sexp.List [Sexp.Atom "nil"; a] ->
	 Nil(parse_type env a)
      | Sexp.List [Sexp.Atom "cons";t;a;b] ->
	 Cons((parse_type env t),(parse_term env a),(parse_term env b))
      | Sexp.List [Sexp.Atom ",";x;y] ->
	 Pair((parse_term env x),(parse_term env y))
      | _ -> Inv(parse_exTm env t)
and parse_exTm env t = 
  let rec lookup_var env n v
    = match env with
    | [] -> FVar v
        | w :: env when v = w -> BVar n
        | _ :: env -> lookup_var env (n+1) v 
  in
  match t with 
  | Sexp.List [Sexp.Atom "p0";x] ->
     P0(parse_exTm env x)
  | Sexp.List [Sexp.Atom "p1";x] ->
     P1(parse_exTm env x)
  | Sexp.List [Sexp.Atom "ifte"; b ; thens ; elses ] -> 
     Ifte((parse_term env b),(parse_exTm env thens),(parse_exTm env elses))
  | Sexp.List [Sexp.Atom ":" ;x; t] -> 
     Ann((parse_term env x),(parse_type [] t))
  | Sexp.Atom v -> lookup_var env 0 (Global(v)) 
  | Sexp.List [Sexp.Atom "iter"; n ; f ; a] -> 
     Iter((parse_term env n),(parse_term env f),(parse_exTm env a))
  | Sexp.List [Sexp.Atom "fold";a;b;c;d] ->
     Fold((parse_term env a),(parse_term env b),(parse_term env c),(parse_term env d))
  | Sexp.List (f::args) -> 
     List.fold_left 
       (fun x y -> Appl(x, y))
       (parse_exTm env f)
       (List.map (parse_term env) args)
  | _ -> failwith "erreur de parsing(exTm)" 
and  parse_type env t = 
  match t with 
  | Sexp.Atom "B" -> Bool
  | Sexp.Atom "N" -> Nat 
  | Sexp.List [Sexp.Atom "*" ; x ; y] ->
     Croix((parse_type [] x),(parse_type[] y))
  | Sexp.List [Sexp.Atom "->"; x ;y] ->
     Fleche((parse_type [] x),(parse_type [] y)) 
  | Sexp.List [Sexp.Atom "list";x] ->
     List(parse_type [] x)
  | _ -> failwith "erreur dans le parsing (type)" 


let read t = parse_term [] (Sexp.of_string t)
let read_type t = parse_type [] (Sexp.of_string t)
					     		 	
let rec pretty_print_inTm t l = 
  match t with 
  | Abs (Global(x),y) -> "(lambda " ^ x ^ " " ^ pretty_print_inTm y (x :: l) ^ ")"
  | Abs(_,x) -> failwith "Pretty print Abs first arg must be a global"
  | Inv x -> pretty_print_exTm x l
  | True -> "true"
  | False -> "false"
  | Zero -> "zero"
  | Succ x -> "(succ " ^ pretty_print_inTm x l ^ ")"
  | Pair (x,y) -> "(, " ^ pretty_print_inTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | Nil x -> "(nil " ^ pretty_print_type x l ^ ")"
  | Cons(a,x,y) -> "(cons " ^ pretty_print_type a l ^ " " ^ pretty_print_inTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
and pretty_print_exTm t l =
  match t with 
  | FVar (Global x) -> x 
  | FVar (Quote x) -> string_of_int x 
  | FVar (Bound x) -> string_of_int x
  | BVar x -> List.nth l x	      
  | Appl(x,y) -> "( " ^ pretty_print_exTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | Ann(x,y) -> "(: " ^ pretty_print_inTm x l ^ " " ^ pretty_print_type y l ^ ")"
  | Ifte(x,y,z) -> "(ifte " ^ pretty_print_inTm x l ^ " " ^ pretty_print_exTm y l ^ " " ^ pretty_print_exTm z l ^  ")"
  | Iter(n,f,a) -> "(iter " ^ pretty_print_inTm n l ^ " " ^ pretty_print_inTm f l ^ " " ^  pretty_print_exTm a l ^ ")"
  | P0(x) -> "(p0 " ^ pretty_print_exTm x l ^ ")"
  | P1(x) -> "(p1 " ^ pretty_print_exTm x l ^ ")"
  | Fold(a,b,c,d) -> "(fold " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm b l ^ " "^ pretty_print_inTm c l ^ " "^ pretty_print_inTm d l ^ ")" 
and pretty_print_type t l = 
  match t with 
  | Bool -> "B"
  | Nat -> "N"
  | Fleche(x,y) -> "(-> " ^ pretty_print_type x l ^ " " ^ pretty_print_type y l ^ ")" 
  | Croix(x,y) ->  "(* " ^ pretty_print_type x l ^ " " ^ pretty_print_type y l ^ ")" 
  | List(a) -> "(list " ^ pretty_print_type a l ^ ")"
    

let rec lambda_term_to_string t = 
  match t with
  | SFVar v -> v
  | SBVar v -> string_of_int v        
  | SAbs x -> "[]." ^ lambda_term_to_string x 
  | SAppl (x,y) -> "(" ^ lambda_term_to_string x ^ " " ^ lambda_term_to_string y ^ ")"
  | STrue -> "True"
  | SFalse -> "False"
  | SIfte (x,y,z) -> "if " ^ lambda_term_to_string x ^ " then " ^ lambda_term_to_string y ^ " else " ^ lambda_term_to_string z 
  | SZero -> "Zero"
  | SSucc x -> "Succ( " ^ lambda_term_to_string x ^ ")" 
  | SIter(n,f,a) -> "(Iter " ^ lambda_term_to_string n ^ lambda_term_to_string f ^  lambda_term_to_string a ^ ")"
  | SPair(x,y) -> "(" ^ lambda_term_to_string x ^ "," ^ lambda_term_to_string y ^ ")"
  | SP0(x) -> "(SP0" ^ lambda_term_to_string x ^ ")"
  | SP1(x) -> "(SP1" ^ lambda_term_to_string x ^ ")"

(*=vfree *)
let vfree name = VNeutral(NFree name)
(*=End *)

let gensym2 =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c

(*=boundfree *)
let boundfree i n = 
  match n with 
  | Quote k -> BVar (i - k - 1)
  | x -> FVar x  
(*=End *)
(*=value_to_inTm *)
let rec value_to_inTm i v =
  match v with 
  | VLam(f) -> let var = gensym2 () in 
	       begin 
		 Abs(Global(var),(value_to_inTm (i+1) (f(vfree(Quote i)))))
	       end 
  | VNeutral(x) -> Inv(neutral_to_exTm i x)
(*=End *)
  | VSucc(n) -> Succ(value_to_inTm i n)
  | VZero -> Zero 
  | VTrue -> True 
  | VFalse -> False 
  | VPair(x,y) -> Pair((value_to_inTm i x),(value_to_inTm i y)) 
(*=neutral_to_exTm *)
and neutral_to_exTm i v = 
  match v with 
  | NFree x -> boundfree i x	       	       
  | NApp(n,x) -> Appl((neutral_to_exTm i n),(value_to_inTm i x))
(*=End *)
		     

let rec substitution_inTm t tsub var = 
  match t with 
  | Inv x -> Inv(substitution_exTm x tsub var)
  | Abs(x,y) -> Abs(x,(substitution_inTm y tsub (var+1)))
  | True -> True
  | False -> False 
  | Zero -> Zero
  | Succ x -> Succ(substitution_inTm x tsub var)
  | Pair(x,y) -> Pair((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  | Nil(a) -> Nil(a)
  | Cons(a,x,y) -> Cons(a,(substitution_inTm x tsub var),(substitution_inTm y tsub var))
and substitution_exTm  t tsub var = 
  match t with 
  | FVar x -> FVar x
  | BVar x when x = var -> tsub
  | BVar x -> BVar x
  | Appl(x,y) -> Appl((substitution_exTm x tsub var),(substitution_inTm y tsub var))
  | Ann(x,y) -> Ann((substitution_inTm x tsub var),y)
  | Ifte(x,y,z) -> Ifte((substitution_inTm x tsub var),(substitution_exTm y tsub var),(substitution_exTm z tsub var))
  | Iter(n,f,a) -> Iter((substitution_inTm n tsub var),(substitution_inTm f tsub var),(substitution_exTm a tsub var))
  | P0(x) -> P0(substitution_exTm x tsub var)
  | P1(x) -> P1(substitution_exTm x tsub var)
  | Fold(a,b,c,d) -> Fold((substitution_inTm a tsub var),(substitution_inTm b tsub var),(substitution_inTm c tsub var),(substitution_inTm d tsub var))


let rec substitution t var tsub 
    = match t with 
    | SFVar v -> SFVar v 
    | SBVar v when v = var -> tsub
    | SBVar v -> SBVar v
    | SAbs x -> SAbs(substitution x (var+1) tsub)
    | SAppl (x,y) -> SAppl(substitution x var tsub,substitution y var tsub)
    | STrue -> STrue
    | SFalse -> SFalse
    | SIfte (x,y,z) -> SIfte((substitution x var tsub),(substitution y var tsub),(substitution z var tsub))
    | SZero -> SZero
    | SSucc x -> SSucc(substitution x var tsub)
    | SIter (n,f,a) -> SIter((substitution n var tsub),(substitution f var tsub),(substitution a var tsub))
    | SPair(x,y) -> SPair((substitution x var tsub),(substitution y var tsub))
    | SP0(x) -> SP0(substitution x var tsub)
    | SP1(x) -> SP1(substitution x var tsub)

let rec relie_libre i bv t =
  match t with 
  | SBVar v -> SBVar v
  | SFVar  v when v = string_of_int i -> SBVar bv
  | SFVar  v -> SFVar  v
  | SAbs(x) -> SAbs(relie_libre i (bv + 1) x)
  | SAppl(x,y) -> SAppl(relie_libre i bv x,relie_libre i bv y)
  | STrue-> STrue
  | SFalse -> SFalse
  | SIfte(x,y,z) -> SIfte((relie_libre i bv x),(relie_libre i bv y),(relie_libre i bv z))
  | SZero -> SZero
  | SSucc x -> SSucc(relie_libre i bv x)
  | SIter (n,f,a) -> SIter((relie_libre i bv n),(relie_libre i bv f),(relie_libre i bv a))
  | SPair (x,y) -> SPair((relie_libre i bv x),(relie_libre i bv y ))
  | SP0(x) -> SP0(relie_libre i bv x)
  | SP1(x) -> SP1(relie_libre i bv x)

(*=relie_libre_inTm *)
let rec relie_libre_inTm i bv t = 
  match t with 
  | Abs(x,y) -> Abs(x,(relie_libre_inTm i (bv + 1) y))
  | Inv(x) -> Inv(relie_libre_exTm i bv x)
(*=End *)
  | True -> True
  | False -> False 
  | Zero -> Zero 
  | Succ(x) -> Succ(relie_libre_inTm i bv x)
  | Pair(x,y) -> Pair((relie_libre_inTm i bv x),(relie_libre_inTm i bv y))
(*=relie_libre_exTm *)
  | Nil(a) -> Nil(a) 
  | Cons(a,x,y) -> Cons(a,(relie_libre_inTm i bv x),(relie_libre_inTm i bv y))
and relie_libre_exTm  i bv t = 
  match t with 
  | BVar v -> BVar v 
  | FVar (Global v) when v = string_of_int i -> BVar bv
  | FVar v -> FVar v 
  | Appl(x,y) -> Appl((relie_libre_exTm i bv x),(relie_libre_inTm i bv y))
(*=End*)
  | Ifte(x,y,z) -> Ifte((relie_libre_inTm i bv x),(relie_libre_exTm i bv y),(relie_libre_exTm i bv z))
  | Ann(x,y) -> Ann((relie_libre_inTm i bv x),y)
  | P0(x) -> P0(relie_libre_exTm i bv x)
  | P1(x) -> P1(relie_libre_exTm i bv x)
  | Iter(n,f,a) -> Iter((relie_libre_inTm i bv n),(relie_libre_inTm i bv f),(relie_libre_exTm i bv a))
  | Fold(a,b,c,d) -> Fold((relie_libre_inTm i bv a),(relie_libre_inTm i bv b),(relie_libre_inTm i bv c),(relie_libre_inTm i bv d))



(*=reduction_forte *)
let rec reduction_forte t i  = 
  match t with 
    | SFVar  v -> SFVar  v
    | SBVar v -> SBVar v
    | SAbs x -> SAbs(relie_libre i 0 (reduction_forte (substitution x 0 (SFVar  (string_of_int i))) (i+1)))
    | SAppl(SAbs(x),y) -> reduction_forte(substitution x 0 y) i
    | SAppl(x,y) -> 
       begin 
	 match reduction_forte x i with 
	 | SFVar z -> SAppl(x,(reduction_forte y i))
	 | SAbs z -> reduction_forte (SAppl(SAbs(z),y)) i 
	 | autre -> SAppl(autre,reduction_forte y i)			        
       end 
(*=End *)
    | STrue -> STrue
    | SFalse -> SFalse
    | SIfte (x,y,z) when x = STrue -> reduction_forte y i
    | SIfte (x,y,z) when x = SFalse -> reduction_forte z i
    | SIfte (x,y,z) -> 
       begin 
	 match reduction_forte x i with
	 | STrue-> reduction_forte y i
	 | SFalse -> reduction_forte z i
	 | _ -> SIfte(x,y,z)
       end  
    | SZero -> SZero
    | SSucc x -> SSucc x 
    | SIter(n,f,a) -> 
       begin 
	 match n with 
	 | SSucc x -> (reduction_forte (SIter(x,f,(reduction_forte (SAppl(f,a)) i))) i)
	 | SZero -> reduction_forte a i 
	 | _ -> SIter(n,f,a) 
       end 
    | SPair (x,y) -> SPair((reduction_forte x i),(reduction_forte y i))
    | SP0(x) -> 
       begin       
	 match (reduction_forte x i) with 
	 | SPair(x,y) -> reduction_forte x i
	 | _ -> SP0(reduction_forte x i)
      end
    | SP1(x) -> 
       begin       
	 match (reduction_forte x i) with 
	 | SPair(x,y) -> reduction_forte y i
	 | _ -> SP1(reduction_forte x i)
       end



	 

(*=big_step_eval_exTm_ann *)
let rec eval_exTm t envi = 
  match t with
    | Ann(x,_) -> eval_inTm x envi
(*=End *)
(*=big_step_eval_exTm_var *) 
    | FVar v -> vfree v 
    | BVar v -> List.nth envi v
(*=End *)
(*=big_step_eval_exTm_app *)
    | Appl(x,y) -> vapp((eval_exTm x envi),(eval_inTm y envi))
(*=End *)
    | Iter(n,f,a) -> viter(eval_inTm n envi, 
                           eval_inTm f envi,
                           eval_exTm a envi)
    | Ifte(c,thens,elses) ->
       let cond  = eval_inTm c envi in
       begin 
	 match cond with 
	 | VTrue -> eval_exTm thens envi
	 | VFalse -> eval_exTm elses envi 
	 | _ -> failwith "Impossible" 
       end 
    | P0(x) ->
       begin 
       match eval_exTm x envi with  
	       | VPair(a,b) -> a
	       | _ -> failwith "Impossibl: P0 can't be applied to something else then a pair"
       end 
    | P1(x) ->
       begin 
       match eval_exTm x envi with  
	       | VPair(a,b) -> a
	       | _ -> failwith "Imposibl: P1 can't be applied to something else then a pair"
       end 				      
    | _ -> failwith "big_step a faire plus tard"
and viter (v, f,a) = 
  match v with
  | VZero ->  a
  | VSucc v -> vapp (f, (viter (v, f, a)))
  | _ -> failwith "Impossible (viter)"
(*=vapp *)
and vapp v = 
  match v with 
  | ((VLam f),v) -> f v
  | ((VNeutral n),v) -> VNeutral(NApp(n,v))
  | _ -> failwith "Impossible (vapp)"
(*=End *)
(*=big_step_eval_inTm_inv *)
and eval_inTm t envi = 
  match t with 
  | Inv(i) -> eval_exTm i envi
(*=End *)
(*=big_step_eval_inTm_abs *)
  | Abs(x,y) -> VLam(function arg -> (eval_inTm y (arg :: envi)))
(*=End *)
  | Zero -> VZero
  | Succ n -> VSucc (eval_inTm n envi)
  | Pair(x,y) -> VPair((eval_inTm x envi),(eval_inTm y envi))
  | True -> VTrue 
  | False -> VFalse
  | _ -> failwith "a faire plus tard big_step"


let gensym =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c
let rec value_to_inTm i v =
  match v with 
  | VLam f -> let freshVar = gensym() in
	      Abs(Global(freshVar),value_to_inTm (i+1) (f (vfree(Quote i))))
  | VNeutral n -> Inv(neutral_to_exTm i n)
  | VTrue -> True
  | VFalse -> False
  | VSucc x -> Succ(value_to_inTm i x)
  | VZero -> Zero
  | VPair(x,y) -> Pair((value_to_inTm i x),(value_to_inTm i y))
and neutral_to_exTm i v = 
  match v with 
  | NFree x -> boundfree i x
  | NApp(n,x) -> Appl((neutral_to_exTm i n),(value_to_inTm i x))


let rec equal_inTm t_un t_deux =
  match (t_un,t_deux) with
  | (Abs(_,x1),Abs(_,x2)) -> equal_inTm x1 x2
  | (Inv(x1),Inv(x2)) -> equal_exTm x1 x2
  | (True,True) -> true
  | (False,False) -> true
  | (Zero,Zero) -> true
  | (Succ(x1),Succ(x2)) -> equal_inTm x1 x2
  | (Pair(x1,y1),Pair(x2,y2)) -> equal_inTm x1 x2 && equal_inTm y1 y2
  | _ -> false
and equal_exTm t_un t_deux =
  match (t_un,t_deux) with
  | (Appl(x1,y1),Appl(x2,y2)) -> equal_exTm x1 x2 && equal_inTm y1 y2
  | (FVar(x1),FVar(x2)) -> x1 = x2
  | (BVar(x1),BVar(x2)) -> x1 = x2
  | (Ann(x1,_),Ann(x2,_)) -> equal_inTm x1 x2
  | (Ifte(x1,y1,z1),Ifte(x2,y2,z2)) -> equal_inTm x1 x2 &&
     equal_exTm y1 y2 && equal_exTm z1 z2
  | (Iter(x1,y1,z1),Iter(x2,y2,z2)) -> equal_inTm x1 x2 &&
     equal_inTm y1 y2 && equal_exTm z1 z2
  | (P0(x1),P0(x2)) -> equal_exTm x1 x2
  | (P1(x1),P1(x2)) -> equal_exTm x1 x2
  | _ -> false
     
     

	       
let rec typed_to_simple_inTm t = 
  match t with 
    | Abs(x,y) -> SAbs (typed_to_simple_inTm y)
    | Inv(x) -> typed_to_simple_exTm x
    | True-> STrue
    | False -> SFalse
    | Zero -> SZero
    | Succ x -> SSucc (typed_to_simple_inTm x)
    | Pair(x,y) -> SPair((typed_to_simple_inTm x),(typed_to_simple_inTm y))
    | _ -> failwith "typed to simple later"
and typed_to_simple_exTm t = 
  match t with 
    | BVar x -> SBVar x 
    | FVar (Global x) -> SFVar x
    | FVar x -> failwith "not possible at this time" 
    | Appl(x,y) -> SAppl((typed_to_simple_exTm x),(typed_to_simple_inTm y))
    | Ann(x,y) -> typed_to_simple_inTm x 
    | Ifte(x,y,z) -> SIfte((typed_to_simple_inTm x),(typed_to_simple_exTm y),(typed_to_simple_exTm z))
    | Iter(n,f,a) -> SIter((typed_to_simple_inTm n),(typed_to_simple_inTm f),(typed_to_simple_exTm a))
    | P0(x) -> SP0(typed_to_simple_exTm x)
    | P1(x) -> SP1(typed_to_simple_exTm x)
    | _ -> failwith "typed to simple later"


       
(*=check_def *)       
let rec check contexte ty inT 
    = match inT with
(*=End *)
(*=check_abs *)
    | Abs(x, b) -> 
       begin
         match ty with
         | Fleche(s, t) -> 
            let freshVar = gensym () in
            check ((Global(freshVar), s) :: contexte) t
	      (substitution_inTm b (FVar (Global(freshVar))) 0) 
         | _ -> failwith "SAbstraction forced into a non-functional type"
       end
(*=End *)
(*=check_inv *)
    | Inv(t) -> ty = synth contexte t
(*=End *)
(*=inTm_extensions *)
    | True -> if ty = Bool then true else false
    | False -> if ty = Bool then true else false
    | Zero -> if ty = Nat then true else false 
    | Succ x -> if ty = Nat then check contexte Nat x else false
(*=End *)
(*=check_pair *)
    | Pair(x,y) -> 
       begin 
	 match ty with 
	 | Croix(a,b) -> if check contexte a x
                            && check contexte b y then true
			 else failwith "In Pair(x,y) x is not of type a"				  
	 | _ -> failwith "Type of a pair must be a Croix"
       end 
(*=End *)
    | Nil(a) -> 
       begin 
	 match ty with 
	 | List(alpha) -> if alpha = a then true else false
	 | _ -> failwith "nil must be of type List"
       end
    | Cons(alpha,a,xs) -> 
       begin 
	 match ty with 
	   | List(alpha_typ) -> if alpha = alpha_typ &&
				     check contexte alpha a &&
				       check contexte xs ty
				then true 
				else failwith "cons not good"
	   | _ -> failwith "cons must be of type List"
       end 
(*=synth_def *)
and synth contexte exT 
    = match exT with
(*=End *)
(*=synth_ann *)
    | Ann(tm, ty) ->
       if check contexte ty tm then ty 
       else failwith "Wrong annotation"
(*=End *)
(*=synth_var *)
    | FVar(x) -> List.assoc x contexte
(*=End *)
    | BVar x -> failwith "Bvar is not possible at this moment"
(*=synth_appl *)
    | Appl(f, s) -> 
       let fTy = synth contexte f in
       begin
         match fTy with
         | Fleche(a, b) -> 
            if check contexte a s then b
            else failwith "Argument type invalid"
         | _ -> failwith "Function type invalid"
       end
(*=End *)
(*=exTm_extensions *)
    | Ifte(x,y,z) -> if check contexte Bool x then 
		       begin 
			 let ttrue = synth contexte y in 
			 let tfalse = synth contexte z in 
			 if ttrue = tfalse then ttrue 
			 else failwith "Ifte type of argument not the same"
		       end 
		     else failwith "Ifte first param need to be a bool"
    | Iter(n,f,a) -> if check contexte Nat n then
		       begin 
			 let type_a = synth contexte a in 
			 if check contexte (Fleche (type_a,type_a)) f
			 then type_a
			 else failwith "Iter 2nd arg must be of type_a -> type_a"
		       end 
		     else failwith "Iter first arg must be a Nat"
(*=End *)
(*=synth_pair *)
    | P0(x) -> 
       begin 
	 match synth contexte x with 
	 | Croix(a,b) -> a
	 | _ -> failwith "Po must be applied to a pair" 	   
       end 
    | P1(x) -> 
       begin 
	 match synth contexte x with 
	 | Croix(a,b) -> b
	 | _ -> failwith "P1 must be applied to a pair" 	   
       end 
(*=End *)
    | Fold(a,b,c,d) -> 
	
		     
let run_check terme typ =
  let res_check = check [] (read_type typ) (read terme) in
  let () = Printf.printf "%b" (res_check) in
  true
  
  




