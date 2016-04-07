open Sexplib 


(* je garde la représentation que l'on avait de l'abstraction, avec la variable en string au début *)

type inTm = 
  | Abs of string * inTm
  | Inv of exTm
  | Pi of string * inTm * inTm 
  | Star
  | Zero
  | Succ of inTm
  | Nat
  | Pair of inTm * inTm 
  | Cross of inTm * inTm
  | List of inTm 
  | Nil of inTm 
  | Cons of inTm * inTm * inTm 
(*
  | Vec of inTm * inTm 
  | DNil of inTm 
  | DCons of inTm * inTm *)
and exTm = 
  | Ann of inTm * inTm 
  | BVar of int 
  | FVar of string 
  | Appl of exTm * inTm
  | Iter of inTm * inTm * inTm * inTm  
  | P0 of exTm
  | P1 of exTm 
type value = 
  | VLam of (value -> value)
  | VNeutral of neutral 
  | VStar 
  | VPi of value * (value -> value)
  | VSucc of value
  | VZero 
  | VNat
  | VPair of value * value
  | VCross of value * value
and neutral = 
  | NFree of string 
  | NApp of neutral * value 

type debug = 
  | Report of debug * debug * debug * debug
  | Success of bool
  | Contexte of string
  | Steps of string
  | Error of string
and debug_synth = 
  | RetSynth of debug * inTm

(* fonction pour les rapports d'erreurs *)
let create_report s c e er= 
  Report(Success(s),Contexte(c),Steps(e),Error(er))

let create_retSynth d inT = 
  RetSynth(d,inT)

let print_report r = 
  match r with 
  | Report(Success(s),Contexte(c),Steps(e),Error(er)) -> 
     "Report : \n -Success : " ^ string_of_bool s ^ "\n" ^
       "-Contexte : " ^ c ^ "\n" ^
	 "-Steps : " ^ e ^ "\n" ^
	   "-Error : " ^ er ^ "\n" 
  | _ -> failwith "can't print something which is not a report" 

let res_debug d = 
  match d with 
  | Report(Success(s),Contexte(c),Steps(e),Error(er)) -> 
     s
  | _ -> failwith "report don't have the good Shape" 


let res_debug_synth d = 
  match d with 
  | RetSynth(Report(Success(s),c,e,er),y) -> s 
  | _ -> failwith "RetSynth don't have a good shape"


let ret_debug_synth d = 
  match d with 
  | RetSynth(Report(Success(s),c,e,er),y) -> y 
  | _ -> failwith "RetSynth don't have a good shape"

(* ici on va crée le parseur lisp avec le pretty printing *)
let rec parse_term env t = 
      match t with   
      | Sexp.Atom "*" -> Star
      | Sexp.Atom "zero" -> Zero
      | Sexp.Atom "N" -> Nat 
      | Sexp.List [Sexp.Atom "succ"; n] -> 
	 Succ(parse_term env n)
      | Sexp.List [Sexp.Atom "lambda"; Sexp.Atom var; body] -> 
	 Abs(var,(parse_term (var::env) body)) 
      | Sexp.List [Sexp.Atom "lambda"; Sexp.List vars ; body] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser: Lambdainvalid variable") vars
	 in 
	 List.fold_right 
           (fun var b -> Abs(var,b))
           vars
           (parse_term (List.append (List.rev vars) env) body)      
      | Sexp.List [Sexp.Atom "->"; s ; t ] -> 
	 Pi("NO",(parse_term env s),(parse_term ("NO" :: env) t))
      | Sexp.List [Sexp.Atom "pi"; Sexp.Atom var ; s ; t] -> 
	 Pi(var,(parse_term env s),(parse_term (var::env) t))        
      | Sexp.List [Sexp.Atom "pi";Sexp.List vars; s; t] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser pi invalide variable") vars 
	 in 
	 List.fold_right
	   (fun var b -> Pi(var,(parse_term (List.append (List.rev vars) env) s),b))
	   vars 
	   (parse_term (List.append (List.rev vars) env) t)
      | Sexp.List [a;Sexp.Atom ",";b] -> 
	 Pair((parse_term env a),(parse_term env b))
      | Sexp.List [a;Sexp.Atom "X";b] -> 
	 Cross((parse_term env a),(parse_term env b))
      | Sexp.List [Sexp.Atom "list";alpha] -> 
	 List(parse_term env alpha)
      | Sexp.List [Sexp.Atom "nil";alpha] -> 
	 Nil(parse_term env alpha)
      | Sexp.List [Sexp.Atom "cons";alpha; a; xs] -> 
	 Cons((parse_term env alpha),(parse_term env a),(parse_term env xs))
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
  | Sexp.List [Sexp.Atom "iter"; p ; n ; f ; z] ->
     Iter((parse_term env p),(parse_term env n),(parse_term env f),(parse_term env z))
  | Sexp.List [Sexp.Atom ":" ;x; t] -> 
     Ann((parse_term env x),(parse_term env t))
  | Sexp.Atom v -> lookup_var env 0 v 
  | Sexp.List (f::args) -> 
     List.fold_left 
       (fun x y -> Appl(x, y))
       (parse_exTm env f)
       (List.map (parse_term env) args)
  | _ -> failwith "erreur de parsing" 

let rec pretty_print_inTm t l = 
  match t with 
  | Abs(str,x) -> "(lambda " ^ str ^ " " ^ pretty_print_inTm x (str :: l) ^ ")"
  | Inv (x) ->  pretty_print_exTm x l
  | Pi (str,s,t) -> "(pi " ^ str ^ " " ^ pretty_print_inTm s l ^ " " ^ pretty_print_inTm t (str :: l) ^ ")"
  | Star -> "*"
  | Succ n -> "(succ " ^ pretty_print_inTm n l ^ ")"
  | Zero -> "zero"
  | Nat -> "N" 
  | Pair(a,b) -> "(" ^ pretty_print_inTm a l ^ " , " ^ pretty_print_inTm b l ^ ")"
  | Cross(a,b) -> "(" ^ pretty_print_inTm a l ^ " X " ^ pretty_print_inTm b l ^ ")"
  | List(alpha) -> "(list " ^ pretty_print_inTm alpha l ^ ")"
  | Nil(alpha) -> "(nil " ^ pretty_print_inTm alpha l ^ ")"
  | Cons(alpha,a,xs) -> "(cons " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm xs l ^ ")"
and pretty_print_exTm t l =
  match t with 
  | Ann(x,y) ->  "(: " ^ pretty_print_inTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | BVar(x) -> begin 
      try List.nth l x with 
	| Failure("nth") ->  failwith ("Pretty_print_exTm BVar: something goes wrong list is to short BVar de " ^ string_of_int x)
	| _ -> List.nth l x
    end
  | FVar (x) -> x
  | Appl(x,y) -> "(" ^ pretty_print_exTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | Iter(p,n,f,z) -> "(iter " ^ pretty_print_inTm p l ^ " " ^ pretty_print_inTm n l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm z l ^ ")"
  | P0(x) -> "(p0 " ^ pretty_print_exTm x l ^ ")"
  | P1(x) -> "(p1 " ^ pretty_print_exTm x l ^ ")"
    
      




(* fonction de substitution et de réduction ect *)
(* cette fonction est "normalement bonne" *)
(* tester la fonction de réduction *)
let rec substitution_inTm t tsub var = 
  match t with 
  | Inv x -> Inv(substitution_exTm x tsub var)
  | Abs(x,y) -> Abs(x,(substitution_inTm y tsub (var+1)))
  | Star -> Star
  | Pi(v,x,y) -> Pi(v,(substitution_inTm x tsub var),(substitution_inTm y tsub (var+1)))
  | Zero -> Zero 
  | Succ n -> Succ(substitution_inTm n tsub var)
  | Nat -> Nat
  | Pair(x,y) -> Pair((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  | Cross(x,y) -> Cross((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  | List(alpha) -> List(substitution_inTm alpha tsub var)
  | Nil(alpha) -> Nil(substitution_inTm alpha tsub var)
  | Cons(alpha,a,xs) -> Cons((substitution_inTm alpha tsub var),(substitution_inTm a tsub var),(substitution_inTm xs tsub var))
and substitution_exTm  t tsub var = 
  match t with 
  | FVar x -> FVar x
  | BVar x when x = var -> tsub
  | BVar x -> BVar x
  | Appl(x,y) -> Appl((substitution_exTm x tsub var),(substitution_inTm y tsub var))
  | Ann(x,y) -> Ann((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  | Iter(p,n,f,a) -> Iter((substitution_inTm p tsub var),(substitution_inTm n tsub var),(substitution_inTm f tsub var),(substitution_inTm a tsub var))
  | P0(x) -> P0(substitution_exTm x tsub var)
  | P1(x) -> P1(substitution_exTm x tsub var)



let vfree name = VNeutral(NFree name)

(* il faut rajouter iter *)
let rec big_step_eval_exTm t envi = 
  match t with
    | Ann(x,_) -> big_step_eval_inTm x envi
    | FVar v -> vfree v 
    | BVar v -> begin try List.nth envi v with 
		| Failure("nth") -> failwith ("Big_step_eval_exTm BVar it's not possible :" ^ pretty_print_exTm t []) 
		| _ -> List.nth envi v
		end 
    | Appl(x,y) -> vapp((big_step_eval_exTm x envi),(big_step_eval_inTm y envi))    
    | Iter(p,n,f,a) -> viter(big_step_eval_inTm n envi, 
                             big_step_eval_inTm f envi,
                             big_step_eval_inTm a envi)
    | P0(x) ->
       begin 
	 match big_step_eval_exTm x envi with  
	 | VPair(a,b) -> a
	 | _ -> failwith "Impossibl: P0 can't be applied to something else then a pair"
       end 
    | P1(x) ->
       begin 
	 match big_step_eval_exTm x envi with  
	 | VPair(a,b) -> a
	 | _ -> failwith "Imposibl: P1 can't be applied to something else then a pair"
       end
and vapp v = 
  match v with 
  | ((VLam f),v) -> f v
  | ((VNeutral n),v) -> VNeutral(NApp(n,v))
  | _ -> failwith "TBD"
and viter (v, f,a) = 
  match v with
  | VZero ->  a
  | VSucc v -> vapp (f, (viter (v, f, a)))
  | _ -> failwith "Impossible (viter)"
and big_step_eval_inTm t envi = 
  match t with 
  | Inv(i) -> big_step_eval_exTm i envi
  | Abs(x,y) -> VLam(function arg -> (big_step_eval_inTm y (arg :: envi)))
  | Star -> VStar
  | Pi (v,x,y) -> VPi ((big_step_eval_inTm x envi),(function arg -> (big_step_eval_inTm y (arg :: envi))))
  | Succ (n) -> VSucc(big_step_eval_inTm n envi)
  | Zero -> VZero
  | Nat -> VNat
  | Pair(x,y) -> VPair((big_step_eval_inTm x envi),(big_step_eval_inTm y envi))
  | Cross(x,y) -> VCross((big_step_eval_inTm x envi),(big_step_eval_inTm y envi))
(* je vais mettre les big step après *)


(* il me semble qu'il me faut une fonction de relie libre avant de lancer big step eval dans le check pour que celui ci puisse faire le travail 
le contexte que l'on va utiliser est de la forme ("nom var",inTm)*)
(* rajouter iter *)
(* Cette fonction ne sert a rien du moins pour le moment *)
(*  rec relie_free_context_inTm  contexte t = 
  match t with 
  | Abs(x,y) -> Abs(x,relie_free_context_inTm contexte y)
  | Pi (v,s,z) -> Pi(v,relie_free_context_inTm contexte s,relie_free_context_inTm contexte z)
  | Star -> Star 
  | Inv(Ann(x,y)) -> Inv(Ann(relie_free_context_inTm contexte x,relie_free_context_inTm contexte y))
  | Inv(BVar(v)) -> Inv(BVar(v))
  | Inv(FVar (v)) -> List.assoc v contexte
  | Inv(Appl (x,y)) -> Inv(Appl(Ann((relie_free_context_inTm contexte (Inv(x))),Star),relie_free_context_inTm contexte y))
  | Zero -> Zero
  | Succ(n) -> Succ(relie_free_context_inTm contexte n)
  | Nat -> Nat 
  | _ -> failwith "il ne faut pas la finir" *)


let read t = parse_term [] (Sexp.of_string t)

let gensym =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c

let rec value_to_inTm i v =
  match v with 
  | VLam(f) -> Abs((string_of_int(i)),(value_to_inTm (i+1) (f(vfree(string_of_int (-i))))))
  | VNeutral(x) -> Inv(neutral_to_exTm i x)
  | VStar -> Star
  | VPi(x,f) -> let var = gensym () in 
		begin
		Pi(var,(value_to_inTm i x),(value_to_inTm (i+1) (f(vfree(string_of_int (-i))))))
		end
  | VZero -> Zero
  | VSucc(n) -> Succ(value_to_inTm i n)
  | VNat -> Nat 
  | VPair(x,y) -> Pair((value_to_inTm i x),(value_to_inTm i y))
  | VCross(x,y) -> Cross((value_to_inTm i x),(value_to_inTm i y))
and neutral_to_exTm i v = 
  match v with 
  | NFree x -> let k = begin 
		   try int_of_string x with 
		   | Failure("int_of_string") -> 10 (* i juste need a positive value *)
		   | _ -> int_of_string x
		 end in
	       if k <= 0 then BVar(i + k - 1)
	       else FVar x
  | NApp(n,x) -> Appl((neutral_to_exTm i n),(value_to_inTm i x))


(*fonction d'égalité pour les termes *)
let rec equal_inTm t1 t2 = 
  match (t1,t2) with 
  | (Abs(_,x1),Abs(_,x2)) -> equal_inTm x1 x2
  | (Pi(_,x1,y1),Pi(_,x2,y2)) -> equal_inTm x1 x2 = equal_inTm y1 y2
  | (Star,Star) -> true 
  | (Zero,Zero) -> true 
  | (Succ(n1),Succ(n2)) -> equal_inTm n1 n2
  | (Nat,Nat) -> true
  | (Inv(x1),Inv(x2)) -> equal_exTm x1 x2
  | (Pair(x1,y1),Pair(x2,y2)) -> equal_inTm x1 x2 = equal_inTm y1 y2
  | (Cross(x1,y1),Cross(x2,y2)) -> equal_inTm x1 x2 = equal_inTm y1 y2
  | _ -> false
and equal_exTm t1 t2 = 
  match (t1,t2) with 
  | (Ann(x1,y1),Ann(x2,y2)) -> equal_inTm x1 x2 = equal_inTm y1 y2
  | (BVar(x1),BVar(x2)) -> x1 = x2
  | (FVar(x1),FVar(x2)) -> x1 = x2
  | (Appl(x1,y1),Appl(x2,y2)) -> equal_exTm x1 x2 = equal_inTm y1 y2 
  | (Iter(w1,x1,y1,z1),Iter(w2,x2,y2,z2)) -> 
     equal_inTm w1 w2 = equal_inTm x1 x2 = equal_inTm y1 y2 = equal_inTm z1 z2
  | (P0(x1),P0(x2)) -> equal_exTm x1 x2
  | (P1(x1),P1(x2)) -> equal_exTm x1 x2
  | _ -> false

	
(* fonctions pour le debug *)
let rec contexte_to_string contexte l= 
  match contexte with 
  | [] -> "|" 	    
  | (s,w) :: tail -> "(" ^ s ^ "," ^ pretty_print_inTm w l ^ ");" ^ contexte_to_string tail l  


(* alors soit je remplace les FVar des le debut lorsque je les mets dans le contexte ou alor a la sortie *)
let rec check contexte inT ty steps = 
  match inT with 
  | Abs(x,y) -> 
     begin 
     match ty with      
     | Pi(v,s,t) -> let freshVar = gensym () in 
		    check ((freshVar,s)::contexte) (substitution_inTm y (FVar(freshVar)) 0) (substitution_inTm t (FVar(freshVar)) 0) (steps ^ ";" ^ (pretty_print_inTm inT [])) 
     | _ -> create_report false (contexte_to_string contexte []) steps "Abs type must be a Pi"
     end 
  | Inv(t) -> 
     if res_debug_synth (synth contexte t (steps ^";" ^(pretty_print_inTm inT [])))
     then 
       let tyT = ret_debug_synth (synth contexte t (steps ^";" ^(pretty_print_inTm inT []))) in
       begin       
	 if equal_inTm (value_to_inTm 0 (big_step_eval_inTm tyT [])) (value_to_inTm 0 (big_step_eval_inTm ty []))
	 then create_report true (contexte_to_string contexte []) steps "NO"
	 else create_report false (contexte_to_string contexte []) steps "eval of tyt and eval of ty not equal"
       end
     else create_report false (contexte_to_string contexte []) steps "Synth of tyT goes wrong"
  | Pi(v,s,t) ->     
     begin 
       match ty with 
	 | Star -> let freshVar = gensym () in 
		   begin 
		     let rep = (check contexte s Star (steps ^ (pretty_print_inTm inT []))) in 
		     begin 
		       match rep with 
		     | Report(Success(true),c,e,er) -> 
			check ((freshVar,s)::contexte) (substitution_inTm t (FVar(freshVar)) 0) Star (steps ^";" ^ (pretty_print_inTm inT []))
		     | Report(Success(false),c,e,er) -> 
			create_report false (contexte_to_string contexte []) steps ("Pi (x S T) S is not of type Star" ^ (pretty_print_inTm inT []))
		     | _ -> failwith "Pi : It is not possible to get a report without a Success in first arg"
		     end 
		   end
	 | Inv(FVar(v)) -> let freshVar = gensym () in 
		   begin 
		     let rep = (check contexte s ty (steps ^ (pretty_print_inTm inT []))) in 
		     begin 
		       match rep with 
		     | Report(Success(true),c,e,er) -> 
			check ((freshVar,s)::contexte) (substitution_inTm t (FVar(freshVar)) 0) ty (steps ^";" ^ (pretty_print_inTm inT []))
		     | Report(Success(false),c,e,er) -> 
			create_report false (contexte_to_string contexte []) steps ("Pi (x S T) S is not of type:" ^ (pretty_print_inTm ty []) ^ "!!!!" ^ (pretty_print_inTm inT []))
		     | _ -> failwith "Pi : It is not possible to get a report without a Success in first arg"
		     end 
		   end
	 | _ -> create_report false (contexte_to_string contexte []) steps "Pi : Ty must be of type star"
     end
  | Star -> 
     begin 
      match ty with 
	| Star -> create_report true (contexte_to_string contexte []) steps "No"
	| _ -> create_report false (contexte_to_string contexte []) steps "Star : ty must be of type Star"
     end
  | Zero -> 
     begin 
       match ty with 
       | Nat -> create_report true (contexte_to_string contexte []) steps "No"
       | _ -> create_report false (contexte_to_string contexte []) steps "Zero : ty must be of type Nat"
     end 
  | Succ(n) -> 
     begin 
       match ty with 
       | Nat -> check contexte n Nat (steps ^ ";" ^(pretty_print_inTm inT []))
       | _ -> create_report false (contexte_to_string contexte []) steps "Succ : ty must be of type Nat"
     end 
  | Nat -> 
     begin
       match ty with 
       | Star -> create_report true (contexte_to_string contexte []) steps "No"
       | _ -> create_report false (contexte_to_string contexte []) steps "Nat : ty must be of type *"
     end 
  (* je sais que ça ne vas pas marcher tout le temps je veux juste discuter d'abord de la gestion des FVar avant de le faire *)
  | Pair(x,y) -> 
     begin 
       match ty with 
       | Cross(a,b) -> if res_debug(check contexte x a (steps ^ ";" ^(pretty_print_inTm inT [])))
		       then check contexte y b (steps ^ ";" ^(pretty_print_inTm inT []))
		       else create_report false (contexte_to_string contexte []) steps "Pair : x is not of type of a in Cross(a,b)"     
       | _ -> failwith "A changer pour la meme raison que l'autre fois mais on va trouver une solution durable"
     end 
 (* je sais que ça ne vas pas marcher tout le temps je veux juste discuter d'abord de la gestion des FVar avant de le faire *)
  | Cross(a,b) -> 
     begin 
       match ty with 
	 | Star -> if res_debug(check contexte a Star (steps ^ ";" ^(pretty_print_inTm inT [])))
		   then check contexte b Star (steps ^ ";" ^(pretty_print_inTm inT []))
		   else create_report false (contexte_to_string contexte []) steps "Cross : b is not of type Star"     
	 | _ -> failwith "A changer aussi toutes les étoiles ne se valent pas"
     end
  | List(alpha) -> 
     begin 
       match ty with 
       | Star -> check contexte alpha Star (steps ^ ";" ^(pretty_print_inTm inT []))
       | _ -> failwith "A changer pour trouver une sol durable"
     end
  | Nil(alpha) -> 
     begin 
       match ty with 
       | List(a) -> (* ici esque je dois faire la reduction des deux alpha je pense que oui *)
	  if equal_inTm alpha a
	  then check contexte alpha Star (steps ^ ";" ^(pretty_print_inTm inT []))
	  else create_report false (contexte_to_string contexte []) steps "Nil alpha is not of type of a"     
       | _ -> failwith "A changer pour trouver une sol durable"
     end
  | Cons(alpha,a,xs) -> 
     begin
       match ty with  
       | List(alphabis) -> 
	  if (equal_inTm alpha alphabis) && (res_debug(check contexte alpha Star (steps ^ ";" ^(pretty_print_inTm inT []))))
	  then 
	    begin 
	      if res_debug(check contexte a alpha (steps ^ ";" ^(pretty_print_inTm inT [])))
	      then check contexte xs ty (steps ^ ";" ^(pretty_print_inTm inT []))
	      else create_report false (contexte_to_string contexte []) steps "Cons a is not of type alpha"     
	    end 
	  else create_report false (contexte_to_string contexte []) steps "Cons , alpha is not equal or alpha is not of type Star"     
       | _ -> failwith "peut etre trouver une autre solution"
     end      
and synth contexte exT steps =
  match exT with 
  | BVar x -> create_retSynth (create_report false (contexte_to_string contexte []) steps "BVar : not possible during type checking") Star
  | FVar x -> create_retSynth (create_report true (contexte_to_string contexte []) steps "NO") (List.assoc x contexte)
  | Ann(tm, ty) ->
       if res_debug (check contexte ty Star (steps ^ ";" ^(pretty_print_exTm exT [])))
	  &&  res_debug(check contexte tm ty (steps ^ ";" ^(pretty_print_exTm exT []))) 
       then create_retSynth (create_report true (contexte_to_string contexte []) steps "NO") ty    
       else
	 create_retSynth (create_report false (contexte_to_string contexte []) steps "Ann: Wrong annotation") Star
  | Appl(x,y) -> 
     let pTy = ret_debug_synth (synth contexte x (steps ^ ";" ^(pretty_print_exTm exT []))) in 
     begin 
       match pTy with 
       | Pi(v,s,t) -> if res_debug(check contexte y s (steps ^ ";" ^(pretty_print_exTm exT []))) 
		    then create_retSynth (create_report true (contexte_to_string contexte []) steps "NO") (substitution_inTm t (Ann(y,s)) 0)
		    else  create_retSynth (create_report false (contexte_to_string contexte []) steps "Y don't have the type of S") Star
       | _ -> create_retSynth (create_report false (contexte_to_string contexte []) steps "Appl: pTy must be of type Pi ") Star
     end
(*  | Iter (p,n,f,z) -> if res_debug(check contexte p (read "(-> N *)") (steps ^ ";" ^(pretty_print_exTm exT [])))
		      then 
			 begin
			   if res_debug(check contexte n (read "N") (steps ^ ";" ^(pretty_print_exTm exT [])))
			   then 
			     begin 
			       if res_debug(check contexte f (read "(pi n N (-> (P n) (P (succ n))))") (steps ^ ";" ^(pretty_print_exTm exT [])))
			       then
				 begin 
				   if res_debug(check contexte z () (steps ^ ";" ^(pretty_print_exTm exT [])))
				   then
				   else
				 end 
			       else create_retSynth (create_report false (contexte_to_string contexte []) steps "Iter: f is not of type (pi n N (-> (P n) (P (succ n))))") Star
			     end 
			   else create_retSynth (create_report false (contexte_to_string contexte []) steps "Iter: n is not of type Nat") Star
			 end
		      else create_retSynth (create_report false (contexte_to_string contexte []) steps "Iter: P is not of type (-> N *)") Star *)
  | _ -> failwith "je dois faire p0 et p1"

