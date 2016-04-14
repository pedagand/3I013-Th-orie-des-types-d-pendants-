open Sexplib


(* je garde la représentation que l'on avait de l'abstraction, avec la variable en string au début *)

type name =
  | Global of string 
  | Bound of int 
  | Quote of int


type inTm = 
  | Abs of name * inTm
  | Inv of exTm
  | Pi of name * inTm * inTm 
  | Star
  | Zero
  | Succ of inTm
  | Nat
  | Pair of inTm * inTm 
  | Cross of inTm * inTm
  | List of inTm 
  | Nil of inTm 
  | Cons of inTm * inTm * inTm 
  | Vec of inTm * inTm
  | DNil of inTm
  | DCons of inTm * inTm 
  | What
  | Id of inTm * inTm * inTm
  | Refl of inTm 
and exTm = 
  | Ann of inTm * inTm 
  | BVar of int 
  | FVar of name 
  | Appl of exTm * inTm
  | Iter of inTm * inTm * inTm * inTm  
  | Trans of inTm * inTm * inTm * inTm * inTm * inTm 
  | P0 of exTm
  | P1 of exTm 
  | DFold of inTm * inTm * inTm * inTm * inTm * inTm 
 
(*= Value*)
type value = 
  | VLam of (value -> value)
  | VNeutral of neutral 
  | VStar 
  | VPi of value * (value -> value)
(*= End*)
(*= Value_Nat*)
  | VNat
  | VZero
  | VSucc of value
(*=End*)
(*= Value_Vector*)
  | VVec of value * value 
  | VDNil of value
  | VDCons of value * value 
(*=End*)
  | VId of value * value * value 
  | VRefl of value
and neutral = 
  | NFree of name 
  | NApp of neutral * value 
  | NIter of value * value * value * value
  | NDFold of value * value * value * value * value * value 
  | NTrans of value * value * value * value * value * value  


type debug = 
  | Report of debug * debug * debug * debug
  | Success of bool
  | Contexte of string
  | Steps of string
  | Error of string
and debug_synth = 
  | RetSynth of debug * value

(* fonction pour les rapports d'erreurs *)
let create_report s c e er= 
  Report(Success(s),Contexte(c),Steps(e),Error(er))

let create_retSynth d v = 
  RetSynth(d,v)

let print_report r = 
  match r with 
  | Report(Success(s),Contexte(c),Steps(e),Error(er)) -> 
     "Report : \n -Success : " ^ string_of_bool s ^ "\n" ^
       "-Contexte : " ^ c ^ "\n" ^
	 "-Steps : " ^ e ^ "\n" ^
	   "-Error : " ^ er ^ "\n" 
  | _ -> failwith "can't print something which is not a report" 

let print_report_synth r = 
  match r with 
  | RetSynth(Report(s,c,e,er),y) -> print_report (Report(s,c,e,er))
  | _ -> failwith "report synth don't have a good shape"

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


let rec parse_term env t = 
      match t with   
      | Sexp.Atom "*" -> Star
      | Sexp.Atom "zero" -> Zero
      | Sexp.Atom "N" -> Nat 
      | Sexp.Atom "?" -> What
      | Sexp.List [Sexp.Atom "succ"; n] -> 
	 Succ(parse_term env n)
      | Sexp.List [Sexp.Atom "id";gA;a;b] -> 
	 Id((parse_term env gA),(parse_term env a),(parse_term env b))
      | Sexp.List[Sexp.Atom "refl";a] -> 
	 Refl(parse_term env a)
      | Sexp.List [Sexp.Atom "lambda"; Sexp.Atom var; body] -> 
	 Abs(Global(var),(parse_term (Global(var)::env) body))
      | Sexp.List [Sexp.Atom "lambda"; Sexp.List vars ; body] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser: Lambdainvalid variable") vars
	 in 
	 List.fold_right 
           (fun var b -> Abs(var,b))
           (List.map (fun x -> Global(x)) vars)
           (parse_term (List.append (List.rev ((List.map (fun x -> Global(x)) vars))) env) body)      
      | Sexp.List [Sexp.Atom "->"; s ; t ] -> 
	 Pi(Global("NO"),(parse_term env s),(parse_term (Global("NO") :: env) t))
      | Sexp.List [Sexp.Atom "pi"; Sexp.Atom var ; s ; t] -> 
	 Pi(Global(var),(parse_term env s),(parse_term (Global(var)::env) t))        
      | Sexp.List [Sexp.Atom "pi";Sexp.List vars; s; t] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser pi invalide variable") vars 
	 in 
	 List.fold_right
	   (fun var b -> Pi(var,(parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env) s),b))
	   (List.map (fun x -> Global(x)) vars)
	   (parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env) t)
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
      | Sexp.List [Sexp.Atom "vec";alpha; n] -> 
	 Vec((parse_term env alpha),(parse_term env n))
      | Sexp.List [Sexp.Atom "dnil";alpha] -> 
	 DNil(parse_term env alpha)
      | Sexp.List [Sexp.Atom "dcons";a;xs] -> 
	 DCons((parse_term env a),(parse_term env xs))
(* ----------------------termes librairie-------------------------------- *)
      | Sexp.List [Sexp.Atom "+";n;a] -> 
	 Inv(Appl(Appl(Ann((parse_term env (Sexp.of_string "(lambda n (lambda a (iter (lambda x N) n (lambda ni (lambda x (succ x))) a)))")),Nat),(parse_term env n)),(parse_term env a)))
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
  | Sexp.List [Sexp.Atom "dfold";alpha;p;n;xs;f;a] -> 
     DFold((parse_term env alpha),(parse_term env p),(parse_term env n),(parse_term env xs),(parse_term env f),(parse_term env a))
  | Sexp.List [Sexp.Atom "trans"; gA;p;a;b;q;x] ->
     Trans((parse_term env gA),(parse_term env p),(parse_term env a),(parse_term env b),(parse_term env q),(parse_term env x))
  | Sexp.Atom v -> lookup_var env 0 (Global(v))
  | Sexp.List (f::args) -> 
     List.fold_left 
       (fun x y -> Appl(x, y))
       (parse_exTm env f)
       (List.map (parse_term env) args)
  | _ -> failwith "erreur de parsing" 

let read t = parse_term [] (Sexp.of_string t)
 
let rec pretty_print_inTm t l = 
  match t with 
  | Abs(Global(str),x) -> "(lambda " ^ str ^ " " ^ pretty_print_inTm x (str :: l) ^ ")"
  | Abs(_,x) -> failwith "Pretty print Abs first arg must be a global"
  | Inv (x) ->  pretty_print_exTm x l
  | Pi (Global(str),s,t) -> "(pi " ^ str ^ " " ^ pretty_print_inTm s l ^ " " ^ pretty_print_inTm t (str :: l) ^ ")"
  | Pi (_,s,t) -> failwith "Pretty print Pi first arg must be a global"
  | Star -> "*"
  | Succ n -> "(succ " ^ pretty_print_inTm n l ^ ")"
  | Zero -> "zero"
  | Nat -> "N" 
  | Pair(a,b) -> "(" ^ pretty_print_inTm a l ^ " , " ^ pretty_print_inTm b l ^ ")"
  | Cross(a,b) -> "(" ^ pretty_print_inTm a l ^ " X " ^ pretty_print_inTm b l ^ ")"
  | List(alpha) -> "(list " ^ pretty_print_inTm alpha l ^ ")"
  | Nil(alpha) -> "(nil " ^ pretty_print_inTm alpha l ^ ")"
  | Cons(alpha,a,xs) -> "(cons " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm xs l ^ ")"
  | Vec(alpha,n) -> "(vec " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm n l ^ ")"
  | DNil(alpha) -> "(dnil " ^ pretty_print_inTm alpha l ^ ")"
  | DCons(a,xs) -> "(dcons " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm xs l ^ ")"
  | What -> "?"
  | Id(bA,a,b) -> "(id " ^ pretty_print_inTm bA l ^ " " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm b l ^ ")"
  | Refl(a) -> "(refl " ^ pretty_print_inTm a l ^ ")"
and pretty_print_exTm t l =
  match t with 
  | Ann(x,y) ->  "(: " ^ pretty_print_inTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | BVar(x) -> begin 
      try List.nth l x with 
	| Failure("nth") ->  failwith ("Pretty_print_exTm BVar: something goes wrong list is to short BVar de " ^ string_of_int x) 
	| _ -> List.nth l x
    end
  | FVar (Global x) ->  x
  | FVar (Quote x) -> string_of_int x 
  | FVar (Bound x) -> string_of_int x
  | Appl(x,y) -> "(" ^ pretty_print_exTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | Iter(p,n,f,z) -> "(iter " ^ pretty_print_inTm p l ^ " " ^ pretty_print_inTm n l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm z l ^ ")"
  | P0(x) -> "(p0 " ^ pretty_print_exTm x l ^ ")"
  | P1(x) -> "(p1 " ^ pretty_print_exTm x l ^ ")"
  | DFold(alpha,p,n,xs,f,a) -> "(dfold " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm p l ^ " " ^pretty_print_inTm n l ^ 
				 " " ^ pretty_print_inTm xs l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm a l ^ ")"
  | Trans(bA,p,a,b,q,x) -> "(trans " ^ pretty_print_inTm bA l ^ " " ^pretty_print_inTm p l ^ " " ^pretty_print_inTm a l ^ " " ^
			     pretty_print_inTm b l ^ " " ^pretty_print_inTm q l ^ " " ^pretty_print_inTm x l ^ ")"


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
  | Vec(alpha,n) -> Vec((substitution_inTm alpha tsub var),(substitution_inTm n tsub var))
  | DNil(alpha) -> DNil(substitution_inTm alpha tsub var)
  | DCons(a,xs) -> DCons((substitution_inTm a tsub var),(substitution_inTm a tsub var))
  | What -> What
  | Id(gA,a,b) -> Id((substitution_inTm gA tsub var),(substitution_inTm a tsub var),(substitution_inTm b tsub var))
  | Refl(a) -> Refl(substitution_inTm a tsub var)
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
  | DFold(alpha,p,n,xs,f,a) -> DFold((substitution_inTm alpha tsub var),(substitution_inTm p tsub var),(substitution_inTm n tsub var),
				     (substitution_inTm xs tsub var),(substitution_inTm f tsub var),(substitution_inTm a tsub var))
  | Trans(gA,p,a,b,q,x) -> Trans((substitution_inTm gA tsub var),(substitution_inTm p tsub var),(substitution_inTm a tsub var),
				 (substitution_inTm b tsub var),(substitution_inTm q tsub var),(substitution_inTm x tsub var))



let vfree n = VNeutral(NFree n)
  
let rec big_step_eval_inTm t envi = 
  match t with 
  | Inv(i) -> big_step_eval_exTm i envi
  | Abs(x,y) -> VLam(function arg -> (big_step_eval_inTm y (arg::envi)))
  | Star -> VStar
  | Pi (v,x,y) -> VPi ((big_step_eval_inTm x envi),(function arg -> (big_step_eval_inTm y (arg :: envi))))
  | Nat -> VNat
  | Zero -> VZero
  | Succ(n) -> VSucc(big_step_eval_inTm n envi)
  | Vec(alpha,n) -> VVec((big_step_eval_inTm alpha envi),(big_step_eval_inTm n envi))
  | DNil(alpha) -> VDNil(big_step_eval_inTm alpha envi)
  | DCons(a,xs) -> VDCons((big_step_eval_inTm a envi),(big_step_eval_inTm xs envi))
  | Id(gA,a,b) -> VId((big_step_eval_inTm gA envi),(big_step_eval_inTm a envi),(big_step_eval_inTm b envi))
  | _ -> failwith "a faire plus tard"
and vapp v = 
  match v with 
  | ((VLam f),v) -> f v
  | ((VNeutral n),v) -> VNeutral(NApp(n,v))
  | _ -> failwith "TBD"
and vitter (p,n,f,a) =
  match n with
  | VZero -> a
  | VSucc(x) -> vapp(f,(vitter (p,x,f,a)))
  | _ -> VNeutral(NIter(p,n,f,a))
and big_step_eval_exTm t envi = 
  match t with 
  | Ann(x,_) -> big_step_eval_inTm x envi 
  | FVar(v) -> vfree v 
  | BVar(v) -> List.nth envi v 
  | Appl(x,y) -> vapp((big_step_eval_exTm x envi),(big_step_eval_inTm y envi))    
  | Iter(p,n,f,a) -> vitter ((big_step_eval_inTm p envi),
			     (big_step_eval_inTm n envi),
			     (big_step_eval_inTm f envi),
			     (big_step_eval_inTm a envi))
  | _ -> failwith "Chaques choses en son temps nottamment DFold"


let boundfree i n = 
  match n with 
  | Quote k -> BVar (i - k - 1)
  | x -> FVar x

let gensym =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c

let rec value_to_inTm i v =
  match v with 
  | VLam f -> value_to_inTm (i+1) (f (vfree(Quote i)))
  | VNeutral n -> Inv(neutral_to_exTm i n)
  | VPi(x,f) -> let var = gensym () in 
		begin
		  Pi(Global(var),(value_to_inTm i x),(value_to_inTm (i+1) (f(vfree(Quote i)))))
		end
  | VStar -> Star
  | VNat -> Nat
  | VZero -> Zero
  | VSucc(n) -> Succ(value_to_inTm i n)
  | VVec(alpha,n) -> Vec((value_to_inTm i alpha),(value_to_inTm i n))
  | VDNil(alpha) -> DNil(value_to_inTm i alpha)
  | VDCons(a,xs) -> DCons((value_to_inTm i a),(value_to_inTm i xs)) 
  | VId(gA,a,b) -> Id((value_to_inTm i gA),(value_to_inTm i a),(value_to_inTm i b))
  | VRefl(a) -> Refl(value_to_inTm i a) 
and neutral_to_exTm i v = 
  match v with 
  | NFree x -> boundfree i x
  | NApp(n,x) -> Appl((neutral_to_exTm i n),(value_to_inTm i x))
  | NDFold(alpha,p,n,xs,f,a) -> DFold((value_to_inTm i alpha),(value_to_inTm i p),(value_to_inTm i n),
				      (value_to_inTm i xs),(value_to_inTm i f),(value_to_inTm i a))
  | NIter(p,n,f,a) -> Iter((value_to_inTm i p),(value_to_inTm i n),(value_to_inTm i f),(value_to_inTm i a))
  | NTrans(gA,p,a,b,q,x) -> Trans((value_to_inTm i gA),(value_to_inTm i p),(value_to_inTm i a),
				  (value_to_inTm i b),(value_to_inTm i q),(value_to_inTm i x))


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
  | (What,What) -> true
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



let rec contexte_to_string contexte = 
  match contexte with 
  | [] -> "|" 	    
  | (Global s,w) :: tail -> "(" ^ s ^ "," ^ pretty_print_inTm (value_to_inTm 0 w) [] ^ ");" ^ contexte_to_string tail  
  | _ -> failwith "Must not append"



let rec check contexte inT ty steps = 
  match inT with 
  | Abs(x,y) -> 
     begin  
       match ty with 
       | VPi(s,t) -> let freshVar = gensym () in 
		     check (((Global freshVar),s)::contexte) (substitution_inTm y (FVar(Global(freshVar))) 0) (t (vfree (Global freshVar))) (pretty_print_inTm inT [] ^ ";"^ steps) 
       | _ -> create_report false (contexte_to_string contexte) steps "Abs type must be a Pi"
     end 
  | Inv(x) -> 
     let ret = synth contexte x (pretty_print_inTm inT [] ^ ";" ^ steps) in 
     if res_debug_synth ret
     then 
       begin 
	 if equal_inTm (value_to_inTm 0 (ty)) (value_to_inTm 0 (ret_debug_synth ret))
	 then create_report true (contexte_to_string contexte) steps "NO"
	 else create_report false (contexte_to_string contexte) steps "Inv: ret and ty are not equal"
       end
     else create_report false (contexte_to_string contexte) steps ("Inv: Synth of x goes wrong \n ----Rapport du Inv---\n" ^ print_report_synth ret ^ "\n------Fin Rapport Inv---\n")
  | Star -> 
     begin 
      match ty with 
	| VStar -> create_report true (contexte_to_string contexte) steps "No"
	| _ -> create_report false (contexte_to_string contexte) steps "Star : ty must be of type Star"
     end
  | Pi (v,s,t) -> 
     begin 
       match ty with 
       | VStar -> let freshVar = gensym () in 
		  if res_debug(check contexte s VStar (pretty_print_inTm inT [] ^ ";"^ steps))
		  then check (((Global freshVar),(big_step_eval_inTm s []))::contexte) (substitution_inTm t (FVar(Global(freshVar))) 0) VStar (pretty_print_inTm inT [] ^ ";"^ steps)
		  else create_report false (contexte_to_string contexte) steps "Pi : S is not of type Star"
       | _ -> create_report false (contexte_to_string contexte) steps "Pi : ty must be of type Star"
     end 
  | Nat -> 
     begin 
       match ty with
       | VStar -> create_report true (contexte_to_string contexte) steps "No"
       | _ -> create_report false (contexte_to_string contexte) steps "Nat : ty must be VStar"
     end 
  | Zero -> 
     begin 
       match ty with 
       | VNat -> create_report true (contexte_to_string contexte) steps "No"
       | _ -> create_report false (contexte_to_string contexte) steps "Zero : ty must be VNat"
     end
  | Succ(x) -> 
     begin 
       match ty with 
	 | VNat -> check contexte x VNat (pretty_print_inTm inT [] ^ ";"^ steps)
	 | _ -> create_report false (contexte_to_string contexte) steps "Succ : ty must be VNat"
     end 
  | Vec(alpha,n) -> 
     begin        
       match ty with 
       | VStar -> let check_alpha = check contexte alpha VStar (pretty_print_inTm inT [] ^ ";"^ steps) in
		  if res_debug(check_alpha) 
		  then check contexte n VNat (pretty_print_inTm inT [] ^ ";"^ steps)
		  else create_report false (contexte_to_string contexte) steps "Vec : alpha must be of type star"
       | _ -> create_report false (contexte_to_string contexte) steps "Vec : ty must be VStar"
     end 
       (* ici c'est toujours pareil je ne sais pas si je dois matcher une FVar ou pas *)
  | DNil(alpha) -> 
     begin
       match ty with
       | VVec(alpha_vec,zero) -> if equal_inTm (value_to_inTm 0 (big_step_eval_inTm alpha [])) 
					       (value_to_inTm 0 alpha_vec)
				then create_report true (contexte_to_string contexte) steps "NO"
				else create_report false (contexte_to_string contexte) steps "DNil : Alpha must be the sames"
       | _ -> create_report false (contexte_to_string contexte) steps "Vec : ty must be a VVec"       
     end 
  | DCons(a,xs) -> 
     begin 
       match ty with 
       | VVec(alpha,VSucc(n)) -> let check_xs = check contexte xs (VVec(alpha,n)) (pretty_print_inTm inT [] ^ ";"^ steps) in 
				 if res_debug(check_xs)
				 then check contexte a alpha (pretty_print_inTm inT [] ^ ";"^ steps)
				 else create_report false (contexte_to_string contexte) steps "DCons : xs must be of type (VVec alpha n)"
       | _ -> create_report false (contexte_to_string contexte) steps "DCons : ty must be a VVec"
     end 
  | What -> create_report false (contexte_to_string contexte) steps ("What : we try to push this terme " ^ (pretty_print_inTm (value_to_inTm 0 ty)  []))
  | Id(gA,a,b) -> let check_gA = check contexte gA VStar (pretty_print_inTm inT [] ^ ";"^ steps) in 		  
		  let eval_gA = big_step_eval_inTm gA [] in 
		  let check_a = check contexte a eval_gA (pretty_print_inTm inT [] ^ ";"^ steps) in 
		  let check_b = check contexte b eval_gA (pretty_print_inTm inT [] ^ ";"^ steps) in 
		  if res_debug(check_gA) 
		  then 
		    begin 
		      if res_debug(check_a) 
		      then 
			begin 
			  if res_debug(check_b) 
			  then create_report true (contexte_to_string contexte) steps "NO"
			  else create_report false (contexte_to_string contexte) steps "Id : b must be of type gA"
			end 
		      else create_report false (contexte_to_string contexte) steps "Id : a must be of type gA"
		    end  
		  else create_report false (contexte_to_string contexte) steps "Id : gA must be of type Star"
  | Refl(a) -> 
     begin
       match ty with 
       | VId(gA,ta,ba) -> let quote_ta = value_to_inTm 0 ta in 
			  let quote_ba = value_to_inTm 0 ba in
			  if equal_inTm a quote_ta && equal_inTm a quote_ba
			  then
			    begin 
			      check contexte a gA (pretty_print_inTm inT [] ^ ";"^ steps)
			    end 
			  else create_report false (contexte_to_string contexte) steps "Refl : a and ta must be equal"	       
       | _ -> create_report false (contexte_to_string contexte) steps "Refl : ty must be of type Id"
     end
  | _ -> failwith "HEHEHEHEHE"
and synth contexte exT steps =
  match exT with 
  | BVar x -> create_retSynth (create_report false (contexte_to_string contexte) steps "BVar : not possible during type checking") VStar
  | FVar x -> create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (List.assoc x contexte)
  | Ann(x,t) -> let ret = check contexte t VStar (pretty_print_exTm exT [] ^ ";"^ steps) in 
		let eval_t = big_step_eval_inTm t [] in
		if res_debug(ret)
		then 
		  begin 
		    if res_debug(check contexte x eval_t (pretty_print_exTm exT [] ^ ";"))
		    then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") eval_t
		    else create_retSynth (create_report false (contexte_to_string contexte) steps "Ann : x is not of type t") VStar
		  end
		else create_retSynth (create_report false (contexte_to_string contexte) steps "Ann : t is not of type VStar") VStar
  | Appl(f,s) -> 
     let synth_f = synth contexte f (pretty_print_exTm exT [] ^ ";"^ steps) in 
     begin
       match ret_debug_synth synth_f with 
       | VPi(s_pi,fu) -> if res_debug(check contexte s s_pi (pretty_print_exTm exT [] ^ ";"))
		     then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (fu (big_step_eval_inTm s [])) 
		     else create_retSynth (create_report false (contexte_to_string contexte) steps "Appl : s is not of type S") VStar
       | _ -> create_retSynth (create_report false (contexte_to_string contexte) steps "Appl : f is not of type Pi") VStar
     end
  | Iter(p,n,f,a) -> let big_p = big_step_eval_inTm p [] in
		     let big_n = big_step_eval_inTm n [] in 
 		     let check_p = check contexte p (big_step_eval_inTm (read "(-> N *)") []) (pretty_print_exTm exT [] ^ ";") in    
		     let check_n = check contexte n (big_step_eval_inTm (read "N") []) (pretty_print_exTm exT [] ^ ";") in
		     let check_f = check contexte f (big_step_eval_inTm (Pi(Global("n"),Nat,Pi(Global("NO"),(Inv(Appl(Ann(p,Pi(Global"NO",Nat,Star)),n))),(Inv(Appl(Ann(p,Pi(Global"NO",Nat,Star)),Succ(n))))))) [])  (pretty_print_exTm exT [] ^ ";") in
		     let check_a = check contexte a (vapp(big_p,VZero)) (pretty_print_exTm exT [] ^ ";") in
		     if res_debug(check_n)
		     then 
		       begin 
			 if res_debug(check_p)
			 then 
			   begin 
			     if res_debug(check_f)
			     then
			       begin 
				 if res_debug(check_a)
				 then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (vapp(big_p,big_n)) 
				 else create_retSynth (create_report false (contexte_to_string contexte) steps "Iter : a is not of type (P 0)") VStar
			       end
			     else create_retSynth (create_report false (contexte_to_string contexte) steps "Iter : f is not of type (pi n N (-> (P n) (P (succ n))))") VStar
			   end 
			 else create_retSynth (create_report false (contexte_to_string contexte) steps "Iter : p is not of type (-> N *)") VStar
		       end 
		     else create_retSynth (create_report false (contexte_to_string contexte) steps "Iter : n is not of type VNat") VStar     
  | _ -> failwith "HAHAHAHAHAHAHA"



(* let () = Printf.printf "%s" (print_report (check [] (read "(lamba x x)") (big_step_eval_inTm (read "(-> * *)") []) "")) *)
