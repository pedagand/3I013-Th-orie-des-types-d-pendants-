open Sexplib
open OUnit2

(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #require "sexplib";;
  #require "oUnit";;
*)

(** * Terms *)

(* TODO: add a [string] to [Abs] for pretty-printing *)

(*=untyped_term *)
type lambda_term =
  | FreeVar of string 
  | BoundVar of int 
  | Abs of string * lambda_term
  | Appl of lambda_term * lambda_term
(*=End *)
  | Let of lambda_term * lambda_term 
  | DefVar of string
(*=bool_term *)
  | True | False 
  | IfThenElse of lambda_term * lambda_term * lambda_term
(*=End *)
(*=nat_term *)
  | Zero | Succ of lambda_term 
  | Iter of lambda_term * lambda_term * lambda_term
(*=End *)
(*=pair_term *)
  | Pair of lambda_term * lambda_term
  | Pi0 of lambda_term
  | Pi1 of lambda_term
(*=End *)

(** * A simple parser *)

let rec parse env t 
    = let rec lookup_var env n v
        = match env with
        | [] -> DefVar v
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
         Abs (var,(parse (var :: env) body))
      | Sexp.List [Sexp.Atom "lambda"; Sexp.List vars; body] -> 
         let vars = List.map (function 
           | Sexp.Atom v -> v
           | _ -> failwith "Parser: invalid variable") vars 
         in
         List.fold_right 
           (fun var b -> Abs (var,b))
           vars
           (parse (List.append (List.rev vars) env) body)
      | Sexp.List [Sexp.Atom "let"; Sexp.List defs; body] -> 
        let (env, defs) = List.fold_left (fun (env, acc) tm ->
            match tm with
            | Sexp.List [Sexp.Atom id; tm] ->
              (id :: env, parse env tm :: acc)
            | _ -> failwith "Parser: invalid 'let'") (env, []) defs
        in
        List.fold_right (fun tm acc -> Let (tm, acc)) (List.rev defs)
          (parse env body)
      | Sexp.Atom v -> lookup_var env 0 v
      | Sexp.List (f :: args) -> 
         List.fold_left 
           (fun x y -> Appl (x, y))
           (parse env f) 
           (List.map (parse env) args)      
      | _ -> failwith "Parser: ill-formed input."

let read t = parse [] (Sexp.of_string t)

module ParserT =
  struct
    let inputs
      = [("(lambda x x)", Abs("x",BoundVar 0));
         ("(lambda x y)", Abs("x",DefVar "y"));
         ("(x y z)", Appl (Appl (DefVar "x", DefVar "y"), DefVar "z"));
         ("(lambda (x y z) (x (y z)))", Abs ("x",Abs ("y",Abs ("z",Appl (BoundVar 2, Appl (BoundVar 1, BoundVar 0))))));
         ("(lambda (x y z) (x y z))", Abs ("x",Abs ("y",Abs ("z",Appl (Appl (BoundVar 2, BoundVar 1), BoundVar 0)))));
         ("(let ((id (lambda x x))
                 (fst (lambda (x y) x)) 
                 (k (id fst))) 
             (k id))", 
          Let (Abs ("x",BoundVar 0),
          Let (Abs ("x",Abs ("y",BoundVar 1)),
          Let (Appl (BoundVar 1, BoundVar 0),
          Appl (BoundVar 0, BoundVar 2)))))  ] 
          
(*    let tests
      = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal (read term) res) inputs
  end 
*)

(** * A simple printer *)

let gensym =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c

(* TODO: use user-provided variable names in abstractions. *)
(* TODO: use [gensym] instead of threading [i] *)
let rec lambda_term_to_Sexpr t l = 
  match t with 
    | DefVar v -> v 
    | FreeVar v -> v 
    | BoundVar v -> List.nth l v 
    | Abs (var,x) -> 
       "(lambda " ^ var ^ " " ^ lambda_term_to_Sexpr x (var::l) ^ ")"
    | Appl(x,y) -> 
       "(" ^ lambda_term_to_Sexpr x l  ^ " " ^ lambda_term_to_Sexpr y l ^ ")"
    | True -> "true"
    | False -> "false" 
    | IfThenElse (x,y,z) -> 
       "(if " ^ lambda_term_to_Sexpr x l ^ lambda_term_to_Sexpr x l ^ lambda_term_to_Sexpr x l ^ ")"
    | Zero -> "zero"
    | Succ n-> "(succ " ^ lambda_term_to_Sexpr n l ^ ")"
    | Iter(n,f,a) -> 
       "(iter " ^ lambda_term_to_Sexpr n l ^ lambda_term_to_Sexpr f l ^ lambda_term_to_Sexpr a l ^ ")"
    | Let (t, b) -> let var = gensym() in 
		    "(let (" ^ var ^ " " ^ lambda_term_to_Sexpr t l ^ ") " ^ lambda_term_to_Sexpr b (var::l) ^ ")"
    | _-> failwith "later"

module PrettyT =
  struct
    (* TODO: write some tests. In particular, check that one can
       [read] the lambda terms we pretty-print. *)
    let compare_term a b = 
      Sexp.of_string a = Sexp.of_string b
    
(*    let inputs = 
      [ (Abs("x",BoundVar 0),"(lambda x x)") ;
 	(Let (Abs("x",BoundVar 0),BoundVar 0),"(let (x1 (lambda x x)) x1)");       
 	(Let (Abs ("x",BoundVar 0),
          Let (Abs ("x",Abs ("y",BoundVar 1)),
          Let (Appl (BoundVar 1, BoundVar 0),
               Appl (BoundVar 0, BoundVar 2)))),"(let (x2 (lambda x x)) (let (x3 (lambda x (lambda y x))) (let (x4 (x2 x3)) (x4 x2))))"); 
      ]

	
    let tests = List.map (fun (term, res) -> "test" >:: fun ctxt -> assert_equal (compare_term (lambda_term_to_Sexpr term []) res) true) inputs
*)
  end

(** * Reduction *)

(** ** substitution *)

(*=substitution *)
let rec substitution term var tsub 
    = match term with 
    | FreeVar v -> FreeVar v 
    | BoundVar v when v = var -> tsub
    | BoundVar v -> BoundVar v
    | Abs (va,x) -> Abs (va,(substitution x (var+1) tsub))
    | Appl (x,y) -> Appl (substitution x var tsub,
                          substitution y var tsub)
    (*=End *)
    | Let (t, b) -> Let((substitution t var tsub),(substitution b (var+1) tsub))
    | DefVar v -> DefVar v 
(*=bool_substitution *)
    | True -> True
    | False -> False
    | IfThenElse (x,y,z) -> 
       IfThenElse (substitution x var tsub,
		   substitution y var tsub,
		   substitution z var tsub)
(*=End *)
(*=nat_substitution *)
    | Zero -> Zero
    | Succ(n) -> Succ(substitution n var tsub)
    | Iter(n,f,a) -> Iter(substitution n var tsub,
                          substitution f var tsub,
                          substitution a var tsub)
    | _ -> failwith "later"
(*=End *)


module SubstitutionT =
  struct
    
(*    let inputs = 
      [
	("(lambda x x)",(DefVar "y"),"(lambda x y)");
(*	("(lambda x (let (id (lambda x x)) (x x)))",(DefVar "y"), "(lambda x (let (id (lambda x x)) (y y)))"); *)
      ]
    
      let tests = List.map (fun (term,sub,res) -> "testsub" >:: fun ctxt -> assert_equal (substitution (read term) (-1) sub) (read res)) inputs *)

  end

let alpha_equiv terme1 terme2 = 
  (* XXX: this is true as long as we do not put debug info in the
          lambda term. Careful if we don't. *)
  terme1 = terme2

module AlphaEquivT =
  struct

    (* TODO: write some tests. In particular, make sure that [(lambda
       x x)] and [(lambda y y)] are equal but that [(lambda (x y) y)]
       is not equal to [(lambda (x y) x)]. *)
    let tests = ["alpha equivalence" >:: 
                 (fun _ -> todo "To be implemented";
                           assert_bool "" false)]

  end

(** ** beta-reduction *)

(*=reduction *)
let beta t 
    = match t with
    | Appl(Abs(var,x),y) -> Some (substitution x 0 y)
    | _ -> None
(*=End *)
(*    | Let(t, b) -> Some (substitution b 0 t)*)

(*=iota_sig *)
let iota t 
  = match t with
(*=End *)
(*=bool_evaluation *)
  | IfThenElse (True, y, z) -> Some y
  | IfThenElse (False, y, z) -> Some z
(*=End *)
(*=nat_evaluation *)
    | Iter(Zero,f,a) -> Some a
    | Iter(Succ num, f, a) -> Some (Iter(num,f,(Appl(f, a))))
(*=End *)
    (*=pair_evaluation *)    
    |Pi0(Pair(x,y)) -> Some x
    |Pi1(Pair(x,y)) -> Some y
(*=End *)
  | _ -> None

let delta env t =
  match t with
  | DefVar x ->
    begin
      try
        Some (List.assoc x env)
      with 
        Not_found -> None
    end
  | _ -> None

let reduction env t =
  match beta t with
  | None -> 
    begin
      match iota t with
      | None -> delta env t
      | mt -> mt
    end
  | mt -> mt

(*=evaluation_sig *)
let evaluation env t  =
  let rec eval t =
    match t with
    (*=End *)
  (*=evaluation *)
    | Appl(f, v) -> 
      let vf = eval f in
      try_reduction (Appl(vf, v))
    (*=End *)
    (*=evaluation_pair *)
    | Pair(x,y) -> Pair((try_reduction x),(try_reduction y))
    (*=End *)
    (*=evaluation_bis *)
    | x ->
       try_reduction x

  and try_reduction t = 
    match reduction env t with
    | Some t' -> eval  t'
    | None -> t
  in
  eval t
(*=End *)

module EvalT =
  struct

(*    (* TODO: write some very basic tests about beta reduction, iota
       reduction and evaluation. *)
    let tests = ["eval" >:: 
                 (fun _ -> todo "To be implemented";
                           assert_bool "" false)]
*)
  end

module ChurchBooleanT =
  struct
  (*  let env = [("tru", read "(lambda (tru fls) tru)");
               ("fals", read "(lambda (tru fls) fls)");
               ("ift", read "(lambda (b ifTru ifFls) (b ifTru ifFls))");]


    let tests = ["ifthenelse" >:: fun ctxt -> 
                   assert_equal (evaluation env (read "(ift fals y x)"))
      (DefVar "x")] *)
  end


(** * Reduction forte *)

(** Nous supposons ici que le terme est fortement normalisant. *)


(* TODO: faire converge la version dans [typed] et celle-ci puis
   supprimer la version dans [typed] code. *)

let rec bind i bv t =
  match t with 
  | BoundVar v -> BoundVar v
  | FreeVar v when v = i -> BoundVar bv
  | FreeVar v -> FreeVar v
  | DefVar v -> DefVar v
  | Abs(var,x) -> Abs(var,(bind i (bv + 1) x))
  | Appl(x,y) -> Appl(bind i bv x,bind i bv y)
  | True -> True
  | False -> False
  | IfThenElse(x,y,z) -> IfThenElse(x,y,z)
  | Zero -> Zero 
  | Succ(n) -> Succ(bind i bv n)
  | Iter(n,f,a) -> Iter((bind i bv n),(bind i bv f),(bind i bv a))
  | _ -> failwith "later"

(*=reduction_forte *)
let reduction_forte env t 
  = 
  let rec eval t =
    match t with 
    | Appl(f, v) -> 
      let vf = eval f in
      let vv = eval v in
      try_reduction (Appl(vf, vv))
    | x ->
      try_reduction x
  and try_reduction t = 
    match reduction env t with
    | Some t' -> eval  t'
    | None -> t
  in
  eval t
(*=End *)

(*
let rec reduction_forte env t  = 
  match t with 
    | FreeVar v -> FreeVar v
    | DefVar v -> DefVar v
    | BoundVar v -> BoundVar v
    | Abs x -> 
      let freshName = gensym () in
      let t = reduction_forte (substitution x 0 (FreeVar freshName)) in
      Abs(bind freshName 0 t)
    | Appl(Abs(x),y) -> reduction_forte(substitution x 0 y)
    | Appl(x,y) -> 
       begin 
	 match reduction_forte x with 
	 | FreeVar z -> Appl(x,(reduction_forte y))
	 | Abs z -> reduction_forte (Appl(Abs(z),y))
	 | neutre -> Appl(neutre,reduction_forte y)				   
       end 
    | True -> True
    | False -> False
    | IfThenElse (x,y,z) when x = True -> reduction_forte y
    | IfThenElse (x,y,z) when x = False -> reduction_forte z
    | IfThenElse (x,y,z) -> 
       begin 
	 match reduction_forte x with
	 | True -> reduction_forte y
	 | False -> reduction_forte z 
	 | _ -> IfThenElse(x,y,z)
       end 
    | _ -> failwith "on va la supprimer" 
*)

module NormT =
  struct

   (* (* TODO: write some more tests. *)
    let tests = ["eval" >:: 
                 (fun _ -> todo "To be implemented";
                           assert_bool "" false)]
   *)
  end

module ChurchNatT =
  struct

    let rec church_num n =
      match n with
      | 0 -> BoundVar 0
      | n -> Appl(BoundVar 1,(church_num (n-1)))
		 
    let int_to_lambda_term n =
      Abs("f",Abs("x",church_num n))

    (* Definitions des termes *)

    let env = [("Z", read "(lambda (f x) x)");
               ("S", read "(lambda (n f x) (f (n f x)))");
               ("PLUS", read "(lambda (m n f x) (m f (n f x)))")]

    let testsucc = "(S Z)"
    let plus_test = "(PLUS (S (S Z)) (S (S Z)))"

(*    let test3 test_ctxt = assert_equal
        (reduction_forte env (read testsucc))
        (reduction_forte env (read "(S 0)"))
    let test4 test_ctxt = assert_equal
        (reduction_forte env (read plus_test))
      (reduction_forte env (read "(S (S (S 0)))")) *)

(*    let tests = 
      ["test 3">:: test3;
      "test 4">:: test4 ] *)
end 
end

    
(** * Test suite *)
(*
let suite =
  test_list [ "Parser tests" >::: ParserT.tests
            ; "Pretty-printer test" >::: PrettyT.tests 
            ; "Substitution test" >::: SubstitutionT.tests
            ; "Alpha equivalence test" >::: AlphaEquivT.tests
            ; "Evaluation test" >::: EvalT.tests 
            ; "Boolean test" >::: ChurchBooleanT.tests 
            ; "Normalization test" >::: NormT.tests 
            ; "Nat test" >::: ChurchNatT.tests ]
     
let () =
  run_test_tt_main suite *)


(* TODO: resurect those tests *)
(* 
let test1 test_ctxt = assert_equal Appl(Abs(BoundVar 0),FreeVar v) (Lambda_calcul.evaluation (FreeVar v));;
let test2 test_ctxt = assert_equal Appl(Abs(BoundVar 0),Abs(BoundVar 0)) (Lambda_calcul.evaluation (Abs(BoundVar 0)));;
let test3 test_ctxt = assert_equal (relie_libre 1 0 (Abs(Abs(Appl((FreeVar "1"),FreeVar "0"))))) (Abs(Abs(Abs(Appl((BoundVar 2),FreeVar "0")))))

let eval = 
"eval">:::
["test 1">:: test1;
 "test 2">:: test2;
 "test 3">:: test3]

;;
let () = 
  run_test_tt_main eval

;;


(* 
(*test pour la fonction relie libre *)

let x = Abs(Abs(Appl((FreeVar "4"),FreeVar "0")))
let () = Printf.printf "%s \n" (lambda_term_to_string(x))
let () = Printf.printf "%s \n" (lambda_term_to_string(Abs(relie_libre 4 0 x)))
let y = Abs(Abs(Appl(FreeVar "1",Appl(FreeVar "0",BoundVar 0)))) 

 *)
*)
