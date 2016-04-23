open OUnit2
open Lambda


let test1x = (Pi(Global "A",Star,Pi(Global "B",(Pi (Global "x", Inv(BVar 0),Star)),Pi(Global "C",(Pi (Global "x", Inv(BVar 1),Star)), (Pi (Global "1",(Pi (Global "2", (Pi(Global "a",Star,Pi(Global "b",(Inv(Appl(BVar 2 ,Inv(BVar 1)))),Inv(Appl(BVar 2, Inv(BVar 1)))))),(Pi (Global "a",Inv(BVar 3),Inv(Appl(BVar 3,Inv(BVar 0))))))),(Pi (Global "a",Inv(BVar 3),Inv(Appl(BVar 2,Inv(BVar 0)))))))))))

let test1y = "(pi A * (pi B (pi x A *) (pi C (pi x A *) (pi 1 (pi 2 (pi a * (pi b (B a) (C a))) (pi a A (B a))) (pi a A (C a))))))"

let inputs
    = [("(lambda x x)", Abs(Global("x"),Inv(BVar 0)));
       ("(lambda x y)", Abs(Global("x"),Inv(FVar(Global("y")))));
       ("(x y z)", 
	Inv(Appl(Appl(FVar (Global"x"), Inv(FVar (Global "y"))), Inv(FVar (Global "z")))));
       ("(lambda (x y z) (x (y z)))", Abs((Global "x"),Abs((Global "y"),Abs((Global "z"),Inv(Appl(BVar 2, Inv(Appl(BVar 1, Inv(BVar 0)))))))));
       ("(lambda (x y z) (x y z))", Abs(Global "x",Abs(Global "y",Abs(Global "z",Inv(Appl (Appl (BVar 2, Inv(BVar 1)), Inv(BVar 0)))))));
       ("((: (lambda x x) *) y)", Inv(Appl(Ann(Abs(Global("x"),Inv(BVar 0)),Star),Inv(FVar (Global "y")))));
       ("((: (lambda x x) (-> N N)) y)",Inv(Appl(Ann(Abs(Global "x",Inv(BVar 0)),Pi(Global "NO",Nat,Nat)),Inv(FVar (Global "y")))));
       ("(pi x * *)",Pi(Global "x",Star,Star));
       ("(pi x (pi y * *) *)", Pi(Global "x",Pi(Global "y",Star,Star),Star));
       ("(pi (x y z) * (lambda w w))",Pi(Global "x",Star,Pi(Global "y",Star,Pi(Global "z",Star,Abs(Global "w",Inv(BVar 0))))));
       ("(pi A * (pi B (pi x A *) *))",Pi(Global "A",Star,Pi(Global "B",(Pi (Global "x" ,Inv(BVar 0), Star)),Star)));
       ("(-> * *)",Pi(Global "NO",Star,Star));
       ("(succ (succ zero))",Succ(Succ(Zero)));
       ("(: (succ zero) N)",Inv(Ann(Succ(Zero),Nat)));
       ("(iter N N N N)",Inv(Iter(Nat,Nat,Nat,Nat)));
       ("(iter (lambda x N) (succ (succ zero)) (lambda n (lambda x (succ x))) zero)",Inv(Iter(Abs(Global "x",Nat),Succ(Succ Zero),Abs(Global "n",Abs(Global "x",Succ (Inv (BVar 0)))),Zero)));
       ("(pi P (-> A *) (-> (P a) (P b)))", 
	Pi(Global "P",Pi(Global "NO",Inv(FVar (Global "A")),Star),Pi(Global "NO",Inv(Appl(BVar 0,Inv(FVar (Global"a")))),Inv(Appl(BVar 1,Inv(FVar (Global"b")))))));
       ("(lambda A (lambda a (lambda b (pi P (-> A *) (-> (P a) (P b))))))",
	Abs(Global "A",Abs(Global "a",Abs(Global "b",(Pi(Global "P",Pi(Global "NO",Inv(BVar 2),Star),Pi(Global "NO",Inv(Appl(BVar 0,Inv(BVar 2))),Inv(Appl(BVar 1,Inv(BVar 2))))))))));
       ("(a X b)",Cross(Inv(FVar (Global "a")),Inv(FVar (Global"b"))));
       ("(a , b)",Pair(Inv(FVar (Global "a")),Inv(FVar (Global"b"))));
       ("(p0 (: (a , b) (N X N)))", 
	Inv(P0(Ann(Pair(Inv(FVar (Global "a")),Inv(FVar (Global "b"))),Cross(Nat,Nat)))));
       ("(p1 (: (a , b) (N X N)))", 
	Inv(P1(Ann(Pair(Inv(FVar (Global "a")),Inv(FVar (Global "b"))),Cross(Nat,Nat)))));
       ("(iter (lambda x x) zero (lambda x (succ x)) zero)",
	Inv(Iter(Abs(Global "x",Inv(BVar 0)),Zero,Abs(Global "x",Succ(Inv(BVar 0))),Zero)));
       ("(list N)",List(Nat));
       ("(nil N)", Nil(Nat));
       ("(cons N zero (nil N))",(Cons(Nat,Zero,Nil(Nat))));
       ("(vec N (succ zero))",Vec(Nat,Succ(Zero)));
       ("(dnil N)",DNil(Nat));
       ("(dcons zero (dnil N))",DCons(Zero,DNil(Nat)));
       ("(dfold alpha P m xs f a)",Inv(DFold(Inv(FVar(Global "alpha")),Inv(FVar(Global "P")),Inv(FVar(Global "m")),Inv(FVar(Global "xs")),Inv(FVar(Global "f")),Inv(FVar(Global "a")))));
       ("?",What);      
       ("(lambda x ?)",Abs(Global("x"),What));
       ("(id N zero (succ zero))", Id(Nat,Zero,Succ(Zero)));
       ("(refl zero)",Refl(Zero));
       ("(trans N N N N N N)",Inv(Trans(Nat,Nat,Nat,Nat,Nat,Nat)));
(*        ("(pi A * (pi a A (pi b A (-> (id A a b) (id A b a)))))", Nat);
       ("(lambda (A a b q) (trans A (lambda (a b q) (id A b a)) a b q (lambda a (refl a))))", Nat); *)
       ("(+ (succ (succ zero)) (succ (succ zero)))", Inv(Appl(Appl(Ann((read "(lambda n_plus (lambda a_plus (iter (lambda x_plus N) n_plus (lambda ni_plus (lambda x_plus (succ x_plus))) a_plus)))")
	   ,(read "(-> N (-> N N))")),(Succ(Succ Zero))),(Succ(Succ Zero)))));
       
      (* ( (pretty_print_inTm test1x []),(test1x)); *)
      (* (test1y),(test1x) ;*)]
	



let tests
    = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal ~printer:(fun a -> pretty_print_inTm a []) (read term) res) inputs

