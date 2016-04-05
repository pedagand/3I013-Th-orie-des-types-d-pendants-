open OUnit2
open Lambda


let test1x = (Pi("A",Star,Pi("B",(Pi ("x", Inv(BVar 0),Star)),Pi("C",(Pi ("x", Inv(BVar 1),Star)), (Pi ("1",(Pi ("2", (Pi("a",Star,Pi("b",(Inv(Appl(BVar 2 ,Inv(BVar 1)))),Inv(Appl(BVar 2, Inv(BVar 1)))))),(Pi ("a",Inv(BVar 3),Inv(Appl(BVar 3,Inv(BVar 0))))))),(Pi ("a",Inv(BVar 3),Inv(Appl(BVar 2,Inv(BVar 0)))))))))))

let test1y = "(pi A * (pi B (pi x A *) (pi C (pi x A *) (pi 1 (pi 2 (pi a * (pi b (B a) (C a))) (pi a A (B a))) (pi a A (C a))))))"

let inputs
    = [("(lambda x x)", Abs("x",Inv(BVar 0)));
       ("(lambda x y)", Abs("x",Inv(FVar "y")));
       ("(x y z)", Inv(Appl(Appl(FVar "x", Inv(FVar "y")), Inv(FVar "z"))));
       ("(lambda (x y z) (x (y z)))", Abs("x",Abs("y",Abs("z",Inv(Appl(BVar 2, Inv(Appl(BVar 1, Inv(BVar 0)))))))));
       ("(lambda (x y z) (x y z))", Abs("x",Abs("y",Abs("z",Inv(Appl (Appl (BVar 2, Inv(BVar 1)), Inv(BVar 0)))))));
       ("((: (lambda x x) *) y)", Inv(Appl(Ann(Abs("x",Inv(BVar 0)),Star),Inv(FVar "y"))));
       ("((: (lambda x x) (-> N N)) y)",Inv(Appl(Ann(Abs("x",Inv(BVar 0)),Pi("NO",Nat,Nat)),Inv(FVar "y"))));
       ("(pi x * *)",Pi("x",Star,Star));
       ("(pi x (pi y * *) *)", Pi("x",Pi("y",Star,Star),Star));
       ("(pi (x y z) * (lambda w w))",Pi("x",Star,Pi("y",Star,Pi("z",Star,Abs("w",Inv(BVar 0))))));
       ("(pi A * (pi B (pi x A *) *))",Pi("A",Star,Pi("B",(Pi ("x" ,Inv(BVar 0), Star)),Star)));
       ("(-> * *)",Pi("NO",Star,Star));
       ("(succ (succ zero))",Succ(Succ(Zero)));
       ("(: (succ zero) N)",Inv(Ann(Succ(Zero),Nat)));
       ("(iter N N N N)",Inv(Iter(Nat,Nat,Nat,Nat)));
       ("(pi P (-> A *) (-> (P a) (P b)))",
	Pi("P",Pi("NO",Inv(FVar "A"),Star),Pi("NO",Inv(Appl(BVar 0,Inv(FVar "a"))),Inv(Appl(BVar 1,Inv(FVar "b"))))));
       ("(lambda A (lambda a (lambda b (pi P (-> A *) (-> (P a) (P b))))))",
	Abs("A",Abs("a",Abs("b",(Pi("P",Pi("NO",Inv(BVar 2),Star),Pi("NO",Inv(Appl(BVar 0,Inv(BVar 2))),Inv(Appl(BVar 1,Inv(BVar 2))))))))));
       ("(a X b)",Cross(Inv(FVar "a"),Inv(FVar "b")));
       ("(a , b)",Pair(Inv(FVar "a"),Inv(FVar "b")));
       ("(p0 (: (a , b) (N X N)))", 
	Inv(P0(Ann(Pair(Inv(FVar "a"),Inv(FVar "b")),Cross(Nat,Nat)))));
       ("(p1 (: (a , b) (N X N)))", 
	Inv(P1(Ann(Pair(Inv(FVar "a"),Inv(FVar "b")),Cross(Nat,Nat)))))
      (* ( (pretty_print_inTm test1x []),(test1x)); *)
      (* (test1y),(test1x) ;*)]
	



let tests
    = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal (read term) res) inputs
