open OUnit2
open Lambda

let inputs
    = [("(lambda x x)", Abs("x",Inv(BVar 0)));
       ("(lambda x y)", Abs("x",Inv(FVar "y")));
       ("(x y z)", Inv(Appl(Appl(FVar "x", Inv(FVar "y")), Inv(FVar "z"))));
       ("(lambda (x y z) (x (y z)))", Abs("x",Abs("y",Abs("z",Inv(Appl(BVar 2, Inv(Appl(BVar 1, Inv(BVar 0)))))))));
       ("(lambda (x y z) (x y z))", Abs("x",Abs("y",Abs("z",Inv(Appl (Appl (BVar 2, Inv(BVar 1)), Inv(BVar 0)))))));
       ("((: (lambda x x) N) y)", Inv(Appl(Ann(Abs("x",Inv(BVar 0)),Nat),Inv(FVar "y"))));
       ("(iter (succ zero) (lambda x x) y)", Inv(Iter((Succ(Zero)),(Abs("x",Inv(BVar 0))),FVar "y")));
       ("((: (lambda (x) (x)) (-> (-> B B) (-> B B))) (lambda (y) (y)))",Inv(Appl(Ann(Abs("x",Inv(BVar 0)),Fleche(Fleche(Bool,Bool),Fleche(Bool,Bool))),(Abs("y",(Inv(BVar 0)))))));
       ("(, (lambda x x) zero )",Pair(Abs("x",Inv(BVar 0)),Zero));
       ("(: (lambda x x) (* B B))",Inv(Ann(Abs("x",Inv(BVar 0)),Croix(Bool,Bool))));
      ("(ifte true (: (, true false) (* B B)) y)",Inv(Ifte(True,Ann((Pair(True,False)),(Croix(Bool,Bool))),FVar "y")))]

let tests
    = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal (read term) res) inputs
