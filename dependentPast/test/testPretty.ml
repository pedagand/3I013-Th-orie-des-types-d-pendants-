open OUnit2
open Sexplib
open Lambda
 

(* We compare pretty-printed strings based on the tokens (ignoring spacing) *)
let compare_term a b = 
  Sexp.of_string a = Sexp.of_string b


let inputs = 
  [ 
    ((Abs("x",Abs("y",Abs("z",Inv(Appl(BVar 2, Inv(Appl(BVar 1, Inv(BVar 0))))))))),"(lambda x (lambda y (lambda z (x (y z)))))");
    ((Inv(Ann(Abs("x",Inv(BVar 0)),Pi("x",Star,Star)))),"(: (lambda x x) (pi x * *))");
    ((Pi("x",Star,Pi("y",Star,Pi("z",Star,Star)))),
     "(pi x * (pi y * (pi z * *)))");
    ((Succ(Succ(Zero))),"(succ (succ zero))");
    ((Inv(Iter(Nat,Nat,Nat,Nat))),"(iter N N N N)");
    ((Pair(Inv(FVar "x"),Inv(FVar "y"))),"(x , y)");
    ((Cross(Inv(FVar "x"),Inv(FVar "y"))),"(x X y)");
    (Inv(P0(Ann(Pair(Inv(FVar "a"),Inv(FVar "b")),Cross(Nat,Nat)))),"(p0 (: (a , b) (N X N)))");
    (Inv(P1(Ann(Pair(Inv(FVar "a"),Inv(FVar "b")),Cross(Nat,Nat)))),"(p1 (: (a , b) (N X N)))");
    (Cons(Nat,Zero,Nil(Nat)),"(cons N zero (nil N))");
    (List(Nat),"(list N)");
    (Nil(Nat),"(nil N)");
  ]

let tests = List.map (fun (term, res) -> "test" >:: fun ctxt -> assert_equal (compare_term (pretty_print_inTm term []) res) true) inputs
