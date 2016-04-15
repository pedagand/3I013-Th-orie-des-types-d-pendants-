open OUnit2
open Sexplib
open Lambda
 

(* We compare pretty-printed strings based on the tokens (ignoring spacing) *)
let compare_term a b = 
  Sexp.of_string a = Sexp.of_string b


let inputs = 
  [ ((Abs(Global"x",Inv(BVar 0))),"(lambda x x)");
    ((Abs(Global "x",Abs(Global "y",Abs(Global "z",Inv(Appl(BVar 2, Inv(Appl(BVar 1, Inv(BVar 0))))))))),"(lambda x (lambda y (lambda z (x (y z)))))");
    ((Inv(Ann(Abs(Global "x",Inv(BVar 0)),Pi(Global "x",Star,Star)))),"(: (lambda x x) (pi x * *))");
    ((Pi(Global "x",Star,Pi(Global "y",Star,Pi(Global "z",Star,Star)))),
     "(pi x * (pi y * (pi z * *)))");
    ((Succ(Succ(Zero))),"(succ (succ zero))");
    ((Inv(Iter(Nat,Nat,Nat,Nat))),"(iter N N N N)");
    ((Pair(Inv(FVar (Global "x")),Inv(FVar (Global "y")))),"(x , y)");
    ((Cross(Inv(FVar (Global "x")),Inv(FVar (Global "y")))),"(x X y)");
    (Inv(P0(Ann(Pair(Inv(FVar (Global "a")),Inv(FVar (Global "b"))),Cross(Nat,Nat)))),"(p0 (: (a , b) (N X N)))");
    (Inv(P1(Ann(Pair(Inv(FVar (Global "a")),Inv(FVar (Global "b"))),Cross(Nat,Nat)))),"(p1 (: (a , b) (N X N)))");
    (Cons(Nat,Zero,Nil(Nat)),"(cons N zero (nil N))");
    (List(Nat),"(list N)");
    (Nil(Nat),"(nil N)");
    (Inv(DFold(Inv(FVar(Global "alpha")),Inv(FVar(Global "P")),Inv(FVar(Global "m")),Inv(FVar(Global "xs")),Inv(FVar(Global "f")),Inv(FVar(Global "a")))),"(dfold alpha P m xs f a)");
    (DCons(Zero,DNil(Nat)),"(dcons zero (dnil N))");
    (DNil(Nat),"(dnil N)");
    (Inv(DFold(Nat,Nat,Nat,Nat,Nat,Nat)),"(dfold N N N N N N)");
    (Vec(Nat,Succ(Zero)),"(vec N (succ zero))");
    (What,"?");
    (Abs(Global"x",What),"(lambda x ?)");
    (Id(Nat,Zero,Succ(Zero)),"(id N zero (succ zero))");
    (Refl(Zero),"(refl zero)");
    (Inv(Trans(Nat,Nat,Nat,Nat,Nat,Nat)),"(trans N N N N N N)");
  ]

let tests = List.map (fun (term, res) -> "test" >:: fun ctxt -> assert_equal (compare_term (pretty_print_inTm term []) res) true) inputs
