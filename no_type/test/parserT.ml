open OUnit2
open Lambda

let inputs
    = [("(lambda x x)", Abs (BoundVar 0));
       ("(lambda x y)", Abs (FreeVar "y"));
       ("(x y z)", Appl (Appl (FreeVar "x", FreeVar "y"), FreeVar "z"));
       ("(lambda (x y z) (x (y z)))", Abs (Abs (Abs (Appl (BoundVar 2, Appl (BoundVar 1, BoundVar 0))))));
       ("(lambda (x y z) (x y z))", Abs (Abs (Abs (Appl (Appl (BoundVar 2, BoundVar 1), BoundVar 0)))))]

let tests
    = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal (read term) res) inputs
