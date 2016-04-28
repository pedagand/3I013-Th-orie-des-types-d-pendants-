open Lambda

let refl = "(lambda (A a b q) (trans A (lambda (a b) (id A b a)) a b q (lambda a (refl a))))"
let type_refl = "(pi A * (pi a A (pi b A (-> (id A a b) (id A b a)))))"

let () = run_check refl type_refl
  
