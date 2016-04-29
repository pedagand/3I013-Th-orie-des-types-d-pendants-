open Lambda

let function_rapport = "(lambda x (lambda y (ifte x (succ x) (x))))"

let type_function_rapport = "(-> N (-> B N)"

let res = run_check function_rapport type_function_rapport

