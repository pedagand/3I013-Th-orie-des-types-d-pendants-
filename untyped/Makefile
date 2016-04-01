all : lambda_calcul

lambda_calcul: lambda.ml
	ocamlbuild -use-ocamlfind lambda.native

test.native: test.ml
	ocamlbuild -use-ocamlfind test.native

nat.native: nat.ml
	ocamlbuild -use-ocamlfind nat.native

clean: 
	ocamlbuild -clean
