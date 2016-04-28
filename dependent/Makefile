all : lambda_calcul

lambda_calcul: lambda.ml
	ocamlbuild -use-ocamlfind lambda.native

nat: nat.ml
	ocamlbuild -use-ocamlfind nat.native

test.native: test.ml
	ocamlbuild -use-ocamlfind test.native

%.native: %.ml
	ocamlbuild -use-ocamlfind $@

clean: 
	ocamlbuild -clean


