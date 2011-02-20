
.PHONY: ocaml clean install uninstall

ocaml:
	ocamlbuild ocaml.otarget

clean:
	ocamlbuild -clean

install: ocaml
	cp --remove-destination ocaml/META _build/ocaml/META
	echo "linkopts += \" -cclib -lcamlidl -cclib -L`ocamlfind query camlidl`\"" >> _build/ocaml/META
	ocamlfind install Z3 _build/ocaml/META _build/ocaml/z3.cmxa _build/ocaml/z3.cma _build/ocaml/*.a _build/ocaml/*.cmi -nodll lib/libz3.so

uninstall:
	ocamlfind remove Z3
