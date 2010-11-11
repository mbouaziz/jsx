
OCBOPTIONS=-j 2 -classic-display

.PHONY: all jsx clean web clean-web

all: jsx

jsx:
	ocamlbuild $(OCBOPTIONS) -lflags -ccopt,-static jsx.native

clean:
	ocamlbuild $(OCBOPTIONS) -clean

web: jsx
	mkdir web/_install
	ocamlbuild $(OCBOPTIONS) web/genoptions.native
	./genoptions.native > web/_install/bool_options.php5
	cp _build/jsx.native web/_install/
	cp web/*.php5 web/_install/
	cp symbolic.es5 ../lambdaJS/data/es5-lib.es5 web/_install/

clean-web:
	rm -rf web/_install
