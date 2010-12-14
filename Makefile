
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
	cp web/*.php5 web/*.js web/_install/
	cp symbolic.es5 ../lambdaJS/data/es5-lib.es5 web/_install/
	mkdir web/_install/samples
	mv web/_install/Documentation.js web/_install/samples
	ln -fs ../../../tests/with-symbols web/_install/samples/A
	ln -fs ../../../tests/bugs web/_install/samples/bugs
	ln -fs ../../../../lambdaJS/tests/eval_es5 web/_install/samples/.eval_es5
	ln -fs ../../../../lambdaJS/tests/parse web/_install/samples/.parse_js
	ln -fs ../../../../lambdaJS/tests/ES5conform/TestCases web/_install/samples/ES5conform

clean-web:
	rm -rf web/_install
