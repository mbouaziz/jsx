
OCBOPTIONS=-j 2 -classic-display

all:
	ocamlbuild $(OCBOPTIONS) jsx.native

clean:
	ocamlbuild $(OCBOPTIONS) -clean
