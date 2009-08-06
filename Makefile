OCAMLBUILD := ocamlbuild -classic-display

ALLML := $(wildcard *.ml *.mly *mll *.mli)

all: main.native

%.native: $(ALLML)
	$(OCAMLBUILD) $@
