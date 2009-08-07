OCAMLBUILD := ocamlbuild -classic-display

ALLML := $(wildcard *.ml *.mly *mll *.mli)

all: main.native

%.native: $(ALLML)
	$(OCAMLBUILD) $@

check:
	make -C tests check

clean:
	$(OCAMLBUILD) -clean
