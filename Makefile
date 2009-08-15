OCAMLBUILD := ocamlbuild -classic-display

ALLML := $(wildcard *.ml *.mly *mll *.mli)

all: main.native

%.native: $(ALLML)
	$(OCAMLBUILD) $@
debug:
	$(OCAMLBUILD) -tag debug main.byte

check:
	make -C tests check

clean:
	$(OCAMLBUILD) -clean

