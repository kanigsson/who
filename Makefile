OCAMLBUILD := ocamlbuild -classic-display
COQVO := WhoMap.vo WhoArith.vo WhoArray.vo
COQV := $(COQVO:.vo=.v)
COQTARGETS := $(addprefix coq_files/, $(COQVO))
COQFILES := $(addprefix coq_files/, $(COQV))


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

$(COQFILES):
	make -C coq_maps

install: main.native $(COQFILES)
	cp -f _build/main.native /usr/local/bin/pwho
	cp -f $(COQTARGETS) $(COQFILES) /usr/local/lib/coq/user-contrib/

uninstall:
	rm -f /usr/local/bin/pwho
	rm -f /usr/local/lib/coq/user-contrib/WhoMap.v*

