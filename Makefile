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

coq_maps/WhoMap.vo:
	make -C coq_maps

install: main.native coq_maps/WhoMap.vo
	cp -f _build/main.native /usr/local/bin/pwho
	cp -f coq_maps/WhoMap.vo /usr/local/lib/coq/user-contrib/WhoMap.vo
	cp -f coq_maps/WhoMap.v /usr/local/lib/coq/user-contrib/WhoMap.v

uninstall:
	rm -f /usr/local/bin/pwho
	rm -f /usr/local/lib/coq/user-contrib/WhoMap.v*

