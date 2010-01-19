OCAMLBUILD := ocamlbuild -classic-display -X papers -tag debug
COQVO := WhoMap.vo WhoArith.vo WhoArray.vo WhoList.vo
COQV := $(COQVO:.vo=.v)
COQTARGETS := $(addprefix coq_files/, $(COQVO))
COQFILES := $(addprefix coq_files/, $(COQV))


ALLML := $(wildcard src/*.ml src/*.mly src/*mll src/*.mli)

all: main.native

%.native: $(ALLML)
	$(OCAMLBUILD) $@

%.cmo: $(ALLML)
	$(OCAMLBUILD) $@
debug:
	$(OCAMLBUILD) -tag debug main.byte

check:
	make -C tests check

clean:
	$(OCAMLBUILD) -clean

coqfiles: $(COQTARGETS)

$(COQTARGETS): $(COQFILES)
	make -C coq_files

install: main.native $(COQTARGETS)
	cp -f _build/main.native /usr/local/bin/pwho
	cp -f $(COQTARGETS) $(COQFILES) /usr/local/lib/coq/user-contrib/

uninstall:
	rm -f /usr/local/bin/pwho
	rm -f /usr/local/lib/coq/user-contrib/WhoMap.v*


tags:
	otags -o TAGS *.ml

documentation:
	$(OCAMLBUILD) -documentation
