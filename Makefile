prefix=/usr/local
datarootdir = ${prefix}/share
datadir = ${datarootdir}
COQPRESENT:=yes
COQLIB:=/usr/local/lib/coq
exec_prefix=${prefix}
BINDIR=${exec_prefix}/bin
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

ifeq ($(COQPRESENT),yes)
install: main.native $(COQTARGETS)
	cp -f _build/src/main.native $(BINDIR)/who-vcg
	cp -f $(COQTARGETS) $(COQFILES) $(COQLIB)/user-contrib/

else
install: main.native
	cp -f _build/src/main.native $(BINDIR)/who-vcg
endif

uninstall:
	rm -f $(BINDIR)/who-vcg
	rm -f $(COQLIB)/user-contrib/WhoMap.v*


tags:
	otags -o TAGS $(ALLML)

documentation:
	$(OCAMLBUILD) -documentation

Makefile version.ml: Makefile.in version.ml.in config.status
	./config.status
	chmod a-w Makefile version.ml

config.status: configure
	./config.status --recheck

configure: configure.in
	autoconf

dist-clean: clean
	rm -f Makefile configure config.status version.ml
	rm -rf autom4te.cache
