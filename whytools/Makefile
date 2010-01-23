whyz3: whyz3.ml
	ocamlbuild -classic-display -no-links whyz3.native
	cp _build/whyz3.native whyz3

install: whyz3
	install whyz3 ~/bin/whyz3

clean:
	rm -f whyz3
