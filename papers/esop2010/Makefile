main: main-pp.dvi

dvi: main-pp.dvi

%.dvi : %.tex
	latex $^
	bibtex $*
	latex $^
	latex $^

%-pp.tex : %.tex uproc
	./uproc < $< > $@

%.ml : %.mll
	ocamllex $^

uproc: uproc.ml
	ocamlopt -o uproc $^

.PHONY:clean

clean:
	rm -f *.dvi *.log *.aux *.log main-pp.tex
