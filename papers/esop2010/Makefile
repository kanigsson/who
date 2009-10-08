main: main-pp.dvi

dvi: main-pp.dvi
pdf: main-pp.pdf

%.dvi : %.tex biblio.bib
	latex $^
	bibtex $*
	latex $^
	latex $^

%.pdf : %.tex biblio.bib
	pdflatex $^
	bibtex $*
	pdflatex $^
	pdflatex $^

%-pp.tex : %-proc.tex uproc
	./uproc < $< > $@

%-proc.tex : %.tex pp
	./pp < $< > $@

%.ml : %.mll
	ocamllex $^

uproc: uproc.ml
	ocamlopt -o uproc $^

pp: pp.ml
	ocamlopt -o pp $^

.PHONY:clean

clean:
	rm -f *.dvi *.log *.aux *.log main-pp.tex main-proc.tex uproc pp
	rm -f *.o *.cmx *.cmi uproc.ml pp.ml
