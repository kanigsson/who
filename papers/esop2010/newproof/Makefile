main: newproof-pp.dvi

dvi: newproof-pp.dvi
pdf: newproof-pp.pdf

%.dvi : %.tex 
	latex $^
	latex $^

%.pdf : %.tex
	pdflatex $^
	pdflatex $^

%-pp.tex : %.tex uproc
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
