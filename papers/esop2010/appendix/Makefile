pdf: appendix-pp.pdf
dvi: appendix-pp.dvi

%.pdf: %.tex
	pdflatex $^
	pdflatex $^

%.dvi: %.tex
	latex $^
	latex $^

uproc: uproc.ml
	ocamlopt -o uproc $^

%.ml : %.mll
	ocamllex $^

%-pp.tex : %.tex uproc
	./uproc < $< > $@

clean:
	rm -f *.dvi *.log *.aux *.log appendix-pp.tex uproc
	rm -f *.o *.cmx *.cmi uproc.ml
