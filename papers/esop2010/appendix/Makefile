dvi: appendix-pp.dvi

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
