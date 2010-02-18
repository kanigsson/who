LATEX:= pdflatex
GOAL: manual.pdf

all: $(GOAL)

%.pdf: %.tex
	$(LATEX) $<
	$(LATEX) $<

clean:
	rm -f *.out *.pdf *.aux *.log
