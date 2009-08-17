ALLTESTFILES := $(wildcard *.lm)

done: $(ALLTESTFILES)
	$(MAKE) -C ../good/parsing $(ALLTESTFILES)
	$(MAKE) -C ../good/infer $(ALLTESTFILES)
	$(MAKE) -C ../good/constr $(ALLTESTFILES)
	$(MAKE) -C ../good/typing $(ALLTESTFILES)
	touch done
