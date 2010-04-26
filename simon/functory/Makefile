
all: clean map_fold

%: %.who
	who-vcg $*.who
	for i in $**_who.pge; do pangoline --desectionize $$i; done
	proveit.sh $**_who.why


clean:
	rm -f *.pge *.why

coq: map_fold.who
	who-vcg map_fold.who --coq
	for i in *.v; do echo 'Add LoadPath "../../coq_files/".' > .temp.v; cat $$i >> .temp.v; mv -f .temp.v $$i; done
