
all: clean map_fold

%: %.who
	who-vcg $*.who
	for i in $**_who.pge; do pangoline --desectionize $$i; done
	proveit.sh $**_who.why


clean:
	rm -f *.pge *.why
