
all: memo_const

%: %.who
	rm -f $*_who*.why $*_who*.pge 
	who-vcg $*.who
	for i in $**_who.pge; do pangoline --desectionize $$i; done
	proveit.sh $**_who.why
