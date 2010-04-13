
all: memo_const

%: %.who
	who-vcg $*.who
	rm -f $*_who*.why
	pangoline --desectionize $*_who.pge
	proveit.sh $*_who*.why
