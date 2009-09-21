OBJ:= who_map.vo tactics.vo simple_map.vo WhoMap.vo WhoArith.vo WhoArray.vo

all: $(OBJ)

%.vo: %.v
	coqc $<

WhoArray.v: WhoArith.vo

clean:
	rm -f *.vo *.glob
#.depend:
#	coqdep $(OBJ:.vo=.v) > .depend
#
#include .depend
