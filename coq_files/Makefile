OBJ:= who_map.vo tactics.vo simple_map.vo WhoMap.vo WhoArray.vo WhoArith.vo WhoList.vo WhoTuples.vo

all: $(OBJ)

%.vo: %.v
	coqc $<

WhoArray.v: WhoArith.vo

%.v.vd: %.v
	coqdep -I . $< > $@

include $(OBJ:.vo=.v.vd)

.PHONY:clean

clean:
	rm -f *.vo *.glob *.v.vd

