COQC := /usr/local/Cellar/coq/8.5/bin/coqc

COQ_SOURCES := $(wildcard *.v)

all: FJ_Definitions.vo

dep.mk: ${COQ_SOURCES}
	coqdep -I . $^ > $@

-include dep.mk

%.vo : %.v
	${COQC} $<

clean:
	-rm *.vo *.glob


.PHONY : all clean
