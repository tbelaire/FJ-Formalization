# COQC := /usr/local/Cellar/coq/my-coq/bin/coqc
# COQC := /usr/local/Cellar/coq/8.5/bin/coqc
COQC := /usr/local/Cellar/coq/8.4pl6_1/bin/coqc

COQ_SOURCES := $(wildcard *.v)

all: FJ_Definitions.vo

dep.mk: ${COQ_SOURCES}
	coqdep -I . $^ > $@

-include dep.mk

%.vo : %.v
	${COQC} $<

clean:
	-rm *.vo *.glob dep.mk


.PHONY : all clean
