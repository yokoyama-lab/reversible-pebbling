# The kappa* enclosure (Rocq + CoqInterval).  See README.md.
ROCQ ?= rocq
FLAGS = -Q . RevPebblingRocq

all: KappaStar.vo

KappaStar.vo: KappaStar.v
	$(ROCQ) c $(FLAGS) $<

check: KappaStar.vo
	$(ROCQ) c $(FLAGS) Check.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all check clean
