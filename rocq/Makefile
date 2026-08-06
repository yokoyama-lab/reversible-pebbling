# kappa*, the rho_c value layer, and the derivative-free beta bracket
# (Rocq + CoqInterval).  See README.md.
ROCQ ?= rocq
FLAGS = -Q . RevPebblingRocq

all: KappaStar.vo RhoEnclose.vo LedgerParam.vo

KappaStar.vo: KappaStar.v
	$(ROCQ) c $(FLAGS) $<

RhoEnclose.vo: RhoEnclose.v KappaStar.vo
	$(ROCQ) c $(FLAGS) $<

LedgerParam.vo: LedgerParam.v RhoEnclose.vo
	$(ROCQ) c $(FLAGS) $<

check: all
	$(ROCQ) c $(FLAGS) Check.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all check clean
