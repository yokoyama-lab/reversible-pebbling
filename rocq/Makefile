# kappa*, the rho_c value layer, the derivative-free beta bracket, and
# the E-branch of the profile (Rocq + CoqInterval).  See README.md.
ROCQ ?= rocq
FLAGS = -Q . RevPebblingRocq

all: KappaStar.vo RhoEnclose.vo LedgerParam.vo EnvelopeE.vo

KappaStar.vo: KappaStar.v
	$(ROCQ) c $(FLAGS) $<

RhoEnclose.vo: RhoEnclose.v KappaStar.vo
	$(ROCQ) c $(FLAGS) $<

LedgerParam.vo: LedgerParam.v RhoEnclose.vo
	$(ROCQ) c $(FLAGS) $<

EnvelopeE.vo: EnvelopeE.v LedgerParam.vo
	$(ROCQ) c $(FLAGS) $<

check: all
	$(ROCQ) c $(FLAGS) Check.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all check clean
