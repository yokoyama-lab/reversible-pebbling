# kappa*, the rho_c value layer, the beta bracket, the E-branch, rho_c as
# a differentiable function, and the window slope enclosure
# (Rocq + CoqInterval).  See README.md.
ROCQ ?= rocq
FLAGS = -Q . RevPebblingRocq

all: KappaStar.vo RhoEnclose.vo LedgerParam.vo EnvelopeE.vo RhoDeriv.vo \
     SlopeWindow.vo LedgerA.vo

KappaStar.vo: KappaStar.v
	$(ROCQ) c $(FLAGS) $<

RhoEnclose.vo: RhoEnclose.v KappaStar.vo
	$(ROCQ) c $(FLAGS) $<

LedgerParam.vo: LedgerParam.v RhoEnclose.vo
	$(ROCQ) c $(FLAGS) $<

EnvelopeE.vo: EnvelopeE.v LedgerParam.vo
	$(ROCQ) c $(FLAGS) $<

RhoDeriv.vo: RhoDeriv.v LedgerParam.vo
	$(ROCQ) c $(FLAGS) $<

SlopeWindow.vo: SlopeWindow.v EnvelopeE.vo
	$(ROCQ) c $(FLAGS) $<

LedgerA.vo: LedgerA.v SlopeWindow.vo
	$(ROCQ) c $(FLAGS) $<

check: all
	$(ROCQ) c $(FLAGS) Check.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all check clean
