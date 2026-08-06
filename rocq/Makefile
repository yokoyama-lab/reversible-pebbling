# kappa*, the rho_c value layer, the beta bracket, the E-branch, rho_c as
# a differentiable function, the window slope enclosure, the ledger, and
# the generated cover of Zone I's slope range (Rocq + CoqInterval).
# See README.md.
ROCQ ?= rocq
FLAGS = -Q . RevPebblingRocq

# The cover is generated (gen/gencover.py) and split into mutually
# independent parts, so `make -j8` builds them in parallel.  Wildcarding
# keeps this list from drifting out of step with what the generator wrote.
COVER_V  := $(sort $(wildcard LedgerCoverP*.v))
COVER_VO := $(COVER_V:.v=.vo)

all: KappaStar.vo RhoEnclose.vo LedgerParam.vo EnvelopeE.vo RhoDeriv.vo \
     SlopeWindow.vo LedgerA.vo CoverGlue.vo $(COVER_VO) LedgerCover.vo

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

CoverGlue.vo: CoverGlue.v LedgerA.vo
	$(ROCQ) c $(FLAGS) $<

$(COVER_VO): %.vo: %.v CoverGlue.vo
	$(ROCQ) c $(FLAGS) $<

LedgerCover.vo: LedgerCover.v $(COVER_VO)
	$(ROCQ) c $(FLAGS) $<

check: all
	$(ROCQ) c $(FLAGS) Check.v

# Regenerate the cover from scratch (needs python3 with mpmath).
# The arguments are: slope range, the margin each window's ledger
# enclosure must clear, the output directory, and the windows per part.
PYTHON ?= python3
cover:
	rm -f LedgerCoverP*.v LedgerCoverP*.vo LedgerCover.v LedgerCover.vo
	cd gen && $(PYTHON) gencover.py 1.45 3.25 0.001 .. 40

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all check clean cover
