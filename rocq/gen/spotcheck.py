#!/usr/bin/env python3
"""Spot-check that each sampled window's slope bracket really contains
-f'(q1), i.e. the window is about the slope it claims to be about.

Non-emptiness (check_tiling.py) rules out the trivial vacuity; this rules
out the subtler one where the bracket is non-empty but sits somewhere the
true slope never goes.

    python3 spotcheck.py [DIR] [EVERY]
"""
import glob, os, re, sys
from fractions import Fraction
from mpmath import mp, mpf
import ledger as L

mp.dps = 40
DIR = sys.argv[1] if len(sys.argv) > 1 else '..'
EVERY = int(sys.argv[2]) if len(sys.argv) > 2 else 50

FR = r'(\d+)/(\d+)'
HZ = re.compile(r'^Lemma hz_(\d+) \(b : R\) : %s <= b <= %s ->' % (FR, FR))
BND = re.compile(r'^\s*%s <= q1 <= %s ->\s*$' % (FR, FR))
HEAD = re.compile(r'^Theorem window_(\d+)\b')

sl, qs = {}, {}
for path in sorted(glob.glob(os.path.join(DIR, 'LedgerCoverP*.v'))):
    lines = open(path).read().splitlines()
    for i, line in enumerate(lines):
        z = HZ.match(line)
        if z:
            sl[int(z.group(1))] = (Fraction(int(z.group(2)), int(z.group(3))),
                                   Fraction(int(z.group(4)), int(z.group(5))))
        h = HEAD.match(line)
        if h:
            for l2 in lines[i:i + 10]:
                b = BND.match(l2)
                if b:
                    qs[int(h.group(1))] = (
                        Fraction(int(b.group(1)), int(b.group(2))),
                        Fraction(int(b.group(3)), int(b.group(4))))
                    break

bad = 0
for i in sorted(qs)[::EVERY]:
    qa, qb = qs[i]
    blo, bhi = sl[i]
    mid = mpf(qa.numerator) / qa.denominator
    mid = (mid + mpf(qb.numerator) / qb.denominator) / 2
    true = -L.fprime(mid)
    ok = mpf(blo.numerator) / blo.denominator <= true <= mpf(bhi.numerator) / bhi.denominator
    if not ok:
        bad += 1
    print("window %4d  q1~%s  -f'=%s  bracket [%s, %s]  %s"
          % (i, mp.nstr(mid, 8), mp.nstr(true, 8), float(blo), float(bhi),
             "ok" if ok else "OUTSIDE"))
print("FAILED (%d outside)" % bad if bad else "SPOTCHECK OK")
sys.exit(1 if bad else 0)
