#!/usr/bin/env python3
"""Check that the cover really covers, by reading the EMITTED theorems.

The claim "q1 in [1.45, 3.25] is covered" is a statement about the union
of 925 separately-proved theorems, and nothing in Rocq checks it.  This
script re-derives it from the generated .v files -- not from the
generator's own bookkeeping -- by parsing each [window_i]'s hypothesis
[qa <= q1 <= qb] and its conclusion [val <= ledger ...], and verifying

  * the windows are consecutive and consecutive ones share an endpoint
    exactly (so the union is a closed interval, with no gaps);
  * the union runs from QLO to QHI;
  * every certified value is positive;
  * every window's slope bracket is NON-EMPTY.  That last one guards
    against vacuity: [hz_i] is trivially provable when blo > bhi, and a
    window whose slope hypothesis cannot be satisfied says nothing.
    (A bracket coming out empty is the signature of a q that is not a
    minimiser at all -- which is what happens below q ~ 0.5, where f is
    concave.  See SlopeWindow.v's note on the range.)

    python3 check_tiling.py [DIR] [QLO] [QHI]
"""

import glob
import os
import re
import sys
from fractions import Fraction

DIR = sys.argv[1] if len(sys.argv) > 1 else '..'
QLO = Fraction(sys.argv[2]) if len(sys.argv) > 2 else Fraction(145, 100)
QHI = Fraction(sys.argv[3]) if len(sys.argv) > 3 else Fraction(325, 100)

FR = r'(\d+)/(\d+)'
HEAD = re.compile(r'^Theorem window_(\d+)\b')
BND = re.compile(r'^\s*%s <= q1 <= %s ->\s*$' % (FR, FR))
VAL = re.compile(r'^\s*%s <= ledger q1 q2 G w1 f1 f2 ft\.\s*$' % FR)
HZ = re.compile(r'^Lemma hz_(\d+) \(b : R\) : %s <= b <= %s ->' % (FR, FR))

wins = {}
slopes = {}
for path in sorted(glob.glob(os.path.join(DIR, 'LedgerCoverP*.v'))):
    lines = open(path).read().splitlines()
    for line in lines:
        z = HZ.match(line)
        if z:
            slopes[int(z.group(1))] = (Fraction(int(z.group(2)), int(z.group(3))),
                                       Fraction(int(z.group(4)), int(z.group(5))))
    for i, line in enumerate(lines):
        m = HEAD.match(line)
        if not m:
            continue
        idx = int(m.group(1))
        qa = qb = val = None
        for line2 in lines[i:i + 30]:
            b = BND.match(line2)
            if b and qa is None:
                qa = Fraction(int(b.group(1)), int(b.group(2)))
                qb = Fraction(int(b.group(3)), int(b.group(4)))
            v = VAL.match(line2)
            if v:
                val = Fraction(int(v.group(1)), int(v.group(2)))
                break
        assert qa is not None and val is not None, "unparsed window %d" % idx
        assert idx not in wins, "duplicate window %d" % idx
        wins[idx] = (qa, qb, val, os.path.basename(path))

n = len(wins)
assert sorted(wins) == list(range(n)), "window indices are not 0..%d" % (n - 1)

cur = wins[0][0]
bad = 0
if cur > QLO:
    print("GAP: cover starts at %s > %s" % (float(cur), float(QLO)))
    bad += 1
for i in range(n):
    qa, qb, val, part = wins[i]
    if qa != cur:
        print("GAP before window %d (%s): [%s] expected, got [%s]"
              % (i, part, float(cur), float(qa)))
        bad += 1
    if qb <= qa:
        print("EMPTY window %d" % i)
        bad += 1
    if val <= 0:
        print("NON-POSITIVE value in window %d: %s" % (i, float(val)))
        bad += 1
    if i not in slopes:
        print("window %d has no hz_%d slope bracket" % (i, i))
        bad += 1
    elif slopes[i][0] >= slopes[i][1]:
        print("EMPTY slope bracket in window %d: [%s, %s] -- VACUOUS"
              % (i, float(slopes[i][0]), float(slopes[i][1])))
        bad += 1
    cur = qb
if cur < QHI:
    print("GAP: cover stops at %s < %s" % (float(cur), float(QHI)))
    bad += 1

vals = [w[2] for w in wins.values()]
widths = [w[1] - w[0] for w in wins.values()]
print("%d windows, union [%s, %s]" % (n, float(wins[0][0]), float(cur)))
print("widths  %.3e .. %.3e" % (float(min(widths)), float(max(widths))))
print("ledger  >= %s (smallest certified value)" % float(min(vals)))
sw = [slopes[i][1] - slopes[i][0] for i in range(n) if i in slopes]
print("slope brackets: %d, widths %.3e .. %.3e, all non-empty"
      % (len(sw), float(min(sw)), float(max(sw))))
print("FAILED (%d problems)" % bad if bad else "TILING OK")
sys.exit(1 if bad else 0)
