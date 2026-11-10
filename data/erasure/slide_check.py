#!/usr/bin/env python3
"""Checks behind ErasurePebbling/Sliding.lean (gap-sequence form of phi).

A board is its gap sequence B = (B_1, ..., B_m), bottom to top; T is the
threshold at the current count (it doubles with every removal).  Removing
pebble i pays max(0, B_i - T) and merges B_i into B_{i+1}.

usage: slide_check.py T m G     (all gap sequences of length m, gaps 1..G)

Reports three things.
  MU        phi(pebble moved up by one cell) <= phi + 1          (phi_moveUp_le)
  SLIDE     x free with gap < T, predecessor v with gap > T, v first optimal:
            phi(b') <= phi(b) - 1 and phi(b - x) <= phi(b' - x) + 1, where b'
            is b with v moved down by one cell (the sliding step)
  BOUNDARY  census of the premises of BoundaryStep: gap x = T, gap v > T,
            v first optimal.  'unique' counts the boards where no other first
            step is optimal (= the premises of BoundaryStep hold); 'fail'
            counts boards where phi(b - x) > phi(b) (a counterexample to R').
Exit code 1 if any check fails.
"""
import sys, itertools, collections
from functools import lru_cache
sys.setrecursionlimit(10000)

def rm(B, i):
    return B[:i] if i == len(B) - 1 else B[:i] + (B[i] + B[i + 1],) + B[i + 2:]

@lru_cache(maxsize=None)
def phi(B, T):
    if not B:
        return 0
    return min(max(0, B[i] - T) + phi(rm(B, i), 2 * T) for i in range(len(B)))

def main():
    T, m, G = (int(a) for a in sys.argv[1:4])
    mu_n = mu_f = sl_n = sl_f = bd_n = bd_u = bd_f = 0
    dbl = collections.Counter()
    for B in itertools.product(range(1, G + 1), repeat=m):
        pB = phi(B, T)
        for w in range(m):
            if w == m - 1:
                B2 = B[:w] + (B[w] + 1,)
            elif B[w + 1] >= 2:
                B2 = B[:w] + (B[w] + 1, B[w + 1] - 1) + B[w + 2:]
            else:
                continue
            mu_n += 1
            mu_f += phi(B2, T) > pB + 1
        opt = [i for i in range(m) if max(0, B[i] - T) + phi(rm(B, i), 2 * T) == pB]
        for x in range(1, m):
            v = x - 1
            if B[x] > T or B[v] <= T or v not in opt:
                continue
            if B[x] < T:
                sl_n += 1
                Bp = B[:v] + (B[v] - 1, B[x] + 1) + B[x + 1:]
                ok = (phi(Bp, T) <= pB - 1 and
                      phi(rm(B, x), 2 * T) <= phi(rm(Bp, x), 2 * T) + 1)
                sl_f += not ok
            else:
                bd_n += 1
                bd_u += opt == [v]
                bd_f += phi(rm(B, x), 2 * T) > pB
                dbl[B[v] > 2 * T] += 1
    print(f"T={T} m={m} G={G} | MU n={mu_n} fail={mu_f} | SLIDE n={sl_n} fail={sl_f} | "
          f"BOUNDARY n={bd_n} unique={bd_u} fail={bd_f} gapv>2T={dbl[True]}")
    return 1 if (mu_f or sl_f or bd_f) else 0

if __name__ == "__main__":
    sys.exit(main())
