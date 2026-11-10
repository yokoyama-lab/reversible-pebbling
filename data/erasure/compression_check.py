#!/usr/bin/env python3
"""Numerical companion of ErasurePebbling/Compression.lean (not a proof).

For a board b (pebbles on cells of a chain of n cells, at most p pebbles) let
  psi(b) = least number of cells whose width must be set from 1 to 0 so that
           the weighted gap potential of b is 0 ("squeezing number").
The Lean proof of the upper bound of Conjecture B2 tracks psi along a play.
This script checks, on ALL boards with at most p pebbles among n cells:
  place   : a legal placement never raises psi
  revrem  : a reversible removal (predecessor pebbled / entrance) never raises psi
  erase   : any other removal raises psi by at most 2^(p-2)
  target  : psi({m}) = max(0, m - 2^(p-1)) for every m <= n
and reports how psi compares with the gap potential phi of UpperBound.lean
(psi <= phi always; psi < phi on some boards, e.g. nodes {2,5,7} for p = 3).

usage: python3 -I compression_check.py P N      (exit code 1 on any failure)
"""
import itertools
import sys
from functools import lru_cache

p = int(sys.argv[1])
n = int(sys.argv[2])


def thr(k):
    return 2 ** (p - k)


def wphi(w, cells):
    """Weighted gap potential: least total excess over all removal orders."""

    @lru_cache(None)
    def f(cs):
        if not cs:
            return 0
        k = len(cs)
        best = None
        for idx, z in enumerate(cs):
            lo = cs[idx - 1] + 1 if idx > 0 else 0
            g = sum(w[lo:z + 1])
            v = max(0, g - thr(k)) + f(cs[:idx] + cs[idx + 1:])
            if best is None or v < best:
                best = v
        return best

    return f(cells)


ones = tuple([1] * n)


def psi(cells):
    if not cells:
        return 0
    top = cells[-1]
    for c in range(0, top + 2):
        for zeros in itertools.combinations(range(top + 1), c):
            w = list(ones)
            for i in zeros:
                w[i] = 0
            if wphi(tuple(w), cells) == 0:
                return c
    raise RuntimeError("unreachable: all-zero widths are flat")


Q = 2 ** (p - 2)
boards = [cs for k in range(0, p + 1) for cs in itertools.combinations(range(n), k)]
PSI = {cs: psi(cs) for cs in boards}
PHI = {cs: wphi(ones, cs) for cs in boards}
bad = {"place": 0, "revrem": 0, "erase": 0, "psi>phi": 0, "target": 0}
cnt = {"place": 0, "revrem": 0, "erase": 0, "psi<phi": 0}
for cs in boards:
    s = set(cs)
    if PSI[cs] > PHI[cs]:
        bad["psi>phi"] += 1
    if PSI[cs] < PHI[cs]:
        cnt["psi<phi"] += 1
    for x in range(n):
        ok = (x == 0) or ((x - 1) in s)
        if x in s:
            t = tuple(sorted(s - {x}))
            if ok:
                cnt["revrem"] += 1
                if PSI[t] > PSI[cs]:
                    bad["revrem"] += 1
            else:
                cnt["erase"] += 1
                if PSI[t] > PSI[cs] + Q:
                    bad["erase"] += 1
        elif ok and len(cs) < p:
            t = tuple(sorted(s | {x}))
            cnt["place"] += 1
            if PSI[t] > PSI[cs]:
                bad["place"] += 1
for m in range(1, n + 1):
    if PSI[(m - 1,)] != max(0, m - 2 ** (p - 1)):
        bad["target"] += 1
print("p", p, "n", n, "boards", len(boards), "checked", cnt, "failures", bad)
if any(bad.values()):
    raise SystemExit(1)
