#!/usr/bin/env python3
"""Exhaustive checks for the gap potential of `ErasurePebbling/UpperBound.lean`.

A configuration is a sorted tuple of pebbled nodes (1-based; the free entrance
is node 0).  With k = |U| pebbles the threshold is T_k = 2^(p-k), the gap of
a pebble is its distance to the previous pebbled node (or 0), and

    phi(U) = min over pebbled z of  max(0, gap(z) - T_k) + phi(U - z),   phi({}) = 0.

Checked for every configuration with at most p pebbles among nodes 1..N:

  insert   gap(x) <= T_{k+1}           ==>  phi(U + x) <= phi(U)          (proved in Lean)
  erase    any x                       ==>  phi(U - x) <= phi(U) + 2^(p-2)  (proved in Lean)
  remove   gap(x) <= T_k  (reversible) ==>  phi(U - x) <= phi(U)          (RemovalLemma: OPEN)
  ends     phi({}) = 0,  phi({n}) >= n - 2^(p-1)

Note that `remove` is checked for every cheap x (gap <= T_k), which is more
than the real game needs (gap = 1).

Usage:  python3 potential_check.py P N        e.g.  3 16 | 4 24 | 5 22
"""
import itertools
import sys
from functools import lru_cache

p = int(sys.argv[1]) if len(sys.argv) > 1 else 4
N = int(sys.argv[2]) if len(sys.argv) > 2 else 24
Q = 2 ** (p - 2)
H = 2 ** (p - 1)


def T(k):
    return 2 ** (p - k) if k <= p else 1


@lru_cache(maxsize=None)
def phi(U):
    if not U:
        return 0
    k = len(U)
    best = None
    for i, z in enumerate(U):
        prev = U[i - 1] if i > 0 else 0
        v = max(0, (z - prev) - T(k)) + phi(U[:i] + U[i + 1:])
        best = v if best is None else min(best, v)
    return best


def pred(U, u):
    return max([v for v in U if v < u], default=0)


states = [()]
for k in range(1, p + 1):
    states += list(itertools.combinations(range(1, N + 1), k))

fails = {"insert": 0, "erase": 0, "remove": 0}
for U in states:
    k = len(U)
    if k < p:
        for x in range(1, N + 1):
            if x in U or x - pred(U, x) > T(k + 1):
                continue
            V = tuple(sorted(U + (x,)))
            if phi(V) > phi(U):
                fails["insert"] += 1
    for x in U:
        V = tuple(u for u in U if u != x)
        if phi(V) > phi(U) + Q:
            fails["erase"] += 1
        if x - pred(U, x) <= T(k) and phi(V) > phi(U):
            fails["remove"] += 1
ends = phi(()) == 0 and all(phi((n,)) >= n - H for n in range(1, N + 1))
print(f"p={p} N={N} states={len(states)} fails={fails} ends_ok={ends}")
sys.exit(0 if ends and not any(fails.values()) else 1)
