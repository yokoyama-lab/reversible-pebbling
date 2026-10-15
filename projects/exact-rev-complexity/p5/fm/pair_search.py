#!/usr/bin/env python3
"""根に 2 つの部分木 A, B をぶら下げた木 T = r(A,B) で，交差型の手順が F を下回る組を探す.

交差型: A を S 個で置く → B を S-1 個で置く → 根を置く → A を S-2 個で外す → B を S-1 個で外す．
  手数 X = F(A,S) + F(B,S-1) + 1 + F(A,S-2) + F(B,S-1)（構成なので M(T,S) <= X）．
F の入れ子（LIFO）の 2 通りとの差は
  X - [A が外側] = Δ_A(S-1) - Δ_B(S-1)，  X - [B が外側] = Δ_B(S) - Δ_A(S)
  （Δ_X(s) = F(X,s-1) - F(X,s)）なので，両方が負になる組だけを F(T,S) の全計算にかける．
X < F(T,S) なら M(T,S) <= X < F(T,S) で F = M の反例．
"""

from __future__ import annotations

import argparse
import itertools

import ftree as ft
from ftree import INF


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=9, help="A, B の頂点数の上限")
    ap.add_argument("--maxdeg", type=int, default=None)
    ap.add_argument("--limit", type=int, default=20)
    a = ap.parse_args()
    by = ft.enumerate_trees(a.nmax, a.maxdeg)
    trees = [g for n in range(1, a.nmax + 1) for g in by[n]]
    smax = a.nmax + 3
    prof = {g: [ft.F(g, s) for s in range(0, smax + 1)] for g in trees}
    cand = found = 0
    best = []
    for A, B in itertools.product(trees, repeat=2):
        pA, pB = prof[A], prof[B]
        for S in range(3, smax + 1):
            fA, fA1, fA2 = pA[S], pA[S - 1], pA[S - 2]
            fB, fB1, fB2 = pB[S], pB[S - 1], pB[S - 2]
            if fA2 == INF or fB1 == INF:
                continue
            X = fA + fB1 + 1 + fA2 + fB1
            nestA = fA + fA1 + fB1 + fB2 + 1
            nestB = fB + fB1 + fA1 + fA2 + 1
            if X >= min(nestA, nestB):
                continue
            cand += 1
            T = ft.node((A, B))
            fT = ft.F(T, S)
            if X < fT:
                found += 1
                if len(best) < a.limit:
                    best.append((ft.nverts(T), ft.show(A), ft.show(B), S, fT, X))
    best.sort()
    print(f"A,B with <= {a.nmax} vertices (maxdeg={a.maxdeg}): trees {len(trees)}, "
          f"crossing beats both LIFO at root: {cand}, of which X < F(T,S): {found}")
    for x in best:
        print("  (n, A, B, S, F(T,S), X):", x)


if __name__ == "__main__":
    main()
