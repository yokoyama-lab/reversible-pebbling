#!/usr/bin/env python3
"""BFS の M を F と F2（交差型を足した構成．cross_fast.py）の両方と突き合わせる.

使い方: python3 check_mf2.py trees.txt m.txt
M <= F2 <= F は構成から常に成り立つので，M > F2 は実装の誤りを意味する．
"""

from __future__ import annotations

import sys
from collections import Counter

import check_mf as c
import cross_fast as cf
import ftree as ft


def main():
    trees = {}
    for line in open(sys.argv[1]):
        xs = list(map(int, line.split()))
        trees[xs[0]] = [-1] + xs[2:]
    pts = 0
    cnt = Counter()
    ex = []
    for line in open(sys.argv[2]):
        xs = list(map(int, line.split()))
        tid, n, ms = xs[0], xs[1], xs[2:]
        g = c.from_parents(trees[tid])
        for S in range(1, n + 1):
            m = ms[S - 1]
            m = ft.INF if m < 0 else m
            f, f2 = ft.F(g, S), cf.F2(g, S)
            pts += 1
            key = ("M<F" if m < f else "M=F") + "," + ("M<F2" if m < f2 else ("M=F2" if m == f2 else "M>F2!"))
            cnt[key] += 1
            if m < f2 and len(ex) < 10:
                ex.append((tid, ft.show(g), S, f, f2, m))
    print(f"points {pts}: {dict(cnt)}")
    for x in ex:
        print("  M < F2 (id, shape, S, F, F2, M):", x)


if __name__ == "__main__":
    main()
