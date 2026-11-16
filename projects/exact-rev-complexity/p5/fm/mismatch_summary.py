#!/usr/bin/env python3
"""check_mf.py の入出力ファイルから F != M の点を列挙し，次数などで分類する."""
import sys
from collections import Counter

import check_mf as c
import ftree as ft

trees = {}
for line in open(sys.argv[1]):
    xs = list(map(int, line.split()))
    trees[xs[0]] = [-1] + xs[2:]
bad = []
for line in open(sys.argv[2]):
    xs = list(map(int, line.split()))
    tid, n, ms = xs[0], xs[1], xs[2:]
    g = c.from_parents(trees[tid])
    for S in range(1, n + 1):
        m = ms[S - 1]
        m = ft.INF if m < 0 else m
        f = ft.F(g, S)
        if m != f:
            deg = Counter(trees[tid][1:])
            bad.append((tid, ft.show(g), S, f, m, max(deg.values()), deg[0]))
print("points", len(bad), "distinct trees", len({b[0] for b in bad}))
print("S", sorted(Counter(b[2] for b in bad).items()))
print("F-M", sorted(Counter(b[3] - b[4] for b in bad).items()))
print("max degree", sorted(Counter(b[5] for b in bad).items()))
print("root degree", sorted(Counter(b[6] for b in bad).items()))
for b in sorted(bad, key=lambda b: (b[5], b[2], b[1]))[: int(sys.argv[3]) if len(sys.argv) > 3 else 10]:
    print("  (id, shape, S, F, M, maxdeg, rootdeg) =", b)
