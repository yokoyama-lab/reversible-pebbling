#!/usr/bin/env python3
"""F2 < F（= 交差型が F を下回る）木を族ごとに数える．n<=N の全木を F2 と F で比べる."""
import sys
from collections import Counter

import cross_fast as cf
import ftree as ft
from ftree import KIDS


def height(g):
    return 1 + max((height(c) for c in KIDS[g]), default=0)


def is_caterpillar(g):
    # 根から下る 1 本の道に葉が付く木（各頂点の非葉の子が高々 1 個）．通常の「毛虫」（葉を除くと道）より狭い
    nonleaf = [c for c in KIDS[g] if KIDS[c]]
    return len(nonleaf) <= 1 and all(is_caterpillar(c) for c in nonleaf)


def is_spider(g):
    # 根以外の頂点は子が高々 1 個
    def chainlike(x):
        return len(KIDS[x]) <= 1 and all(chainlike(c) for c in KIDS[x])
    return all(chainlike(c) for c in KIDS[g])


def maxdeg(g):
    return max([len(KIDS[g])] + [maxdeg(c) for c in KIDS[g]])


N = int(sys.argv[1])
by = ft.enumerate_trees(N)
for n in range(1, N + 1):
    fam = Counter()
    tot = Counter()
    for g in by[n]:
        feats = {"cat": is_caterpillar(g), "spider": is_spider(g), "h<=2": height(g) <= 3, "h<=3": height(g) <= 4,
                 "maxdeg<=2": maxdeg(g) <= 2, "maxdeg<=3": maxdeg(g) <= 3}
        bad = any(cf.F2(g, S) < ft.F(g, S) for S in range(1, n + 1))
        for k, v in feats.items():
            if v:
                tot[k] += 1
                if bad:
                    fam[k] += 1
        tot["all"] += 1
        if bad:
            fam["all"] += 1
    print(f"n={n}: " + ", ".join(f"{k} {fam[k]}/{tot[k]}" for k in ["all", "cat", "spider", "h<=2", "h<=3", "maxdeg<=2", "maxdeg<=3"]), flush=True)
