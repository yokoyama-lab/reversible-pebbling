#!/usr/bin/env python3
"""ランダムな二分木（子 2 個以下）で F2 < F を探す（反例の候補探し．決定的: 種を固定）.

使い方: python3 rand_bin.py seed count nmin nmax
F2 < F が出たら，その木は M <= F2 < F の反例（expand.py で証人を作り replay で確かめる）．
"""
import random
import sys
import time

import cross_fast as cf
import ftree as ft
from ftree import INF

seed, count, nmin, nmax = map(int, sys.argv[1:5])
rng = random.Random(seed)


def rand_tree(n: int, style: int) -> int:
    if n == 1:
        return ft.LEAF
    if n == 2:
        return ft.node((ft.LEAF,))
    r = rng.random()
    if style == 0:      # 一様に近い分割
        p_one = 0.2
    elif style == 1:    # 鎖が多い
        p_one = 0.6
    else:               # 枝分かれが多い
        p_one = 0.05
    if r < p_one:
        return ft.node((rand_tree(n - 1, style),))
    if style == 3:      # 偏った分割（片側が小さい）
        a = rng.randint(1, max(1, (n - 1) // 4))
    else:
        a = rng.randint(1, n - 2)
    return ft.node((rand_tree(a, style), rand_tree(n - 1 - a, style)))


t0 = time.time()
found = 0
for i in range(count):
    n = rng.randint(nmin, nmax)
    g = rand_tree(n, i % 4)
    p = next(S for S in range(1, n + 1) if ft.F(g, S) < INF)
    for S in range(p, min(n, p + 4) + 1):
        f, f2 = ft.F(g, S), cf.F2(g, S)
        if f2 < f:
            found += 1
            print(f"FOUND n={n} S={S} F={f} F2={f2} shape={ft.canon(g)}", flush=True)
    cf.F2.cache_clear()  # 木ごとにキャッシュを捨てる（メモリを抑える）
    cf.K.cache_clear()
    ft.F.cache_clear()
    if (i + 1) % 25 == 0:
        print(f"# {i + 1} trees, found {found}, {time.time() - t0:.0f}s", flush=True)
print(f"DONE {count} trees, found {found}", flush=True)
