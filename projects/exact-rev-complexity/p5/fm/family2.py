#!/usr/bin/env python3
"""差が 2m 以上になる族（critic の代案）の検算: 定理 5 の M の式と F を比べる.

根の子: m 組 (X_j, Y_j) と葉（計 S-1 個）．X_j = x(葉 L_j 枚, z(葉, 葉))，L_j = S-2j-2 >= 2（最小空間 S-2j），
Y_j = 葉 S-2j 枚の星（最小空間 S-2j+1）．
M は定理 5 の式（部分木の M には F を使う．部分木で M=F であることは BFS で別に確かめる）．
"""
import itertools

import ftree as ft
from ftree import INF

L = ft.LEAF


def build(m, S):
    kids = []
    for j in range(1, m + 1):
        Lj = S - 2 * j - 2
        assert Lj >= 2
        kids.append(ft.node((L,) * Lj + (ft.node((L, L)),)))
        kids.append(ft.node((L,) * (S - 2 * j)))
    nleaf = S - 1 - 2 * m
    assert nleaf >= 0
    return kids, kids + [L] * nleaf


def thm5_M(children, S):
    nonleaf = [c for c in children if ft.KIDS[c]]
    nleaf = len(children) - len(nonleaf)
    def best(off):  # 予算 S-i+1-off（i=1..）．葉は後ろへ（予算 1 以上なら 1 手）
        b = INF
        for perm in itertools.permutations(nonleaf):
            v = sum(ft.F(c, S - i + 1 - off) for i, c in enumerate(perm, 1))
            b = min(b, v)
        return b + nleaf
    return 1 + best(0) + best(1)


for m, S in [(1, 6), (1, 8), (2, 8), (2, 9), (3, 10), (4, 12)]:
    nonleaf, kids = build(m, S)
    T = ft.node(kids)
    f = ft.F(T, S)
    mm = thm5_M(kids, S)
    print(f"m={m} S={S} n={ft.nverts(T)}: F={f} M(定理5)={mm} 差={f - mm} (>= 2m={2*m}: {f - mm >= 2*m})", flush=True)
