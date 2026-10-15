#!/usr/bin/env python3
"""F に「交差する保持区間」を足した構成 F2 を計算し，F2 < F となる木（= M < F の反例候補）を探す.

F2(T,S) = min( F の分割:  F2(T_u,S) + F2(T_u,S-1) + F2(T-T_u,S-1),
               交差:      F2(T_u,S) + F2(T_v,S-1) + F2(T-T_u-T_v,S-2) + F2(T_u,S-2) + F2(T_v,S-1) )
  交差の手順: u を S 個で置く → u を持って v を S-1 個で置く → u,v を持って残りの根を S-2 個で置く
            → v と根を持って u を S-2 個で外す → 根を持って v を S-1 個で外す．
  u,v は根以外で互いに祖先・子孫でない頂点．どの段も構成なので M <= F2 <= F．
F2 < F の木が見つかれば M < F の反例である（構成を手順に展開して独立の検査器に通すこと）．
"""

from __future__ import annotations

import argparse
import functools

import ftree as ft
from ftree import INF, KIDS, node


@functools.lru_cache(None)
def cuts2(g: int) -> tuple[tuple[int, int, int], ...]:
    """互いに祖先・子孫でない根以外の頂点の組 {u,v} ごとに (T_u, T_v, T - T_u - T_v)."""
    ks = KIDS[g]
    res = set()
    k = len(ks)
    # u, v が異なる子の部分木にある場合
    for i in range(k):
        for j in range(i + 1, k):
            rest = ks[:i] + ks[i + 1:j] + ks[j + 1:]
            for (su, ru) in ((ks[i], None),) + tuple(ft.cuts(ks[i])):
                for (sv, rv) in ((ks[j], None),) + tuple(ft.cuts(ks[j])):
                    kids = list(rest)
                    if ru is not None:
                        kids.append(ru)
                    if rv is not None:
                        kids.append(rv)
                    res.add((su, sv, node(kids)))
    # u, v が同じ子 c の部分木にある場合（c 自身は u,v のどちらでもない）
    for i in range(k):
        rest = ks[:i] + ks[i + 1:]
        for (su, sv, r) in cuts2(ks[i]):
            res.add((su, sv, node(rest + (r,))))
    return tuple(sorted(res))


@functools.lru_cache(None)
def F2(g: int, S: int):
    if S <= 0:
        return INF
    if not KIDS[g]:
        return 1
    best = INF
    for (s, r) in ft.cuts(g):
        v = F2(s, S) + F2(s, S - 1) + F2(r, S - 1)
        if v < best:
            best = v
    if S >= 3:
        for (su, sv, r) in cuts2(g):
            for (a, b) in ((su, sv), (sv, su)):
                v = F2(a, S) + F2(b, S - 1) + F2(r, S - 2) + F2(a, S - 2) + F2(b, S - 1)
                if v < best:
                    best = v
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=12)
    ap.add_argument("--maxdeg", type=int, default=None)
    a = ap.parse_args()
    by = ft.enumerate_trees(a.nmax, a.maxdeg)
    for n in range(1, a.nmax + 1):
        cnt = 0
        ex = []
        for g in by[n]:
            for S in range(1, n + 1):
                f, f2 = ft.F(g, S), F2(g, S)
                assert f2 <= f
                if f2 < f:
                    cnt += 1
                    if len(ex) < 5:
                        ex.append((ft.show(g), S, f, f2))
        print(f"n={n}: trees {len(by[n])}, (T,S) with F2<F: {cnt}", ex, flush=True)


if __name__ == "__main__":
    main()
