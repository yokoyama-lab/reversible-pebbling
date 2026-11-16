#!/usr/bin/env python3
"""置く順と外す順を独立にした再帰 G（F の LIFO の結びつきを外したもの）.

  G(葉,S) = 1 (S>=1)
  G(T,S)  = 1 + min_{H ⊇ ch(r), |H| <= S-1} [ D_S(H) + D_{S-1}(H) ]
  D_B(H)  = H の頂点を 1 つずつ置いて保持していく順序 (c_1..c_j) についての最小値
            sum_i G(piece(c_i | c_1..c_{i-1}), B - i + 1)
  piece(c | 先に保持した集合) = T_c から，先に保持した c の子孫の部分木を除いた木
  （除いた頂点は保持されているので入力として使える）．

構成: 森 T - r で H を順序 sigma で D_S の手順どおりに作る → 根を置く →
      順序 tau で D_{S-1} の手順を作り，それを逆再生して H を消す（根を持っているので予算 S-1）．
sigma と tau は独立．F は tau = sigma（外す順 = 置く順の逆）に固定した特別な場合なので M <= G <= F．

H の大きさは S-1 以下に限る（根を置く瞬間に H と根が盤上にある）．計算量は部分集合の数で決まるので小さい木向け．
使い方: python3 gdec.py selftest N   # N 以下の全木で G と F2 を比べる（M=F2 が確かめてある範囲では G=F2 のはず）
"""

from __future__ import annotations

import functools
import sys

import cross_fast as cf
import ftree as ft
from ftree import INF, KIDS

sys.setrecursionlimit(1_000_000)


def explicit(g: int):
    par = ft.parents(g)
    n = len(par)
    kids = [[] for _ in range(n)]
    for i in range(1, n):
        kids[par[i]].append(i)
    desc = [0] * n  # 子孫（自分を含む）のビット集合
    for v in range(n - 1, -1, -1):
        m = 1 << v
        for c in kids[v]:
            m |= desc[c]
        desc[v] = m
    return par, kids, desc


@functools.lru_cache(None)
def G(g: int, S: int):
    if S <= 0:
        return INF
    if S < ft.chain_space(ft.height(g)):
        return INF  # M の下界（道への制限）．G は構成なので M <= G．完全二分木による枝刈りは F の有限性にしか示していないので使わない
    if not KIDS[g]:
        return 1
    par, kids, desc = explicit(g)
    n = len(par)

    @functools.lru_cache(None)
    def piece_shape(c: int, held: int) -> int:
        def build(v: int) -> int:
            return ft.node(tuple(build(w) for w in kids[v] if not (held >> w) & 1))
        return build(c)

    def piece(c: int, held: int) -> int:
        # c の部分木のうち，保持中の c の子孫より下を除いたもの
        return piece_shape(c, held & desc[c] & ~(1 << c))

    must = 0
    for c in kids[0]:
        must |= 1 << c
    best = INF
    for B, store in ((S, {}), (S - 1, {})):
        # D_B(H) を |H| の小さい順に
        D = {0: 0}
        layer = [0]
        for k in range(1, S):  # |H| = k <= S-1
            nxt = {}
            for H in layer:
                base = D[H]
                bud = B - (k - 1)
                for c in range(1, n):
                    if (H >> c) & 1:
                        continue
                    val = G(piece(c, H), bud)
                    if val == INF:
                        continue
                    H2 = H | (1 << c)
                    v = base + val
                    if v < nxt.get(H2, INF):
                        nxt[H2] = v
            D.update(nxt)
            layer = list(nxt)
        store.update(D)
        if B == S:
            DS = store
        else:
            DS1 = store
    for H, a in DS.items():
        if H & must != must:
            continue
        b = DS1.get(H)
        if b is None:
            continue
        if 1 + a + b < best:
            best = 1 + a + b
    return best


def main():
    if sys.argv[1] == "selftest":
        N = int(sys.argv[2])
        by = ft.enumerate_trees(N)
        pts = less = more = 0
        ex = []
        for n in range(1, N + 1):
            for g in by[n]:
                for S in range(1, n + 1):
                    a, b = G(g, S), cf.F2(g, S)
                    pts += 1
                    if a < b:
                        less += 1
                        ex.append((ft.show(g), S, b, a))
                    elif a > b:
                        more += 1
                        ex.append(("G>F2!", ft.show(g), S, b, a))
        print(f"n<={N}: points {pts}, G<F2 {less}, G>F2 {more}", ex[:5])


if __name__ == "__main__":
    main()
