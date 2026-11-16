#!/usr/bin/env python3
"""交差型 F2（cross.py と同じ定義）を，組の最小化を 2 段に分けて速く計算する.

  F2(T,S) = min( min_u F2(T_u,S) + F2(T_u,S-1) + F2(T-T_u,S-1),
                 min_u F2(T_u,S) + F2(T_u,S-2) + K(T-T_u に u の印を残した木, S-1) )
  K(G*,s) = min_{v は根でも印の祖先でもない} 2 F2(G*_v, s) + F2(G* - G*_v から印を消した木, s-1)

印（MARK）は「途中で外される u」の跡．v が印の祖先だと，v を外すとき u がもう無いので不正になる．
印の無い穴（外側の段で保持されている頂点）は消してよい（その部分問題の間ずっと保持されている）．

使い方:
  python3 cross_fast.py selftest 12        # 頂点数 12 以下の全木で cross.py の F2 と一致するか
  python3 cross_fast.py cbt 7 3            # 完全二分木 T_h（h<=7），S=p_min..p_min+3 で F と F2
"""

from __future__ import annotations

import functools
import sys

import ftree as ft
from ftree import INF, KIDS, node

MARK = len(KIDS)
KIDS.append(())  # 葉と同じ形だが別の番号（node(()) は LEAF のまま）


@functools.lru_cache(None)
def hasmark(g: int) -> bool:
    return g == MARK or any(hasmark(c) for c in KIDS[g])


@functools.lru_cache(None)
def strip(g: int) -> int:
    assert g != MARK
    return node(tuple(strip(c) for c in KIDS[g] if c != MARK))


@functools.lru_cache(None)
def cutsM(g: int) -> tuple[tuple[int, int], ...]:
    """根以外の u ごとに (T_u, T_u を印に置き換えた木)．g は印を含まない."""
    ks = KIDS[g]
    res = set()
    for k in range(len(ks)):
        rest = ks[:k] + ks[k + 1:]
        res.add((ks[k], node(rest + (MARK,))))
        for (s, r) in cutsM(ks[k]):
            res.add((s, node(rest + (r,))))
    return tuple(sorted(res))


@functools.lru_cache(None)
def cutsK(g: int) -> tuple[tuple[int, int], ...]:
    """印をちょうど 1 つ含む g で，根でも印の祖先（と印自身）でもない v ごとに (G_v, G - G_v)."""
    ks = KIDS[g]
    res = set()
    for k in range(len(ks)):
        c = ks[k]
        rest = ks[:k] + ks[k + 1:]
        if not hasmark(c):
            res.add((c, node(rest)))
            for (s, r) in ft.cuts(c):
                res.add((s, node(rest + (r,))))
        elif c != MARK:
            for (s, r) in cutsK(c):
                res.add((s, node(rest + (r,))))
    return tuple(sorted(res))


@functools.lru_cache(None)
def F2(g: int, S: int):
    assert not hasmark(g)
    if S <= 0:
        return INF
    if ft.PRUNE and S < ft.lb_space(g):
        return INF  # 正当性は ftree.py（F2 と F は有限性が同じ）
    if not KIDS[g]:
        return 1
    best = INF
    for (s, r) in ft.cuts(g):
        v = F2(s, S) + F2(s, S - 1) + F2(r, S - 1)
        if v < best:
            best = v
    if S >= 3:
        for (s, rstar) in cutsM(g):
            a = F2(s, S) + F2(s, S - 2)
            if a >= best:
                continue
            v = a + K(rstar, S - 1)
            if v < best:
                best = v
    return best


@functools.lru_cache(None)
def K(gstar: int, S: int):
    best = INF
    for (s, r) in cutsK(gstar):
        v = 2 * F2(s, S) + F2(strip(r), S - 1)
        if v < best:
            best = v
    return best


def main():
    mode = sys.argv[1]
    if mode == "selftest":
        import cross
        N = int(sys.argv[2])
        by = ft.enumerate_trees(N)
        pts = bad = 0
        for n in range(1, N + 1):
            for g in by[n]:
                for S in range(1, n + 1):
                    pts += 1
                    if F2(g, S) != cross.F2(g, S):
                        bad += 1
        print(f"selftest n<={N}: points {pts}, cross_fast.F2 != cross.F2: {bad}")
    elif mode == "cbt":
        H = int(sys.argv[2])
        extra = int(sys.argv[3])
        for h in range(2, H + 1):
            g = ft.cbt(h)
            p = next(S for S in range(1, 2 ** h + 1) if ft.F(g, S) < INF)
            row = []
            for S in range(p, p + extra + 1):
                row.append((S, ft.F(g, S), F2(g, S)))
            print(f"h={h} p_min={p}: (S, F, F2) = {row}", flush=True)


if __name__ == "__main__":
    main()
