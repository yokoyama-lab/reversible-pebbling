#!/usr/bin/env python3
"""F / F2 の最適な構成を頂点番号つきの手順に展開し，witness.replay で再生して検査する.

BFS が届かない大きな木でも「M <= 手数」を証人つきで示すための道具．
展開した手数が F2（または F）の値と等しく，replay が通れば，その値は M の上界として検証済み．

使い方:
  python3 expand.py selftest N        # 頂点数 N 以下の全木・全 S で，展開の手数 = F2 かつ replay 合格か
  python3 expand.py family k          # 反例の族（下の family()）を k=... で構成して F と証人を示す
"""

from __future__ import annotations

import functools
import sys

import cross_fast as cf
import ftree as ft
from ftree import INF
from witness import replay

sys.setrecursionlimit(1_000_000)


class Tree:
    def __init__(self, par: list[int]):
        self.par = par
        self.n = len(par)
        self.kids = [[] for _ in range(self.n)]
        for i in range(1, self.n):
            self.kids[par[i]].append(i)

    @functools.lru_cache(None)
    def shape(self, v: int, excl: frozenset) -> int:
        return ft.node([self.shape(c, excl) for c in self.kids[v] if c not in excl])

    def verts(self, v: int, excl: frozenset) -> list[int]:
        out = [v]
        for c in self.kids[v]:
            if c not in excl:
                out.extend(self.verts(c, excl))
        return out

    def is_anc(self, a: int, b: int) -> bool:
        while b != -1:
            if a == b:
                return True
            b = self.par[b]
        return False


def expand(T: Tree, r: int, excl: frozenset, S: int, use_f2: bool) -> list[int]:
    """部分問題（根 r，excl の頂点とその下は保持済みとして除く）を S 個でペブリングする手順."""
    g = T.shape(r, excl)
    val = cf.F2(g, S) if use_f2 else ft.F(g, S)
    assert val < INF, (ft.show(g), S)
    Fv = cf.F2 if use_f2 else ft.F
    sub = [v for v in T.verts(r, excl) if v != r]
    if not sub:
        return [r]
    # F の分割
    for u in sub:
        su = T.shape(u, excl)
        ru = T.shape(r, excl | {u})
        if Fv(su, S) + Fv(su, S - 1) + Fv(ru, S - 1) == val:
            return (expand(T, u, excl, S, use_f2) + expand(T, r, excl | {u}, S - 1, use_f2)
                    + expand(T, u, excl, S - 1, use_f2)[::-1])
    assert use_f2
    # 交差
    for u in sub:
        for v in sub:
            if u == v or T.is_anc(u, v) or T.is_anc(v, u):
                continue
            su, sv = T.shape(u, excl), T.shape(v, excl)
            rr = T.shape(r, excl | {u, v})
            if Fv(su, S) + Fv(sv, S - 1) + Fv(rr, S - 2) + Fv(su, S - 2) + Fv(sv, S - 1) == val:
                return (expand(T, u, excl, S, use_f2) + expand(T, v, excl, S - 1, use_f2)
                        + expand(T, r, excl | {u, v}, S - 2, use_f2)
                        + expand(T, u, excl, S - 2, use_f2)[::-1] + expand(T, v, excl, S - 1, use_f2)[::-1])
    raise AssertionError("no split attains the value")


def check(par: list[int], S: int, use_f2: bool):
    T = Tree(par)
    moves = expand(T, 0, frozenset(), S, use_f2)
    ok, msg = replay(par, S, moves)
    return moves, ok, msg


def family(k: int) -> tuple[list[int], int]:
    """反例の族: S = k+3．根の子は，鎖 X（2^k 頂点．最小空間 k+1 = S-2），
    星 Y（中心と S-2 枚の葉．最小空間 S-1），葉 S-3 枚の計 S-1 個．
    F は Y を先・X を後に置く入れ子しか取れず，交差（X を先に置いて先に外す）が
    F(X,S-1) - F(X,S) 手だけ短い．"""
    S = k + 3
    par = [-1]
    # 鎖 X: 頂点 x_1（根の子）- x_2 - ... - x_{2^k}
    prev = 0
    for _ in range(2 ** k):
        par.append(prev)
        prev = len(par) - 1
    y = len(par)
    par.append(0)
    for _ in range(S - 2):
        par.append(y)
    for _ in range(S - 3):
        par.append(0)
    return par, S


def main():
    mode = sys.argv[1]
    if mode == "selftest":
        import check_mf as c
        N = int(sys.argv[2])
        by = ft.enumerate_trees(N)
        pts = bad = 0
        for n in range(1, N + 1):
            for g in by[n]:
                par = ft.parents(g)
                assert c.from_parents(par) == g
                for S in range(1, n + 1):
                    for use_f2 in (False, True):
                        val = cf.F2(g, S) if use_f2 else ft.F(g, S)
                        if val == INF:
                            continue
                        moves, ok, msg = check(par, S, use_f2)
                        pts += 1
                        if not ok or len(moves) != val:
                            bad += 1
                            if bad <= 5:
                                print("BAD", ft.show(g), S, use_f2, val, len(moves), msg)
        print(f"selftest n<={N}: {pts} expansions, bad {bad}")
    elif mode == "family":
        for k in map(int, sys.argv[2:]):
            par, S = family(k)
            T = Tree(par)
            g = T.shape(0, frozenset())
            f, f2 = ft.F(g, S), cf.F2(g, S)
            moves, ok, msg = check(par, S, True)
            print(f"k={k}: n={len(par)} S={S} F={f} F2={f2} witness {len(moves)} moves, replay: {msg}; "
                  f"F - witness = {f - len(moves)}", flush=True)


if __name__ == "__main__":
    main()
