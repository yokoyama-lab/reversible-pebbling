#!/usr/bin/env python3
"""木の Knill 型再帰 F と，木のゲームの全数探索 M（p5_tree_count.py とは別に書いた．標準ライブラリだけ）.

ゲーム（KSS の persistent 可逆ペブリング）: 頂点 v を置く／外す手は v の子がすべてペブル済みのときだけ合法．
空の盤から根だけがペブルされた盤へ．同時に置けるペブルは S 個まで．M(G,S) は最短手数．

再帰（原稿 P5 の定義）:
    F(G,S) = inf (S <= 0),  F(葉,S) = 1 (S >= 1),
    F(G,S) = min_{u != 根} F(G_u,S) + F(G_u,S-1) + F(G - G_u,S-1).

木の形は「子の形の番号の昇順タプル」で正規化して番号を振る．
"""

from __future__ import annotations

import functools
import sys
from collections import deque

sys.setrecursionlimit(1_000_000)
INF = float("inf")

KIDS: list[tuple[int, ...]] = []
_IDX: dict[tuple[int, ...], int] = {}


def node(kids) -> int:
    key = tuple(sorted(kids))
    i = _IDX.get(key)
    if i is None:
        i = len(KIDS)
        _IDX[key] = i
        KIDS.append(key)
    return i


LEAF = node(())


@functools.lru_cache(maxsize=None)
def size(g: int) -> int:
    return 1 + sum(size(c) for c in KIDS[g])


@functools.lru_cache(maxsize=None)
def splits(g: int) -> tuple[tuple[int, int], ...]:
    """(G_u, G - G_u) の組をすべて（形として重複を除いて）返す．u は根以外を動く."""
    ch = KIDS[g]
    out = set()
    for k in range(len(ch)):
        if k > 0 and ch[k] == ch[k - 1]:
            continue
        rest = ch[:k] + ch[k + 1:]
        out.add((ch[k], node(rest)))
        for (s, r) in splits(ch[k]):
            out.add((s, node(rest + (r,))))
    return tuple(sorted(out))


@functools.lru_cache(maxsize=None)
def F(g: int, S: int):
    if S <= 0:
        return INF
    if g == LEAF:
        return 1
    best = INF
    for (s, r) in splits(g):
        a = F(s, S - 1)
        if a == INF:
            continue
        b = F(r, S - 1)
        if b == INF:
            continue
        v = F(s, S) + a + b
        if v < best:
            best = v
    return best


def pmin(g: int) -> int:
    S = 1
    while F(g, S) == INF:
        S += 1
    return S


def Bt(h: int) -> int:
    g = LEAF
    for _ in range(h - 1):
        g = node((g, g))
    return g


def explicit(g: int):
    """形 g を頂点番号つきの木に展開する（根は 0）．children[v] を返す."""
    children: list[list[int]] = []

    def build(x):
        v = len(children)
        children.append([])
        for c in KIDS[x]:
            children[v].append(build(c))
        return v

    build(g)
    return children


def bfs_M(g: int, S: int):
    """全数探索による M(G,S)（頂点数 20 程度まで）."""
    ch = explicit(g)
    n = len(ch)
    need = [sum(1 << c for c in ch[v]) for v in range(n)]
    goal = 1
    dist = {0: 0}
    q = deque([0])
    while q:
        x = q.popleft()
        d = dist[x]
        if x == goal:
            return d
        pc = bin(x).count("1")
        for v in range(n):
            if (x & need[v]) != need[v]:
                continue
            bit = 1 << v
            if not (x & bit) and pc + 1 > S:
                continue
            y = x ^ bit
            if y not in dist:
                dist[y] = d + 1
                q.append(y)
    return INF


A000081 = [1, 1, 2, 4, 9, 20, 48, 115, 286, 719, 1842, 4766, 12486, 32973]


def all_rooted_trees(nmax: int) -> list[int]:
    """頂点数 nmax 以下の根付き木の形（子の数は制限しない）．個数を A000081 で自己検査する."""
    by = {1: [LEAF]}
    for n in range(2, nmax + 1):
        acc = set()

        def rec(rem, lo, kids):
            if rem == 0:
                acc.add(node(tuple(kids)))
                return
            for s in range(lo[0], rem + 1):
                for g in by[s]:
                    if (s, g) < lo:
                        continue
                    rec(rem - s, (s, g), kids + [g])

        rec(n - 1, (1, -1), [])
        by[n] = sorted(acc)
        assert len(by[n]) == A000081[n - 1], (n, len(by[n]))
    return [g for n in range(1, nmax + 1) for g in by[n]]
