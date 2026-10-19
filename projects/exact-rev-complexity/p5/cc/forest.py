#!/usr/bin/env python3
"""森の多目標の距離 d_B(∅,X) と領域・Ψ・鎖への並べ方の下界 L（標準ライブラリだけ）.

森は親の配列 par（-1 は成分の根）で表す．頂点 v を置く／外す手は v の子がすべて盤にあるときだけ合法．
"""
from __future__ import annotations

import functools
import itertools
import sys
from collections import deque

sys.path.insert(0, __file__.rsplit("/", 2)[0] + "/lb")
from chain import Fc_dp, INF  # noqa: E402


def children(par):
    ch = [[] for _ in par]
    for v, p in enumerate(par):
        if p >= 0:
            ch[p].append(v)
    return ch


def bfs_all(par, B, alive=None):
    n = len(par)
    if alive is None:
        alive = (1 << n) - 1
    need = [0] * n
    for v, p in enumerate(par):
        if p >= 0 and (alive >> v) & 1:
            need[p] |= 1 << v
    dist = {0: 0}
    q = deque([0])
    while q:
        x = q.popleft()
        d = dist[x]
        pc = bin(x).count("1")
        for v in range(n):
            if not (alive >> v) & 1:
                continue
            if x & need[v] != need[v]:
                continue
            if not (x >> v) & 1 and pc + 1 > B:
                continue
            y = x ^ (1 << v)
            if y not in dist:
                dist[y] = d + 1
                q.append(y)
    return dist


def regions(par, X, alive=None):
    """X の各元 x の領域の頂点数と，x の上の領域の代表（無ければ -1）."""
    n = len(par)
    if alive is None:
        alive = (1 << n) - 1

    @functools.lru_cache(None)
    def rep(v):
        if (X >> v) & 1:
            return v
        p = par[v]
        if p < 0 or not (alive >> p) & 1:
            return -1
        return rep(p)

    size = {x: 0 for x in range(n) if (X >> x) & 1 and (alive >> x) & 1}
    up = {}
    for v in range(n):
        if not (alive >> v) & 1:
            continue
        r = rep(v)
        if r >= 0:
            size[r] += 1
    for x in size:
        p = par[x]
        up[x] = rep(p) if p >= 0 and (alive >> p) & 1 else -1
    return size, up


def psi(sizes, B):
    s = 0
    for i, m in enumerate(sorted(sizes, reverse=True)):
        if m == 0:
            continue
        f = Fc_dp(m, B - i) if B - i > 0 else INF
        if f == INF:
            return INF
        s += f
    return s


def load_forest(tid, path):
    for line in open(path):
        xs = line.split()
        if xs and xs[0] == str(tid):
            return [int(p) - 1 for p in xs[2:]]
    raise KeyError(tid)


def decompositions(par, C, B):
    """補題 D の (c, P) をすべて列挙し，(c, P, pre, post, 最適か, INEQ(Ψ) を満たすか) を返す."""
    n = len(par)
    ch = children(par)
    k = bin(C).count("1")
    D = bfs_all(par, B)
    alive2 = ((1 << n) - 1) & ~C
    par2 = [(-1 if (p >= 0 and (C >> p) & 1) else p) for p in par]
    D2 = bfs_all(par2, B - k, alive2)
    d = D.get(C, INF)
    tgt = psi(list(regions(par, C)[0].values()), B)
    out = []
    for c in range(n):
        if not (C >> c) & 1:
            continue
        base = (C & ~(1 << c))
        for u in ch[c]:
            base |= 1 << u
        free = [v for v in range(n) if not (base >> v) & 1 and v != c]
        for r in range(len(free) + 1):
            for sub in itertools.combinations(free, r):
                P = base
                for v in sub:
                    P |= 1 << v
                if bin(P).count("1") > B - 1:
                    continue
                pre = D.get(P, INF)
                post = D2.get(P & ~C, INF)
                if pre == INF or post == INF:
                    continue
                lp = psi(list(regions(par, P)[0].values()), B)
                lq = psi(list(regions(par2, P & ~C, alive2)[0].values()), B - k)
                ok = 1 + lp + lq >= tgt
                out.append((c, P, pre, post, 1 + pre + post == d, ok, lp, lq))
    return d, tgt, out
