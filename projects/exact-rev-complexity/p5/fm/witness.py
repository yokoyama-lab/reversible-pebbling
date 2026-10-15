#!/usr/bin/env python3
"""反例の証人: 木 T と S について，BFS で最短手順を取り出し，独立の検査器で再生する.

使い方: python3 witness.py '<形>' S
  形は ftree.show の書式（"." が葉，"(...)" が子を並べた頂点）．

出力: 最短手数 M（BFS，経路つき），F(T,S)（ftree），手順（頂点番号の列），検査器の判定．
検査器 replay() は bfs_m.c とも ftree.F とも独立に，規則を素朴に書き下したもの．
"""

from __future__ import annotations

import sys
from collections import deque

import ftree as ft


def parse(s: str) -> int:
    pos = 0

    def rec() -> int:
        nonlocal pos
        if s[pos] == ".":
            pos += 1
            return ft.LEAF
        assert s[pos] == "("
        pos += 1
        kids = []
        while s[pos] != ")":
            kids.append(rec())
        pos += 1
        return ft.node(kids)

    g = rec()
    assert pos == len(s), "trailing input"
    return g


def bfs_path(par: list[int], S: int):
    n = len(par)
    need = [0] * n
    for i in range(1, n):
        need[par[i]] |= 1 << i
    prev = {0: None}
    q = deque([0])
    while q:
        x = q.popleft()
        if x == 1:
            break
        pc = bin(x).count("1")
        for v in range(n):
            if x & need[v] != need[v]:
                continue
            if not (x >> v) & 1 and pc + 1 > S:
                continue
            y = x ^ (1 << v)
            if y not in prev:
                prev[y] = (x, v)
                q.append(y)
    if 1 not in prev:
        return None
    moves = []
    x = 1
    while prev[x] is not None:
        x, v = prev[x]
        moves.append(v)
    return moves[::-1]


def replay(par: list[int], S: int, moves: list[int]) -> tuple[bool, str]:
    """規則を素朴に書き下した検査器．"""
    n = len(par)
    children = {v: [i for i in range(n) if par[i] == v] for v in range(n)}
    peb = set()
    peak = 0
    for t, v in enumerate(moves, 1):
        if not (0 <= v < n):
            return False, f"step {t}: bad vertex {v}"
        for c in children[v]:
            if c not in peb:
                return False, f"step {t}: child {c} of {v} not pebbled"
        if v in peb:
            peb.remove(v)
        else:
            peb.add(v)
        peak = max(peak, len(peb))
        if len(peb) > S:
            return False, f"step {t}: {len(peb)} pebbles > S={S}"
    if peb != {0}:
        return False, f"final configuration {sorted(peb)} != {{root}}"
    return True, f"ok: {len(moves)} moves, peak {peak} pebbles, final {{root}}"


def main():
    g = parse(sys.argv[1])
    S = int(sys.argv[2])
    par = ft.parents(g)
    print(f"tree {ft.show(g)}  n={len(par)}  S={S}")
    print("parent array:", par)
    f = ft.F(g, S)
    moves = bfs_path(par, S)
    print(f"F(T,S) = {f}")
    print(f"M(T,S) = {len(moves) if moves is not None else 'inf'} (BFS with path)")
    if moves is not None:
        print("moves:", " ".join(map(str, moves)))
        ok, msg = replay(par, S, moves)
        print("replay:", msg)
        # 1 手少ない長さで到達できないこと（BFS の最短性）は BFS 自体が保証する．
        if ok and len(moves) < f:
            print(f"COUNTEREXAMPLE: M <= {len(moves)} < F = {f}")


if __name__ == "__main__":
    main()
