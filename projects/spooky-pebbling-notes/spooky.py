#!/usr/bin/env python3
"""spooky pebble game の厳密最短時間を BFS で求める（一般 DAG）。

定義は Quist–Laarman, LMCS 21:4 (arXiv 2401.10579) Definition 2.2 の逐語:
  状態は (P_t, S_t)（ペブルとゴースト）。P_0=S_0=∅、P_T=R（根＝出次数0）、S_T=∅。
  各ステップで 1 頂点 v について次のいずれか:
    pebble(v)  : P += v, S 不変, v の全 in-node が P_{t-1} にある
    unpebble(v): P -= v, S 不変, v の全 in-node が P_{t-1} にある
    ghost(v)   : P -= v, S += v                      （前提条件なし）
    unghost(v) : P += v, S -= v, v の全 in-node が P_{t-1} にある
  pebbling time = T、pebbling cost = max|P_t|（量子空間）、
  ghosting cost = max|S_t|（古典空間）。

ghost/unghost を禁じると Knill の可逆ペブルゲーム F(n,S) に一致する。
これを校正アンカーとして実装を検証する（tests を先に書くこと）。
"""
from __future__ import annotations

from collections import deque

EMPTY, PEBBLE, GHOST = 0, 1, 2


def chain(n: int) -> list[list[int]]:
    """長さ n の鎖 0→1→…→(n-1)。in_nodes[v] を返す。"""
    return [[] if v == 0 else [v - 1] for v in range(n)]


def roots(in_nodes: list[list[int]]) -> list[int]:
    """出次数 0 の頂点（＝どの in_nodes にも現れない頂点）。"""
    has_out = {u for ins in in_nodes for u in ins}
    return [v for v in range(len(in_nodes)) if v not in has_out]


def _digits(code: int, n: int) -> list[int]:
    out = []
    for _ in range(n):
        out.append(code % 3)
        code //= 3
    return out


def min_time(in_nodes: list[list[int]], pebble_cap: int,
             ghost_cap: int | None = None, spooky: bool = True) -> int | None:
    """初期 ∅ から (P=R, S=∅) への最短手数。到達不能なら None。

    pebble_cap / ghost_cap は全時刻で守られる（cost は max なので状態制約でよい）。
    spooky=False で ghost/unghost を禁じる＝可逆ペブルゲーム。
    """
    n = len(in_nodes)
    pw = [3 ** i for i in range(n)]
    target = sum(pw[v] * PEBBLE for v in roots(in_nodes))

    start = 0
    if start == target:
        return 0
    dist = {start: 0}
    q = deque([start])
    while q:
        code = q.popleft()
        d = dist[code]
        st = _digits(code, n)
        npeb = sum(1 for x in st if x == PEBBLE)
        ngho = sum(1 for x in st if x == GHOST)
        ready = [all(st[u] == PEBBLE for u in in_nodes[v]) for v in range(n)]
        for v in range(n):
            cur = st[v]
            moves = []
            if cur == EMPTY and ready[v] and npeb < pebble_cap:
                moves.append(code + pw[v] * PEBBLE)             # pebble
            elif cur == PEBBLE:
                if ready[v]:
                    moves.append(code - pw[v] * PEBBLE)         # unpebble
                if spooky and (ghost_cap is None or ngho < ghost_cap):
                    moves.append(code + pw[v])                  # ghost (1→2)
            elif cur == GHOST and spooky:
                if ready[v] and npeb < pebble_cap:
                    moves.append(code - pw[v])                  # unghost (2→1)
            for nxt in moves:
                if nxt not in dist:
                    if nxt == target:
                        return d + 1
                    dist[nxt] = d + 1
                    q.append(nxt)
    return None


def knill_F(n: int, S: int) -> int | None:
    """Knill の再帰 F(n,S)=min_m[F(m,S)+F(m,S-1)+F(n-m,S-1)], F(1,S)=1。

    BFS の独立 2 実装（照合用）。n > 2^(S-1) では None。
    """
    from functools import lru_cache

    @lru_cache(maxsize=None)
    def F(n: int, S: int) -> float:
        if S < 1:
            return float("inf")
        if n == 1:
            return 1
        if n > 2 ** (S - 1):
            return float("inf")
        return min(F(m, S) + F(m, S - 1) + F(n - m, S - 1)
                   for m in range(1, n))

    v = F(n, S)
    return None if v == float("inf") else int(v)
