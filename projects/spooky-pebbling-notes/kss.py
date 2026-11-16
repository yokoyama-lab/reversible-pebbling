#!/usr/bin/env python3
"""鎖上の 3 量（pebble / unpebble / unghost）の厳密最短手数を全数探索で出す。

KSS（Kornerup–Sadun–Soloveichik, *Tight Bounds on the Spooky Pebble Game*,
Quantum 9:1636 (2025), arXiv:2110.08973v3）の §4 が使う 3 量を、
**KSS の漸化式を使わずに** BFS で独立に出す。目的は 2 つ:

1. KSS の構造定理（Lemma 4.1 → Cor 4.7 / Cor 4.12 / Thm 4.11）を全数探索で検証する
2. KSS の体系で**閉じていない**部分（T_UP の厳密漸化式が無い）を、こちらで埋める

用語（KSS §4 の定義。線グラフ v_1 → … → v_n）:

| 量 | 始状態 | 終状態 |
|---|---|---|
| `T_P(n,s)`  | すべて空 | v_n にペブル、他は空、ゴースト無し |
| `T_UP(n,s)` | v_n にペブル、他は空 | すべて空 |
| `T_UG(n,s)` | v_n にゴースト、他は空 | すべて空 |

`s` はペブル上限（＝量子空間）。ゴースト（古典空間）に上限は掛けない。
遷移規則は Quist–Laarman LMCS 21:4 Definition 2.2（`spooky.py` と同じ逐語）。
"""
from __future__ import annotations

from collections import deque
from functools import lru_cache

from spooky import EMPTY, GHOST, PEBBLE, chain  # noqa: F401  （EMPTY は可読性のため）


def _digits(code: int, n: int) -> list[int]:
    out = []
    for _ in range(n):
        out.append(code % 3)
        code //= 3
    return out


def min_time_between(in_nodes: list[list[int]], pebble_cap: int,
                     start: int, goal: int) -> int | None:
    """状態 `start` から `goal` への最短手数。到達不能なら None。

    状態は基数 3 の符号（0=空 / 1=ペブル / 2=ゴースト）。`spooky.min_time` は
    始点と終点が固定なので、こちらは任意の 2 点間を測る（unpebble / unghost 用）。
    """
    n = len(in_nodes)
    pw = [3 ** i for i in range(n)]
    if start == goal:
        return 0
    dist = {start: 0}
    q = deque([start])
    while q:
        code = q.popleft()
        d = dist[code]
        st = _digits(code, n)
        npeb = sum(1 for x in st if x == PEBBLE)
        ready = [all(st[u] == PEBBLE for u in in_nodes[v]) for v in range(n)]
        for v in range(n):
            cur = st[v]
            moves = []
            if cur == EMPTY and ready[v] and npeb < pebble_cap:
                moves.append(code + pw[v] * PEBBLE)          # pebble
            elif cur == PEBBLE:
                if ready[v]:
                    moves.append(code - pw[v] * PEBBLE)      # unpebble
                moves.append(code + pw[v])                   # ghost（前提条件なし）
            elif cur == GHOST:
                if ready[v] and npeb < pebble_cap:
                    moves.append(code - pw[v])               # unghost
            for nxt in moves:
                if nxt not in dist:
                    if nxt == goal:
                        return d + 1
                    dist[nxt] = d + 1
                    q.append(nxt)
    return None


def _chain_states(n: int) -> tuple[int, int, int]:
    """(すべて空, v_n にペブル, v_n にゴースト) の符号。"""
    top = 3 ** (n - 1)
    return 0, top * PEBBLE, top * GHOST


@lru_cache(maxsize=None)
def T_P(n: int, s: int) -> int | None:
    """空 → v_n にペブル（KSS の T_P）。"""
    empty, peb, _ = _chain_states(n)
    return min_time_between(chain(n), s, empty, peb)


@lru_cache(maxsize=None)
def T_UP(n: int, s: int) -> int | None:
    """v_n にペブル → 空（KSS の T_UP）。"""
    empty, peb, _ = _chain_states(n)
    return min_time_between(chain(n), s, peb, empty)


@lru_cache(maxsize=None)
def T_UG(n: int, s: int) -> int | None:
    """v_n にゴースト → 空（KSS の T_UG）。"""
    empty, _, gho = _chain_states(n)
    return min_time_between(chain(n), s, gho, empty)


# --- KSS の漸化式（一次資料の逐語。検証用に、値は外から与える） ---

def cor47(n: int, s: int, T_up, T_p) -> float:
    """Cor 4.7 の右辺。`T_up` / `T_p` は (n,s) を取り float を返す関数。"""
    if n == 1:
        return 1 if s >= 1 else float("inf")
    if s < 3 and s < n:
        return float("inf")
    return min((2 * k - 1 + T_up(k, s - 1) + T_p(n - k, s - 1)
                for k in range(1, n)), default=float("inf"))


def cor412(n: int, s: int, T_up, T_ug) -> float:
    """Cor 4.12 の右辺。"""
    if n == 1:
        return 2 if s >= 1 else float("inf")
    if s < 2 and s < n:
        return float("inf")
    return min((2 * k - 1 + T_up(k, s) + T_ug(n - k, s - 1)
                for k in range(1, n + 1)), default=float("inf"))


def table(nmax: int = 12, smax: int = 5) -> None:
    print(f"{'n':>3} " + "".join(f"{'P' + str(s):>7}" for s in range(2, smax + 1))
          + "".join(f"{'UP' + str(s):>7}" for s in range(2, smax + 1))
          + "".join(f"{'UG' + str(s):>7}" for s in range(2, smax + 1)))
    for n in range(1, nmax + 1):
        row = f"{n:>3} "
        for f in (T_P, T_UP, T_UG):
            for s in range(2, smax + 1):
                v = f(n, s)
                row += f"{'-' if v is None else v:>7}"
        print(row)


if __name__ == "__main__":
    import sys
    a = [int(x) for x in sys.argv[1:]]
    table(*a) if a else table()
