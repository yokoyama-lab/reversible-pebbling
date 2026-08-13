#!/usr/bin/env python3
"""最適な unpebble / unghost の手順を復元して表示する（θ の前後の比較用）。

    python3 witness_up.py 9 4     # n=9, s=4 の T_UP と T_UG の最適手順
    python3 witness_up.py 10 4    # θ(4)=10 の側

見たいのは「$v_n$ のペブルをいつ、どう手放すか」。θ の前後で最適手順が
何を変えるのかが、符号 $T_{UG}-T_{UP}=\\pm1$ の理由になっているはず。
"""
from __future__ import annotations

import sys
from collections import deque

from spooky import EMPTY, GHOST, PEBBLE, chain

NAME = {(EMPTY, PEBBLE): "pebble", (PEBBLE, EMPTY): "unpebble",
        (PEBBLE, GHOST): "ghost", (GHOST, PEBBLE): "unghost"}


def _digits(code: int, n: int) -> list[int]:
    out = []
    for _ in range(n):
        out.append(code % 3)
        code //= 3
    return out


def shortest_path(n: int, s: int, start: int, goal: int) -> list[str] | None:
    in_nodes = chain(n)
    pw = [3 ** i for i in range(n)]
    prev: dict[int, tuple[int, str]] = {}
    dist = {start: 0}
    q = deque([start])
    while q:
        code = q.popleft()
        if code == goal:
            break
        st = _digits(code, n)
        npeb = sum(1 for x in st if x == PEBBLE)
        ready = [all(st[u] == PEBBLE for u in in_nodes[v]) for v in range(n)]
        for v in range(n):
            cur = st[v]
            nxts = []
            if cur == EMPTY and ready[v] and npeb < s:
                nxts.append((code + pw[v] * PEBBLE, PEBBLE))
            elif cur == PEBBLE:
                if ready[v]:
                    nxts.append((code - pw[v] * PEBBLE, EMPTY))
                nxts.append((code + pw[v], GHOST))
            elif cur == GHOST and ready[v] and npeb < s:
                nxts.append((code - pw[v], PEBBLE))
            for nxt, to in nxts:
                if nxt not in dist:
                    dist[nxt] = dist[code] + 1
                    prev[nxt] = (code, f"{NAME[(cur, to)]}(v{v + 1})")
                    q.append(nxt)
    if goal not in dist:
        return None
    seq = []
    cur = goal
    while cur != start:
        p, op = prev[cur]
        seq.append(op)
        cur = p
    return seq[::-1]


def show(n: int, s: int) -> None:
    top = 3 ** (n - 1)
    for label, start in (("T_UP（v_n にペブル → 空）", top * PEBBLE),
                         ("T_UG（v_n にゴースト → 空）", top * GHOST)):
        seq = shortest_path(n, s, start, 0)
        if seq is None:
            print(f"\n### {label}: 到達不能")
            continue
        vn = [i for i, op in enumerate(seq) if op.endswith(f"(v{n})")]
        print(f"\n### {label}  n={n} s={s}  → {len(seq)} 手")
        print(f"  v{n} に触る手: {[(i, seq[i]) for i in vn]}")
        print("  " + " ".join(seq))


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[1:]] or [9, 4]
    show(a[0], a[1])
