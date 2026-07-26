"""標準（不可逆）ペブリングゲームの厳密 BFS エンジン。

`revpebble.py` の可逆版（toggle 規則: 取る操作にも先行点条件を課す）に対し、
標準版はペブルを**取る操作に先行点条件を課さない**（いつでも自由に取れる）。
置く操作の条件・clean 終端条件（目標頂点だけにペブルが残る状態）は可逆版と揃える
（idea02_separation_onset.md §3-2: 「比較の公平性のため」）。

`Dag` データ型・`_available`（先行点判定）は `revpebble.py` から再利用する
（`revpebble.py` は編集禁止・import のみ）。

候補2 の $P(G)$（標準ペブル数）は「clean に target へ到達できる最小ピーク $p$」
= `pmin_std(dag, target)`。$R(G)$ は `revpebble.pmin` そのもの。
"""

from __future__ import annotations

import sys
from collections import deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag, _available  # noqa: E402


def bfs_std(
    dag: Dag,
    target: int,
    p: int,
    *,
    with_parents: bool = False,
) -> tuple[int | None, dict | None]:
    """標準ペブリングの最小手数を BFS で厳密に求める。

    可逆版 `revpebble.bfs` との唯一の違い: 状態にペブルが載っている頂点は
    先行点条件を確認せず常に取り除ける（標準ペブリングの規則）。
    """
    start: frozenset[int] = frozenset()
    goal: frozenset[int] = frozenset({target})
    if target in dag.free:
        return (0, {} if with_parents else None)
    if p < 1:
        return (None, None)

    dist: dict[frozenset[int], int] = {start: 0}
    parent: dict[frozenset[int], tuple[frozenset[int], int]] = {}
    queue: deque[frozenset[int]] = deque([start])
    movable = dag.pebbleable()

    while queue:
        state = queue.popleft()
        d = dist[state]
        if state == goal:
            return (d, parent if with_parents else None)
        for v in movable:
            if v in state:
                # 標準ペブリング: 取る操作に先行点条件は無い。
                nxt = state - {v}
            else:
                if not _available(dag, state, v):
                    continue
                if len(state) + 1 > p:
                    continue
                nxt = state | {v}
            if nxt not in dist:
                dist[nxt] = d + 1
                if with_parents:
                    parent[nxt] = (state, v)
                queue.append(nxt)
    return (None, None)


def pmin_std(dag: Dag, target: int, pmax: int = 30) -> int | None:
    """clean に target へ到達できる最小ピーク p（標準ペブル数 P(G)）。"""
    for p in range(1, pmax + 1):
        moves, _ = bfs_std(dag, target, p)
        if moves is not None:
            return p
    return None


def mstar_std_chain(n: int, p: int | None = None) -> int | None:
    """鎖 chain(n) の標準ペブリングでの最小手数（p 省略時は p_min で評価）。"""
    from revpebble import chain

    g = chain(n)
    if p is None:
        p = pmin_std(g, n)
        if p is None:
            return None
    moves, _ = bfs_std(g, n, p)
    return moves


if __name__ == "__main__":  # 手動確認用
    from revpebble import chain, complete_binary_tree, pmin, pyramid

    print("標準ペブル数 P(chain n) n=1..10:")
    for n in range(1, 11):
        print(f"  n={n}: P={pmin_std(chain(n), n)}")

    print("標準 vs 可逆ペブル数 (complete binary tree, h=0..4):")
    for h in range(0, 5):
        g = complete_binary_tree(h)
        root = g.n - 1
        p_std = pmin_std(g, root)
        p_rev = pmin(g, root)
        print(f"  h={h}: P={p_std} R={p_rev}")

    print("標準ペブル数 P(pyramid h) h=0..4:")
    for h in range(0, 5):
        g = pyramid(h)
        root = g.n - 1
        print(f"  h={h}: P={pmin_std(g, root)}")
