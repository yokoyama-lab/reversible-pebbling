"""候補4: 実プログラム（0/1 ナップサック・行列連鎖乗算）の DP 依存 DAG の構造テスト。

`docs/50_pro_paper_plan.md` §3.D「実プログラムのメモ DAG」向け。
編集距離・LCS は既に `memo_dags.grid_dag` と同じ依存構造（先行点=左・上・左上）
なので新規に作らない。ナップサックと行列連鎖乗算は**依存構造そのものが違う**
（ナップサックは重み依存の可変ジャンプ、行列連鎖は区間 DP で高 in-degree）ので新規に作る。

実行: python3 tests/test_exp04_real_programs.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from real_program_dags import knapsack_dag, knapsack_target, mcm_dag, mcm_target  # noqa: E402
from revpebble import bfs, pmin  # noqa: E402


def test_knapsack_dag_structure() -> None:
    """dp[i][w] (i>=1) の先行点は dp[i-1][w] と（w>=weight[i-1] なら）dp[i-1][w-weight[i-1]]。

    dp[0][*] は free（base case: 品物0個なら価値0）。
    """
    weights = [2, 3, 1]
    capacity = 4
    g = knapsack_dag(weights, capacity)

    def idx(i: int, w: int) -> int:
        return i * (capacity + 1) + w

    assert g.n == (len(weights) + 1) * (capacity + 1)
    for w in range(capacity + 1):
        assert idx(0, w) in g.free
        assert g.preds[idx(0, w)] == frozenset()
    for i, wt in enumerate(weights, start=1):
        for w in range(capacity + 1):
            v = idx(i, w)
            expected = {idx(i - 1, w)}
            if w >= wt:
                expected.add(idx(i - 1, w - wt))
            assert g.preds[v] == frozenset(expected), (i, w, g.preds[v], expected)
    assert knapsack_target(weights, capacity) == idx(len(weights), capacity)


def test_mcm_dag_structure() -> None:
    """dp[i][j] (j>i) の先行点は { dp[i][k], dp[k+1][j] : i<=k<j }。dp[i][i] は free。"""
    n = 5
    g = mcm_dag(n)

    def idx(length: int, i: int) -> int:
        offset = length * n - length * (length - 1) // 2
        return offset + i

    for i in range(n):
        assert idx(0, i) in g.free
        assert g.preds[idx(0, i)] == frozenset()
    for length in range(1, n):
        for i in range(n - length):
            j = i + length
            v = idx(length, i)
            expected = set()
            for k in range(i, j):
                expected.add(idx(k - i, i))
                expected.add(idx(j - (k + 1), k + 1))
            assert g.preds[v] == frozenset(expected), (length, i, g.preds[v], expected)
    assert mcm_target(n) == idx(n - 1, 0)


# --- 小さい厳密値の回帰テスト（revpebble.bfs で実測して確定した値） -----------


def test_knapsack_dag_small_values() -> None:
    weights = [1, 2]
    capacity = 3
    g = knapsack_dag(weights, capacity)
    t = knapsack_target(weights, capacity)
    p = pmin(g, t)
    assert p is not None
    m, _ = bfs(g, t, p)
    assert m is not None
    # 素朴 BFS で実測した厳密値を固定する（2026-07-27）
    assert (p, m) == (3, 5), (p, m)


def test_mcm_dag_small_values() -> None:
    g = mcm_dag(4)
    t = mcm_target(4)
    p = pmin(g, t)
    assert p is not None
    m, _ = bfs(g, t, p)
    assert m is not None
    assert (p, m) == (5, 15), (p, m)


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"ok   {name}")
            except AssertionError as exc:
                failures += 1
                print(f"FAIL {name}: {exc}")
    sys.exit(1 if failures else 0)
