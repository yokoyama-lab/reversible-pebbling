"""候補4: 双方向 BFS（frontierdp_memo.bidir_bfs）が素朴 BFS（revpebble.bfs）と
全点一致することの回帰テスト。

方針（`docs/10_method_toolkit.md` (2) 二重実装で照合）: 素朴 BFS が届く全域で、
target の p_min から p_min+3 まで、あらゆる p について両実装が同じ手数を返すことを
確認する。1点でも不一致なら bidir_bfs は信用できないので、以後その値は使わない。

実行: python3 tests/test_exp04_frontier.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from frontierdp_memo import bidir_bfs, pmin_bidir  # noqa: E402
from memo_dags import fib_dag, grid_dag, grid_target, pascal_dag, pascal_target  # noqa: E402
from real_program_dags import knapsack_dag, knapsack_target, mcm_dag, mcm_target  # noqa: E402
from revpebble import bfs, chain, complete_binary_tree, pmin, pyramid  # noqa: E402


def _cross_check(g, target: int, pmax_extra: int = 3) -> None:
    p0 = pmin(g, target)
    p0b = pmin_bidir(g, target)
    assert p0 == p0b, (g.name, "p_min", p0, p0b)
    if p0 is None:
        return
    for p in range(1, p0 + pmax_extra + 1):
        want, _ = bfs(g, target, p)
        got = bidir_bfs(g, target, p)
        assert got == want, (g.name, p, "want", want, "got", got)


def test_bidir_matches_naive_on_fib() -> None:
    for n in range(1, 22):  # 素朴 BFS が軽く届く範囲（pebbleable <= 21）
        g = fib_dag(n)
        _cross_check(g, n)


def test_bidir_matches_naive_on_grid() -> None:
    for k in range(1, 6):  # grid(5,5) まで（pebbleable=16、素朴 BFS が届く上限）
        g = grid_dag(k, k)
        _cross_check(g, grid_target(k, k))


def test_bidir_matches_naive_on_pascal() -> None:
    for n in range(1, 7):
        g = pascal_dag(n)
        _cross_check(g, pascal_target(n))


def test_bidir_matches_naive_on_chain() -> None:
    """帯幅1（既存の鎖）でも一致することを確認（回帰の土台）。"""
    for n in range(1, 15):
        g = chain(n)
        _cross_check(g, n)


def test_bidir_matches_naive_on_trees() -> None:
    """木・ピラミッドでも一致することを確認（線形構造以外でも正しいか）。"""
    for h in range(1, 4):
        g = complete_binary_tree(h)
        _cross_check(g, g.n - 1)
    for h in range(1, 5):
        g = pyramid(h)
        _cross_check(g, g.n - 1)


def test_bidir_matches_naive_on_knapsack() -> None:
    """依存構造が違う実プログラム DAG（重み依存の可変ジャンプ）でも一致するか。"""
    for cap in [3, 5, 7]:
        for weights in ([1, 2, 3], [2, 3, 4, 1], [1, 1, 2, 3, 5]):
            g = knapsack_dag(weights, cap)
            if len(g.pebbleable()) > 17:
                continue
            _cross_check(g, knapsack_target(weights, cap))


def test_bidir_matches_naive_on_mcm() -> None:
    """区間 DP（先行点が区間長に比例して増える高 in-degree）でも一致するか。"""
    for n in range(2, 7):
        g = mcm_dag(n)
        if len(g.pebbleable()) > 17:
            continue
        _cross_check(g, mcm_target(n))


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
