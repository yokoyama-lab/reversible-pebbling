"""候補4: memo_dags.py の DAG 生成関数のテスト。

構造テスト（先行点・free 集合が定義どおりか）と、revpebble エンジンで
実測して確定した厳密値の回帰テスト（tests/test_revpebble.py と同じ流儀）。
実行: python3 tests/test_exp04_memo_dags.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from memo_dags import (  # noqa: E402
    fib_dag,
    grid_dag,
    grid_target,
    pascal_dag,
    pascal_target,
)
from revpebble import bfs, pmin  # noqa: E402

# --- 構造テスト -------------------------------------------------------------


def test_fib_dag_structure() -> None:
    """fib_dag(n): 頂点 0,1 が free、v>=2 の先行点が {v-1,v-2}。"""
    g = fib_dag(6)
    assert g.n == 7
    assert g.free == frozenset({0, 1})
    assert g.preds[0] == frozenset() and g.preds[1] == frozenset()
    for v in range(2, 7):
        assert g.preds[v] == frozenset({v - 1, v - 2}), v


def test_grid_dag_structure() -> None:
    """grid_dag(m,n): 境界が free、内部セルの先行点が左・上・左上。"""
    m, n = 3, 4
    g = grid_dag(m, n)
    assert g.n == m * n

    def idx(i: int, j: int) -> int:
        return i * n + j

    for i in range(m):
        for j in range(n):
            v = idx(i, j)
            if i == 0 or j == 0:
                assert v in g.free
                assert g.preds[v] == frozenset()
            else:
                assert v not in g.free
                assert g.preds[v] == frozenset({idx(i - 1, j - 1), idx(i - 1, j), idx(i, j - 1)})
    assert grid_target(m, n) == m * n - 1


def test_pascal_dag_structure() -> None:
    """pascal_dag(n): 三角形の縁 (k=0,k=i) が free、内部は二項係数の再帰。"""
    n = 5
    g = pascal_dag(n)

    def idx(i: int, k: int) -> int:
        return i * (i + 1) // 2 + k

    assert g.n == idx(n, n) + 1
    for i in range(n + 1):
        for k in range(i + 1):
            v = idx(i, k)
            if k == 0 or k == i:
                assert v in g.free
                assert g.preds[v] == frozenset()
            else:
                assert v not in g.free
                assert g.preds[v] == frozenset({idx(i - 1, k - 1), idx(i - 1, k)})
    assert pascal_target(n) == idx(n, n // 2)
    assert pascal_target(n, k=1) == idx(n, 1)


# --- 厳密値の回帰テスト（revpebble.bfs で実測して確定した値） ----------------

# fib_dag(n) の p_min・M*（p_min で評価）。n=1..16。
# 2026-07-27 に scripts/memo_dags.py + revpebble.bfs で実測して確定（素朴 BFS、budget<=15 頂点）。
FIB_PMIN = [1, 1, 2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7]
FIB_MSTAR = [0, 1, 3, 5, 7, 11, 13, 17, 19, 23, 27, 33, 33, 37, 43, 51]


def test_fib_dag_small_values() -> None:
    for n, (want_p, want_m) in enumerate(zip(FIB_PMIN, FIB_MSTAR), start=1):
        g = fib_dag(n)
        p = pmin(g, n)
        assert p == want_p, (n, p, want_p)
        m, _ = bfs(g, n, p)
        assert m == want_m, (n, m, want_m)


# grid_dag(m,n) の p_min・M*（正方 m=n=2..4、素朴 BFS で実測して確定）。
GRID_SQUARE = {
    2: (1, 1),
    3: (4, 7),
    4: (6, 25),
}


def test_grid_dag_small_values() -> None:
    for k, (want_p, want_m) in GRID_SQUARE.items():
        g = grid_dag(k, k)
        t = grid_target(k, k)
        p = pmin(g, t)
        assert p == want_p, (k, p, want_p)
        m, _ = bfs(g, t, p)
        assert m == want_m, (k, m, want_m)


# pascal_dag(n) の中央二項係数 C(n, n//2) への p_min・M*（素朴 BFS で実測して確定）。
PASCAL_CENTER = {
    2: (1, 1),
    3: (2, 3),
    4: (4, 7),
    5: (5, 13),
    6: (6, 23),
}


def test_pascal_dag_small_values() -> None:
    for n, (want_p, want_m) in PASCAL_CENTER.items():
        g = pascal_dag(n)
        t = pascal_target(n)
        p = pmin(g, t)
        assert p == want_p, (n, p, want_p)
        m, _ = bfs(g, t, p)
        assert m == want_m, (n, m, want_m)


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
