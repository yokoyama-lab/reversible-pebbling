"""候補4: メモ化 DP の依存関係を DAG として生成する関数群。

revpebble.Dag を返す。頂点はトポロジカル順（u < v）に番号付けする。
このモジュールは DAG の**定義**のみを持つ。BFS/DP のロジックは revpebble.py
（読むだけ・編集禁止）と exp04_memo_dags.py 側に置く。
"""

from __future__ import annotations

from revpebble import Dag


def fib_dag(n: int) -> Dag:
    """Fibonacci 型 DAG。頂点 0..n、頂点 v (v>=2) の先行点は {v-1, v-2}。

    頂点 0, 1 は free（base case, 常時利用可能）。帯幅2。target は頂点 n。
    """
    if n < 1:
        raise ValueError("n >= 1 が必要")
    preds: list[frozenset[int]] = [frozenset(), frozenset()]
    for v in range(2, n + 1):
        preds.append(frozenset({v - 1, v - 2}))
    return Dag(n=n + 1, preds=tuple(preds), free=frozenset({0, 1}), name=f"fib({n})")


def grid_dag(m: int, n: int) -> Dag:
    """m x n グリッド DAG（編集距離型）。セル (i,j) の先行点は左・上・左上。

    境界（i==0 または j==0）は free。番号付けは行優先: idx(i,j) = i*n + j
    （u < v が保たれる: 前の行・同じ行の前の列は必ず小さい番号）。
    target は右下隅 (m-1, n-1)。
    """
    if m < 1 or n < 1:
        raise ValueError("m,n >= 1 が必要")

    def idx(i: int, j: int) -> int:
        return i * n + j

    preds: list[frozenset[int]] = []
    free: set[int] = set()
    for i in range(m):
        for j in range(n):
            if i == 0 or j == 0:
                preds.append(frozenset())
                free.add(idx(i, j))
            else:
                preds.append(frozenset({idx(i - 1, j - 1), idx(i - 1, j), idx(i, j - 1)}))
    return Dag(n=m * n, preds=tuple(preds), free=frozenset(free), name=f"grid({m},{n})")


def grid_target(m: int, n: int) -> int:
    """grid_dag(m, n) の右下隅の頂点番号。"""
    return m * n - 1


def pascal_dag(n: int) -> Dag:
    """パスカルの三角形 DAG。行 i=0..n、列 k=0..i。

    C(i,k) の先行点は C(i-1,k-1), C(i-1,k)。三角形の縁（k==0 または k==i、
    常に 1 なので計算不要な base case）は free。番号付けは行優先:
    idx(i,k) = i*(i+1)/2 + k（前の行は必ず小さい番号）。
    """
    if n < 0:
        raise ValueError("n >= 0 が必要")

    def idx(i: int, k: int) -> int:
        return i * (i + 1) // 2 + k

    preds: list[frozenset[int]] = []
    free: set[int] = set()
    for i in range(n + 1):
        for k in range(i + 1):
            if k == 0 or k == i:
                preds.append(frozenset())
                free.add(idx(i, k))
            else:
                preds.append(frozenset({idx(i - 1, k - 1), idx(i - 1, k)}))
    return Dag(n=idx(n, n) + 1, preds=tuple(preds), free=frozenset(free), name=f"pascal({n})")


def pascal_target(n: int, k: int | None = None) -> int:
    """pascal_dag(n) 内の C(n,k) の頂点番号。k 省略時は中央 (n//2)。"""
    if k is None:
        k = n // 2
    if not (0 <= k <= n):
        raise ValueError("0 <= k <= n が必要")
    return n * (n + 1) // 2 + k
