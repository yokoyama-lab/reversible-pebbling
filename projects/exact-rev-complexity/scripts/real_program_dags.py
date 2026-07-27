"""候補4: 実プログラム（DP アルゴリズム）の依存関係を DAG として生成する関数群。

`docs/50_pro_paper_plan.md` §3.D「実プログラムのメモ DAG」向け。
編集距離・LCS は `memo_dags.grid_dag` と依存構造が同一（先行点=左・上・左上）なので
ここでは作らない。**依存構造そのものが異なる**2つを追加する:

- **0/1 ナップサック**: dp[i][w] の先行点は dp[i-1][w] と（品物 i-1 の重み次第で）
  dp[i-1][w-weight[i-1]]。**ジャンプ幅が品物ごとに変わる**（fib/grid の固定オフセットと違う）。
- **行列連鎖乗算**: dp[i][j] の先行点は区間分割点 k ごとの dp[i][k], dp[k+1][j]。
  **in-degree が区間長に比例**（fib/grid は先行点が定数個）。
"""

from __future__ import annotations

from revpebble import Dag


def knapsack_dag(weights: list[int], capacity: int) -> Dag:
    """0/1 ナップサック DP の依存 DAG。

    頂点 idx(i,w) = i*(capacity+1)+w（i=0..len(weights), w=0..capacity）。
    dp[0][*] は free（品物0個なら価値0、計算不要）。
    dp[i][w] (i>=1) の先行点は dp[i-1][w] と、w >= weights[i-1] なら
    dp[i-1][w-weights[i-1]] も加える。
    """
    if capacity < 0:
        raise ValueError("capacity >= 0 が必要")
    if any(wt < 1 for wt in weights):
        raise ValueError("weights はすべて 1 以上が必要（0 は自己依存になる）")

    def idx(i: int, w: int) -> int:
        return i * (capacity + 1) + w

    n_items = len(weights)
    total = (n_items + 1) * (capacity + 1)
    preds: list[frozenset[int]] = [frozenset() for _ in range(total)]
    free: set[int] = set()
    for w in range(capacity + 1):
        free.add(idx(0, w))
    for i, wt in enumerate(weights, start=1):
        for w in range(capacity + 1):
            v = idx(i, w)
            ps = {idx(i - 1, w)}
            if w >= wt:
                ps.add(idx(i - 1, w - wt))
            preds[v] = frozenset(ps)
    return Dag(n=total, preds=tuple(preds), free=frozenset(free), name=f"knapsack({weights},{capacity})")


def knapsack_target(weights: list[int], capacity: int) -> int:
    """knapsack_dag(weights, capacity) の最終解 dp[len(weights)][capacity] の頂点番号。"""
    return len(weights) * (capacity + 1) + capacity


def mcm_dag(n: int) -> Dag:
    """行列連鎖乗算 DP（区間 DP）の依存 DAG。n 個の行列（乗算 n-1 回）。

    頂点は区間長 l=j-i と開始 i の組 (l,i)（l=0..n-1, i=0..n-1-l）。
    番号付けは l を primary key に昇順（先行点は常に短い区間 = 小さい l なので u<v）。
    dp[i][i]（l=0, 単一行列）は free（コスト0、計算不要）。
    dp[i][j]（l=j-i>=1）の先行点は分割点 k=i..j-1 ごとの dp[i][k], dp[k+1][j]。
    """
    if n < 1:
        raise ValueError("n >= 1 が必要")

    def offset(length: int) -> int:
        return length * n - length * (length - 1) // 2

    def idx(length: int, i: int) -> int:
        return offset(length) + i

    total = offset(n)  # l=0..n-1 の頂点数合計 = n + (n-1) + ... + 1 = n(n+1)/2
    preds: list[frozenset[int]] = [frozenset() for _ in range(total)]
    free: set[int] = set()
    for i in range(n):
        free.add(idx(0, i))
    for length in range(1, n):
        for i in range(n - length):
            j = i + length
            v = idx(length, i)
            ps: set[int] = set()
            for k in range(i, j):
                ps.add(idx(k - i, i))
                ps.add(idx(j - (k + 1), k + 1))
            preds[v] = frozenset(ps)
    return Dag(n=total, preds=tuple(preds), free=frozenset(free), name=f"mcm({n})")


def mcm_target(n: int) -> int:
    """mcm_dag(n) の最終解 dp[0][n-1] の頂点番号。"""
    return (n - 1) * n - (n - 1) * (n - 2) // 2 + 0
