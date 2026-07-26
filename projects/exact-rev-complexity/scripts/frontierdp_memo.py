"""候補4: 素朴 BFS の壁を超えるための厳密アルゴリズム（双方向 BFS）。

## 背景（なぜ「窓幅一定のフロンティア DP」ではないか）

当初「フロンティア DP（局所窓の状態だけを持つ）」を狙ったが、`revpebble.py` の
toggle 規則を確認すると **ペブルを取る操作にも先行点が利用可能である必要がある**
（`_available` は put/take 両方に課される）。これは「一度置いたペブルは、置いた
ときの根拠（先行点）が残っている間しか取れない」という制約であり、鎖の
Bennett/Knill 再帰が非自明な理由そのもの: 最適スケジュールは局所的な「直近 k 頂点」
の窓には収まらず、離れた位置に「チェックポイント」を再帰的に保持する
（二分再帰）。したがって固定幅の窓オートマトンは**そもそも真の最適値に到達できない
可能性が高く**、これを「フロンティア DP」として実装すると不正な外挿値を出す危険がある。

## 採用した方法: 双方向 BFS（meet-in-the-middle）

toggle 操作は対称（v を toggle する前提条件は toggle 前後で不変）なので、
状態遷移グラフは**無向**。よって `bfs` の片側探索を、始点側・終点側からの
交互展開に置き換えても**同じ厳密最短路長**が得られる（近似ではない）。
片側探索の探索半径が実質半分になるため、状態数が指数的に減る
（分岐因子 $F$、直径 $D$ のとき $F^D \to 2F^{D/2}$ 程度）。

この関数が `revpebble.bfs` と**全く同じ値**を返すことを、素朴 BFS が届く全域
（`tests/test_exp04_frontier.py`）で確認してから、素朴 BFS が届かない領域に使う。
"""

from __future__ import annotations

from revpebble import Dag, _available  # noqa: E402  (revpebble を読むだけ、編集しない)


def bidir_bfs(dag: Dag, target: int, p: int) -> int | None:
    """revpebble.bfs と同じ厳密最短手数を双方向 BFS で計算する。

    停止規則（Pohl の双方向探索の標準規則を無重みグラフに特化したもの）:
    両側とも深さ d_f, d_b まで**完全に**展開済みのとき、これ以上展開しても
    見つかる交差点の距離和は d_f + d_b 以上にしかならない。したがって
    既知の最良解 mu が mu <= d_f + d_b を満たした時点で停止してよい。
    """
    start: frozenset[int] = frozenset()
    goal: frozenset[int] = frozenset({target})
    if target in dag.free:
        return 0
    if p < 1:
        return None
    if start == goal:
        return 0

    movable = dag.pebbleable()

    dist_f: dict[frozenset[int], int] = {start: 0}
    dist_b: dict[frozenset[int], int] = {goal: 0}
    frontier_f: list[frozenset[int]] = [start]
    frontier_b: list[frozenset[int]] = [goal]
    d_f = 0
    d_b = 0
    mu: int | None = dist_b.get(start)  # start happens to be goal? already excluded above
    if goal in dist_f:
        mu = dist_f[goal]

    def expand(
        frontier: list[frozenset[int]],
        dist_this: dict[frozenset[int], int],
        dist_other: dict[frozenset[int], int],
        d_new: int,
    ) -> tuple[list[frozenset[int]], int | None]:
        nxt: list[frozenset[int]] = []
        best: int | None = None
        for state in frontier:
            for v in movable:
                if not _available(dag, state, v):
                    continue
                if v in state:
                    ns = state - {v}
                else:
                    if len(state) + 1 > p:
                        continue
                    ns = state | {v}
                if ns in dist_this:
                    continue
                dist_this[ns] = d_new
                if ns in dist_other:
                    cand = d_new + dist_other[ns]
                    if best is None or cand < best:
                        best = cand
                nxt.append(ns)
        return nxt, best

    turn_forward = True
    while frontier_f and frontier_b:
        if mu is not None and d_f + d_b >= mu:
            break
        if turn_forward:
            d_f += 1
            frontier_f, found = expand(frontier_f, dist_f, dist_b, d_f)
        else:
            d_b += 1
            frontier_b, found = expand(frontier_b, dist_b, dist_f, d_b)
        turn_forward = not turn_forward
        if found is not None and (mu is None or found < mu):
            mu = found

    return mu


def pmin_bidir(dag: Dag, target: int, pmax: int = 40) -> int | None:
    """clean に target へ到達できる最小ピーク p（bidir_bfs 版）。"""
    for p in range(1, pmax + 1):
        moves = bidir_bfs(dag, target, p)
        if moves is not None:
            return p
    return None


if __name__ == "__main__":  # 手動確認
    from memo_dags import fib_dag

    for n in range(1, 20):
        g = fib_dag(n)
        p = pmin_bidir(g, n)
        m = bidir_bfs(g, n, p) if p else None
        print(f"fib({n}): p_min={p} M*={m}")
