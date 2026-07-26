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

from revpebble import Dag  # noqa: E402  (revpebble を読むだけ、編集しない)

# ---------------------------------------------------------------------------
# 2026-07-27 続報3: 状態表現を frozenset から int ビットマスクに変更（OOM 対策）。
# 設計は候補1 の scripts/exp01b_engine.py（読むだけ・編集しない）と同じ発想
# （状態=ビットマスク、遷移は前計算した (bit, need_mask) の組、双方向 BFS）だが、
# **交差点の取り方は独自にしている**: exp01b_engine.mstar_mask は新たに追加した
# 状態を順に調べて最初に見つかった交差点をそのまま返すが、同じラウンド内に
# 複数の交差点があるとき「最初に見つかったもの」が最小和である保証は無い
# （反対側の記録済み距離はラウンドをまたいで様々な値を取りうるため）。
# ここでは §12 で証明した停止規則をそのまま維持し、ラウンドごとに
# 全交差点の最小和 best を取ってから比較する（frozenset 版 bidir_bfs と
# 同じロジック、内部表現だけ int 化。correctness はそのまま、速度とメモリだけ改善）。
# ---------------------------------------------------------------------------


def _compile(dag: Dag) -> tuple[tuple[int, int], ...]:
    """(bit, need_mask) の組に前計算する。need_mask は free でない先行点のみ。"""
    moves: list[tuple[int, int]] = []
    for v in dag.pebbleable():
        need = 0
        for u in dag.preds[v]:
            if u not in dag.free:
                need |= 1 << u
        moves.append((1 << v, need))
    return tuple(moves)


def _expand_mask(state: int, moves: tuple[tuple[int, int], ...], p: int, pc: int) -> list[int]:
    out: list[int] = []
    can_add = pc < p
    for bit, need in moves:
        if state & need != need:
            continue
        if state & bit:
            out.append(state ^ bit)
        elif can_add:
            out.append(state | bit)
    return out


def bidir_bfs(dag: Dag, target: int, p: int) -> int | None:
    """revpebble.bfs と同じ厳密最短手数を双方向 BFS（int ビットマスク）で計算する。

    停止規則（Pohl の双方向探索の標準規則を無重みグラフに特化したもの）:
    両側とも深さ d_f, d_b まで**完全に**展開済みのとき、これ以上展開しても
    見つかる交差点の距離和は d_f + d_b 以上にしかならない。したがって
    既知の最良解 mu が mu <= d_f + d_b を満たした時点で停止してよい。
    交差点はラウンドごとに**全件スキャンして最小の和を取る**（上のコメント参照）。
    """
    if target in dag.free:
        return 0
    if p < 1:
        return None

    moves = _compile(dag)
    start = 0
    goal = 1 << target
    if goal.bit_count() > p:
        return None
    if start == goal:
        return 0

    dist_f: dict[int, int] = {start: 0}
    dist_b: dict[int, int] = {goal: 0}
    frontier_f: list[int] = [start]
    frontier_b: list[int] = [goal]
    d_f = 0
    d_b = 0
    mu: int | None = None

    def expand(
        frontier: list[int],
        dist_this: dict[int, int],
        dist_other: dict[int, int],
        d_new: int,
    ) -> tuple[list[int], int | None]:
        nxt: list[int] = []
        best: int | None = None
        for state in frontier:
            pc = state.bit_count()
            for ns in _expand_mask(state, moves, p, pc):
                if ns in dist_this:
                    continue
                dist_this[ns] = d_new
                if ns in dist_other:
                    cand = d_new + dist_other[ns]
                    if best is None or cand < best:
                        best = cand
                nxt.append(ns)
        return nxt, best

    while frontier_f and frontier_b:
        if mu is not None and d_f + d_b >= mu:
            break
        # 小さい側を伸ばす（exp01b_engine と同じ発想。correctness には影響しない）。
        if len(frontier_f) <= len(frontier_b):
            d_f += 1
            frontier_f, found = expand(frontier_f, dist_f, dist_b, d_f)
        else:
            d_b += 1
            frontier_b, found = expand(frontier_b, dist_b, dist_f, d_b)
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
