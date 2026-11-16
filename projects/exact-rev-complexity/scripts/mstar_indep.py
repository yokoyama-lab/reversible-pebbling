"""$M^*(G,p,e)$ の独立第2実装（BFS 系の照合用・candidate: A* / Dijkstra）。

## なぜこれが要るか

`scripts/revpebble.py` の `bfs`（可逆ペブリング, e=0 固定）と `scripts/landauer.py` の
`landauer_profile` / `landauer_bfs`（$e$-Landauer 一般）はどちらも**前向き BFS**であり、
`landauer_profile` と `landauer_bfs` の間の「二重実装」照合はあるが、
状態表現（前者はビットマスクを `mask*width+used` に詰めた単一 int、後者は
`(frozenset, int)` タプル）が違うだけで、探索の原理（幅優先・キュー）は同一である。
規則そのもの（可用性判定・置く/取る/消去の遷移）にバグがあれば両者が共有してしまう。

本モジュールは**原理の異なる第3の実装**として、優先度キューによる最短路探索
（ヒューリスティックが admissible+consistent なら A*、`mode="bits"` では
ヒューリスティックを 0 にするので Dijkstra に退化する）を、ゲームの
docstring（`revpebble.py` 冒頭・`landauer.py` 冒頭）から自分で読み直して書く。
`revpebble.py` / `landauer.py` の movegen 関数（`_available` / `_compile` /
BFS 本体）は一切 import しない。DAG の**構築**（`Dag` データクラス・`chain` 等の
族関数）は対象グラフの定義そのものであり解法ロジックではないので、
呼び出し側スクリプトで流用してよい（本モジュールは preds/free/n を受け取るだけで
`Dag` 型にも依存しない）。

## モデル（自分で読み直した理解）

- 状態 = (ペブル済み頂点の集合, 消費済み不可逆消去コスト)。
- 頂点 v が「可用」⇔ v の全先行点が free であるか、現在ペブルされている。
- 手（1 手 = コスト 1）:
  - **置く**: v が非ペブル・可用・置いた後のペブル数 ≤ p → ペブルを乗せる。
  - **取る（可逆）**: v がペブル済み・可用 → 外す（used は変わらない）。
  - **消去（不可逆・1 ビット）**: v がペブル済み・非可用 → 外せるが used+1 ≤ e が必要。
    `mode` に関わらずこの単一ビット消去は常に許される（`landauer.py` 参照）。
  - **一括消去（`mode="bits"` のみ）**: ペブル済み集合の任意の部分集合 A（|A|≥2）を
    1 手で同時に消す。used += |A| ビット、used+|A| ≤ e が必要。可用性は問わない
    （LTV の m-erasure の一般化として `landauer.py` が定義している通り）。
- target が free なら 0 手で終了（free は常時可用でペブルする必要がない）。
- p < 1 なら到達不能（target が free の場合を除く）。
- 目標: ペブル集合 == {target} になる最短手数。

## ヒューリスティック

- `mode="ops"`: 1 手は必ずちょうど 1 ビットを反転する（置く/取る/消去は全て単一ビット）。
  したがって「現在のペブル集合と目標集合の対称差のビット数」は認容的かつ整合的
  （1 手で高々 1 しか変化しない）。A* の h として使う。
- `mode="bits"`: 一括消去が 1 手で複数ビットを同時に減らせるため、対称差ビット数は
  認容性を失いうる（過大評価になりうる）。安全のため h=0（= Dijkstra）にする。
"""

from __future__ import annotations

import heapq
from typing import Sequence


def mstar_indep(
    preds: Sequence[frozenset[int]],
    free: frozenset[int],
    n: int,
    target: int,
    p: int,
    e: int,
    mode: str = "ops",
) -> int | None:
    """A*（ops）/ Dijkstra（bits）で $M^*(G,\\mathrm{target},p,e)$ を厳密に求める。

    `preds[v]` は v の先行点集合、`free` は常時可用な入力源の集合。
    到達不能なら None。
    """
    if mode not in ("ops", "bits"):
        raise ValueError(f"unknown mode: {mode}")
    if target in free:
        return 0
    if p < 1:
        return None

    free_mask = 0
    for v in free:
        free_mask |= 1 << v
    pred_mask = [0] * n
    for v in range(n):
        m = 0
        for u in preds[v]:
            m |= 1 << u
        pred_mask[v] = m
    movable = [v for v in range(n) if v not in free]
    goal_mask = 1 << target

    def ready(mask: int, v: int) -> bool:
        # v の先行点のうち、free でも現在ペブルでもないものが残っていないか。
        return (pred_mask[v] & ~(mask | free_mask)) == 0

    use_heuristic = mode == "ops"

    def h(mask: int) -> int:
        if not use_heuristic:
            return 0
        return (mask ^ goal_mask).bit_count()

    # 状態キー = (used << n) | mask 。landauer.py の `mask*width+used` とは
    # 詰め方の順序が逆（used が上位ビット）で、意図的に別の符号化にしてある。
    def key(mask: int, used: int) -> int:
        return (used << n) | mask

    start_mask, start_used = 0, 0
    start_key = key(start_mask, start_used)
    best: dict[int, int] = {start_key: 0}
    # heap 要素: (f, g, mask, used) 。g は tie-break に使うので heap の第2要素に入れる。
    heap: list[tuple[int, int, int, int]] = [(h(start_mask), 0, start_mask, start_used)]

    while heap:
        f, g, mask, used = heapq.heappop(heap)
        k = key(mask, used)
        if best.get(k) != g:
            continue  # 古いエントリ（より良い経路が既に見つかっている）
        if mask == goal_mask:
            return g
        npeb = mask.bit_count()
        ng = g + 1

        def relax(nmask: int, nused: int, ng: int = ng) -> None:
            nk = key(nmask, nused)
            if nk not in best or ng < best[nk]:
                best[nk] = ng
                heapq.heappush(heap, (ng + h(nmask), ng, nmask, nused))

        for v in movable:
            bit = 1 << v
            if mask & bit:
                if ready(mask, v):
                    relax(mask ^ bit, used)
                elif used + 1 <= e:
                    relax(mask ^ bit, used + 1)
            else:
                if ready(mask, v) and npeb + 1 <= p:
                    relax(mask | bit, used)

        if mode == "bits" and npeb >= 2:
            sub = mask
            while sub:
                cnt = sub.bit_count()
                if cnt >= 2 and used + cnt <= e:
                    relax(mask ^ sub, used + cnt)
                sub = (sub - 1) & mask

    return None


def mstar_indep_reversible(
    preds: Sequence[frozenset[int]], free: frozenset[int], n: int, target: int, p: int
) -> int | None:
    """e=0 固定版（`revpebble.bfs` の照合専用ショートハンド）。"""
    return mstar_indep(preds, free, n, target, p, e=0, mode="ops")


if __name__ == "__main__":  # 手動確認用（自己完結、他モジュール非依存）
    # chain(4): 0 --free--> 1 -> 2 -> 3 -> 4, target=4
    n = 5
    preds = [frozenset(), frozenset({0}), frozenset({1}), frozenset({2}), frozenset({3})]
    free = frozenset({0})
    print("chain(4) target=4:")
    for p in (2, 3, 4):
        print(f"  p={p} e=0..3:", [mstar_indep(preds, free, n, 4, p, e) for e in range(4)])
    print("  bits mode p=3 e=0..3:",
          [mstar_indep(preds, free, n, 4, 3, e, mode="bits") for e in range(4)])
