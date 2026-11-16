"""可逆ペブリングゲームの厳密 BFS エンジン（DAG 一般）。

モデル（clean reachability reversible pebbling game）
  - 有向非巡回グラフ G=(V,E)。頂点 v の先行点集合 preds(v)。
  - `free` に入っている頂点は常に利用可能でペブル数に数えない（鎖の入力源）。
  - 手（move）: 頂点 v の全先行点がペブル済み（または free）なら、v のペブルを
    「置く」「取る」どちらもできる（toggle 規則 = 可逆性）。1 toggle = 1 手。
  - 初期状態: ペブル無し。終端状態: 目標頂点のみにペブルがある状態（clean）。
  - 制約: 途中の同時ペブル数 ≤ p（ピーク上限）。
  - コスト: 手数。M*(G,target,p) = 最小手数。p_min = 到達可能な最小の p。

このモデルは 2026_exact_reversible_pebbling で確定した実測値
（reach(p)=2^{p-1}、鎖の M* 表）を再現する。tests/ が回帰テスト。
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field


@dataclass(frozen=True)
class Dag:
    """ペブリング対象の DAG。頂点は 0..n-1 の整数。"""

    n: int
    preds: tuple[frozenset[int], ...]
    free: frozenset[int] = field(default=frozenset())
    name: str = "dag"

    def __post_init__(self) -> None:
        assert len(self.preds) == self.n, "preds の長さが頂点数と一致しない"
        for v, ps in enumerate(self.preds):
            for u in ps:
                assert 0 <= u < self.n, f"不正な先行点 {u}"
                assert u < v, "頂点番号はトポロジカル順であること（u < v）"

    def pebbleable(self) -> tuple[int, ...]:
        """ペブルを載せうる頂点（free 以外の全頂点）。"""
        return tuple(v for v in range(self.n) if v not in self.free)


def restrict_to_ancestors(dag: Dag, target: int) -> tuple[Dag, int]:
    """target とその祖先だけを残した DAG と、付け替えた target 番号を返す。

    目標に寄与しない頂点は、クリーンな最適戦略では一度も置かれない
    （置けば終端までに必ず取り除く必要があり、手数もペブルも純損になる）。
    したがって p_min と M* は制限の前後で変わらない。変わるのは頂点数 N であり、
    非祖先を数えたままだと床 2N-1 が過大になって M* を上回りうる。
    """
    keep: set[int] = set()
    stack = [target]
    while stack:
        v = stack.pop()
        if v in keep:
            continue
        keep.add(v)
        stack.extend(dag.preds[v])
    order = sorted(keep)  # 元の番号がトポロジカル順なので、昇順で順序が保たれる
    remap = {v: i for i, v in enumerate(order)}
    preds = tuple(frozenset(remap[u] for u in dag.preds[v]) for v in order)
    free = frozenset(remap[v] for v in order if v in dag.free)
    return (Dag(n=len(order), preds=preds, free=free,
                name=f"{dag.name}|anc({target})"), remap[target])


def chain(n: int) -> Dag:
    """長さ n の鎖。頂点 0 が常時可用な入力源、頂点 n が終端。

    Knill 1995 / Královič 2001 が扱う Bennett のゲームと同じ形。
    """
    preds = [frozenset()] + [frozenset({i - 1}) for i in range(1, n + 1)]
    return Dag(n=n + 1, preds=tuple(preds), free=frozenset({0}), name=f"chain({n})")


def complete_binary_tree(h: int) -> Dag:
    """高さ h の完全二分木（葉→根の方向に依存）。葉は free（入力）。

    h=0 は単一頂点。頂点数 2^{h+1}-1。根が終端。
    Královič は可逆ペブル空間が h+Theta(lg* h) であることを示した（手数は未表化）。
    """
    # レベル h（葉）から レベル 0（根）へ。番号はトポロジカル順に振る。
    levels: list[list[int]] = []
    counter = 0
    for lv in range(h, -1, -1):
        levels.append([])
        for _ in range(2**lv):
            levels[-1].append(counter)
            counter += 1
    preds: list[frozenset[int]] = [frozenset() for _ in range(counter)]
    for depth in range(1, len(levels)):
        children = levels[depth - 1]
        parents = levels[depth]
        for j, v in enumerate(parents):
            preds[v] = frozenset({children[2 * j], children[2 * j + 1]})
    leaves = frozenset(levels[0]) if h > 0 else frozenset()
    return Dag(
        n=counter,
        preds=tuple(preds),
        free=leaves,
        name=f"cbt({h})",
    )


def pyramid(h: int) -> Dag:
    """高さ h のピラミッド DAG（標準ペブリングの定番例）。底辺が free、頂点が終端。"""
    levels: list[list[int]] = []
    counter = 0
    for lv in range(h + 1, 0, -1):
        levels.append([])
        for _ in range(lv):
            levels[-1].append(counter)
            counter += 1
    preds: list[frozenset[int]] = [frozenset() for _ in range(counter)]
    for depth in range(1, len(levels)):
        below = levels[depth - 1]
        cur = levels[depth]
        for j, v in enumerate(cur):
            preds[v] = frozenset({below[j], below[j + 1]})
    return Dag(n=counter, preds=tuple(preds), free=frozenset(levels[0]), name=f"pyr({h})")


def _available(dag: Dag, state: frozenset[int], v: int) -> bool:
    return all((u in dag.free) or (u in state) for u in dag.preds[v])


def bfs(
    dag: Dag,
    target: int,
    p: int,
    *,
    with_parents: bool = False,
) -> tuple[int | None, dict | None]:
    """最小手数 M*(dag, target, p) を BFS で厳密に求める。

    戻り値 (手数, parent 辞書)。到達不能なら (None, None)。
    parent は with_parents=True のときのみ構築（最適スケジュール抽出用）。
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
            if not _available(dag, state, v):
                continue
            if v in state:
                nxt = state - {v}
            else:
                if len(state) + 1 > p:
                    continue
                nxt = state | {v}
            if nxt not in dist:
                dist[nxt] = d + 1
                if with_parents:
                    parent[nxt] = (state, v)
                queue.append(nxt)
    return (None, None)


def pmin(dag: Dag, target: int, pmax: int = 30) -> int | None:
    """clean に target へ到達できる最小ピーク p。"""
    for p in range(1, pmax + 1):
        moves, _ = bfs(dag, target, p)
        if moves is not None:
            return p
    return None


def mstar_chain(n: int, p: int | None = None) -> int | None:
    """鎖 chain(n) の最小手数。p 省略時は p_min で評価。"""
    g = chain(n)
    if p is None:
        p = pmin(g, n)
        if p is None:
            return None
    moves, _ = bfs(g, n, p)
    return moves


def reach(p: int, nmax: int = 64) -> int:
    """ピーク p で clean 到達できる最大の鎖長。予想（既知の系）: 2^{p-1}。"""
    best = 0
    for n in range(1, nmax + 1):
        moves, _ = bfs(chain(n), n, p)
        if moves is None:
            break
        best = n
    return best


def schedule(dag: Dag, target: int, p: int) -> list[tuple[str, int]] | None:
    """最適スケジュールを 1 本抽出する（("put"|"take", 頂点) の列）。"""
    moves, parent = bfs(dag, target, p, with_parents=True)
    if moves is None or parent is None:
        return None
    seq: list[tuple[str, int]] = []
    cur: frozenset[int] = frozenset({target})
    while cur in parent:
        prev, v = parent[cur]
        seq.append(("put" if v in cur else "take", v))
        cur = prev
    seq.reverse()
    return seq


if __name__ == "__main__":  # 手動確認用
    print("reach(p):", [reach(p) for p in range(1, 7)])
    print("M*(chain n) n=1..14:", [mstar_chain(n) for n in range(1, 15)])
    for h in range(0, 5):
        g = complete_binary_tree(h)
        root = g.n - 1
        p = pmin(g, root)
        print(f"cbt(h={h}): p_min={p}, M*={bfs(g, root, p)[0] if p else None}")
